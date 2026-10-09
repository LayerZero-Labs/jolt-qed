# A prover can make SC.W fail when the reservation holds

**Status:** found and run on 2026-10-09; not reported upstream. Whether it is a bug
depends on a question for a16z (see "Is this a bug?").

## Summary

`SC.W` (store-conditional) stores to memory only if an earlier `LR.W` or `LR.D`
reserved the address. Jolt expands `SC.W` into a sequence of Jolt instructions. The
sequence takes the outcome, success or failure, as advice: a `VirtualAdvice`
instruction whose value the prover supplies. The constraints check only one
direction:

- if the advice says success, the reservation must be at the address;
- if the advice says failure, nothing is checked.

So a prover can report failure even when the reservation holds. The program then
sees `rd = 1` and the store does not happen. Jolt's tracer never does this: it
reports success whenever the reservation holds. We ran Jolt's prover with the
`SC.W` outcome forced to failure, and Jolt's unmodified verifier accepted the proof.

## The check in Jolt

The expansion, `crates/jolt-program/src/expand/memory/scw.rs`:

- line 21: the success flag is a `VirtualAdvice`;
- line 31: `VirtualAssertLTE` checks the flag is 0 or 1;
- lines 40-55: `VirtualAssertEQ` checks `flag * (reservation - rs1) = 0`. The comment
  there says: "If v_success is 1, the reservation address must equal rs1. If
  v_success is 0, this product is zero regardless of the address."
- line 117: `rd = flag XOR 1`. A flag of 0 also makes the sequence store the old
  memory value back, so memory does not change.

The honest tracer, `tracer/src/instruction/scw.rs`:

- line 52: `success = cpu.reservation_covers(address, ReservationWidth::Word)`;
- line 64: it writes `success` into the `VirtualAdvice`.

## Counterexample

Fourteen instructions at `0x80000000` (`make_elf.py`). The program uses one word of
memory, at address A = `0x80000040`, just after its code. The ELF fills that word
with 0.

```asm
auipc x1, 0           # x1 = 0x80000000
addi  x1, x1, 0x40    # x1 = A
lr.w  x2, (x1)        # reserve A
addi  x3, x0, 7
sc.w  x4, x3, (x1)    # store 7 at A if the reservation holds; x4 = 0 if stored
lw    x5, 0(x1)       # x5 = word at A
auipc x6, 0
addi  x6, x6, -0x38   # x6 = 0x7fffffe0, the output address
slli  x4, x4, 8
or    x5, x5, x4      # x5 = x5 | (x4 << 8)
sd    x5, 0(x6)       # output x5
addi  x7, x0, 1
sb    x7, 0x10(x6)    # termination byte = 1, as SDK guests do
jal   x0, 0           # stop: the PC repeats
```

Nothing touches A between the `lr.w` and the `sc.w`, so the reservation holds and
Jolt's tracer stores 7: the output is 7. If the `sc.w` fails, A stays 0 and
`x4 = 1`: the output is `0x100`.

## Result

| Prover | Output bytes | Verifier |
|---|---|---|
| honest | `[7, 0, 0, 0, 0, 0, 0, 0]` | `Ok(())` |
| cheating | `[0, 1, 0, 0, 0, 0, 0, 0]` | `Ok(())` |

The cheating prover is Jolt's prover with one change, `tracer.patch`: when
`JOLT_CHEAT_SC_FAIL` is set, the tracer writes failure into the `SC.W` advice. The
patch changes only `RISCVTrace::trace` for `SC.W`, which only the prover runs. The
bytecode, preprocessing and verifier are Jolt's own. The harness, `sc_flag.rs`,
calls `jolt_sdk::preprocess_program`, `jolt_sdk::prove_program` and
`jolt_verifier::verify`, as the SDK does.

## Is this a bug?

That depends on what a proof promises:

- **The output of Jolt's tracer.** Then this is a soundness bug: the verifier
  accepts the output `0x100`, which Jolt's tracer never produces for this program.
- **An output some RISC-V machine could produce.** The RISC-V A extension lets an SC
  fail even when the reservation is valid. Then the proof is fine, and the comment at
  line 40 suggests the one-way check is intended.

Question for a16z: which of the two does a Jolt proof promise?

Programs that retry until the SC succeeds, as compiled Rust atomics do, compute the
same output either way; a forced failure only costs another round. A program whose
output depends on whether one particular SC succeeded is affected.

`SC.D` (`crates/jolt-program/src/expand/memory/scd.rs`) has the same one-way check.
We did not run it.

## Follow-up questions (not in the issue; ask depending on the answer)

If a proof promises the output of Jolt's tracer:

- Would they add the other direction, so that the outcome must be 1 when the
  reservation is at the address? That needs an "is equal" check on
  `reservation - rs1`, which the sequence does not have today.

If a proof promises any output a correct RISC-V execution could produce:

- Should the docs say that a guest cannot rely on one particular SC succeeding?
- Are there other places where the constraints allow a RISC-V behaviour that Jolt's
  tracer never produces? Each one changes our statement of soundness.

Either way:

- Virtual registers 32 and 33 hold the reservation. Is it intended that only the LR
  and SC sequences write them? Our model of Jolt's tracer relies on this.

## In the Lean model

Our language `JoltInstance.InLanguage` follows Jolt's tracer:
`SourceInstruction.honestTracerAdvice` gives `SC.W` the flag "virtual register 32
holds rs1's address", which is the tracer's reservation check (`model_review.md`,
"SC success flag"). With that language, soundness is false for this program. If
a16z say a forced failure is allowed, the language must allow either flag when the
reservation holds.

## Side finding: a bare ELF that stops without the termination store

Before adding the `sb` to the termination byte, every hand-made ELF failed to prove
honestly, even a single `jal x0, 0`: the prover stopped with
`StageClaimSumcheckFailed { stage: "Stage4", ... }`. This is
[a16z/jolt#1951](https://github.com/a16z/jolt/issues/1951) item 1, already tracked
in `model_review.md`. The earlier reports showed it at the witness level; this
shows the full prover rejects such a run.

## Reproduce

```sh
sh bug-report/sc-forced-failure/run.sh /absolute/path/to/jolt
```

The script copies the Jolt checkout to a temporary directory (without `target/` and
`.git`), applies `tracer.patch` there, adds `sc_flag.rs` as an example of `jolt-sdk`,
builds it in release mode, and runs it on the ELF from `make_elf.py`, first honestly
and then with `JOLT_CHEAT_SC_FAIL=1`. The checkout itself is not modified. It needs
Python 3, rsync and Rust toolchain 1.95; the build takes a few minutes.

## Source state

Local Jolt checkout at `43cc043332762034b5f65379441576e06e7a3890` (2026-10-09). Its
only tracked changes are in `.claude/skills/`, which the build does not use.
