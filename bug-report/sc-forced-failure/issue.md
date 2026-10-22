# SC.W: Soundness issue

## 1. The program

We run this RISC-V program. `make_elf.py` in the attached zip builds the ELF. The
program starts at `0x80000000`. It uses one word of memory, at address
A = `0x80000040`, just after its code. The ELF fills that word with 0.

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

The program reserves A with `lr.w`, then stores 7 at A with `sc.w`. Nothing runs
between the two, so the reservation holds, and Jolt's tracer makes the `sc.w`
succeed: it stores 7 at A and sets `x4 = 0`. The program then outputs
`(word at A) | (x4 << 8)`, which is 7: the bytes `[7, 0, 0, 0, 0, 0, 0, 0]`.

It runs with no inputs or advice, `max_output_size = 8`, and a 4096-byte stack and
heap.

## 2. Where we deviate from Jolt's tracer

Jolt expands `sc.w` into a sequence of Jolt instructions. One of them is a
`VirtualAdvice` that holds the outcome: 1 for success, 0 for failure. Jolt's tracer
writes 1 there, because the reservation holds
([`SCW::trace`, L52-L64](https://github.com/a16z/jolt/blob/00508a09fd3850e1f45a5515260a3e133a180940/tracer/src/instruction/scw.rs#L52-L64)).

We write 0 instead. Every other step is exactly what Jolt's tracer does. With 0,
the rest of the `sc.w` sequence stores nothing and sets `x4 = 1`, so the program
outputs `0x100`: the bytes `[0, 1, 0, 0, 0, 0, 0, 0]`.

## 3. How to do this in Jolt

We change one line of Jolt's tracer, so that it writes 0 at the `sc.w` step. The
prover, preprocessing and verifier are Jolt's own, unchanged.

The change, in `tracer/src/instruction/scw.rs` (`tracer.patch` in the zip):

```diff
-        let success = cpu.reservation_covers(address, ReservationWidth::Word);
+        let success = cpu.reservation_covers(address, ReservationWidth::Word)
+            && std::env::var_os("JOLT_CHEAT_SC_FAIL").is_none();
```

Jolt's prover takes the trace from this tracer and produces a proof. Jolt's verifier
then checks the proof against the outputs the prover reports. `sc_flag.rs` in the zip
does this with the SDK's own calls: `jolt_sdk::preprocess_program`,
`jolt_sdk::prove_program` and `jolt_verifier::verify`.

`run.sh` does all of this on a copy of your checkout, which it leaves unchanged:

```sh
unzip sc-forced-failure-repro.zip -d sc-forced-failure-repro
sh sc-forced-failure-repro/run.sh /absolute/path/to/jolt
```

It needs Python 3, rsync and Rust 1.95.

## 4. The verifier still accepts

| Tracer | Output bytes | `jolt_verifier::verify` |
|---|---|---|
| Jolt's tracer | `[7, 0, 0, 0, 0, 0, 0, 0]` | `Ok(())` |
| Ours: writes 0 at the `sc.w` step | `[0, 1, 0, 0, 0, 0, 0, 0]` | `Ok(())` |

Tested at `00508a09` (#1968).

## Why the verifier cannot tell

The `sc.w` sequence checks the outcome in one direction only
([`expand_scw`, L39-L60](https://github.com/a16z/jolt/blob/00508a09fd3850e1f45a5515260a3e133a180940/crates/jolt-program/src/expand/memory/scw.rs#L39-L60)):

- if the outcome is 1, the reservation must be at the address;
- if the outcome is 0, nothing is checked.

The comment there says so: "If v_success is 0, this product is zero regardless of
the address." `sc.d` has the same check
([`expand_scd`, L39-L60](https://github.com/a16z/jolt/blob/00508a09fd3850e1f45a5515260a3e133a180940/crates/jolt-program/src/expand/memory/scd.rs#L39-L60)).
We ran only `sc.w`.

## Question

Which claim does a Jolt proof prove? The verifier checks a proof against a program
P, its inputs and advice I, and an output O. Accepting the proof should mean that a
claim about P, I and O is true. We see two possible claims, and which one Jolt
intends decides whether this is a bug.

1. **"Jolt's tracer, running P on I, outputs O."**

   Then this is a soundness bug. The verifier accepts a proof for the program above
   with O = `[0, 1, 0, 0, 0, 0, 0, 0]`, but Jolt's tracer, running that program,
   outputs `[7, 0, 0, 0, 0, 0, 0, 0]`. The claim is false.

2. **"Some execution of P on I that the RISC-V spec allows outputs O."**

   Then this is not a bug. The spec allows any SC to fail (see the note below), so it
   allows an execution of the program above in which the `sc.w` fails, and that
   execution outputs `[0, 1, 0, 0, 0, 0, 0, 0]`. The claim is true, the verifier is
   right to accept, and the one-way check in `expand_scw` matches the spec.

Which of the two claims does a Jolt proof prove?

> [!NOTE]
> **Why RISC-V allows an SC to fail.** LR/SC exists to build atomic updates, and the
> RISC-V spec promises one direction only: if an SC succeeds, no other store reached
> the reserved address since the LR, so the update was atomic. An SC may fail at any
> time, because real hardware loses reservations for reasons the program cannot see,
> such as an interrupt or a cache eviction. When it fails, nothing is written and the
> program retries. The spec adds a progress promise: a short retry loop eventually
> succeeds ("Eventual Success of Store-Conditional Instructions" in the A extension).
> So correct RISC-V code always retries, and a program that retries, as compiled Rust
> atomics do, produces the same output under either reading. Only a program that
> relies on one particular SC succeeding, like the one above, can tell the two apart.

Note: the program stores 1 to the termination byte before it stops. Without that
store, even the honest proof fails (#1951 item 1).
