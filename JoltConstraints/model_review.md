---
title: Jolt model in Lean, open issues
updated: 2026-10-08
rust: $HOME/Work-with-A16z/jolt at 3cb4e243 with upstream 00508a09 (#1968, includes 8e536f19) merged but not yet committed (upstream main 629ed77b not yet audited)
---

# Open issues

The final theorem is `HonestTrace.allConstraints_rust_sizes` (`Completeness/All.lean`):
it claims the modeled verifier checks and constraints hold at the sizes Rust's prover
picks, against the public I/O the verifier checks. This still depends on the `sorry`s
under "Proofs owed"; it is not a completed completeness proof.
Everything it rests on that is not proved is listed here.

`AllConstraints joltInstance privateInputs witness` binds the constraint data to
the instance through `ConstraintContext` (`constraint_context.lean`). Bytecode,
initial RAM, public I/O and the entry slot cannot be chosen independently of
these inputs. Trusted advice is part of the instance; Jolt's verifier holds a
commitment to it, and we model its contents directly. Untrusted advice is
prover-chosen. Both contribute to initial RAM without being public I/O.
The context also checks the instance's input/output sizes and lowest address,
the padded trace limit, the bytecode domain, and the verifier's RAM bounds.
`ConstraintEquations` is the underlying equation bundle over those data.

## Upstream issues

Jolt issues that stop a completeness proof. If one is still open when the main proofs
pass, escalate it.

| Issue | What breaks | In our model |
|---|---|---|
| [#1949](https://github.com/a16z/jolt/issues/1949) | A load/store address that wraps past 2^64 breaks the RAM-address constraint | (01) stays `sorry`; a fix PR is announced in the issue |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 1 | A run that does not panic and never stores to the termination word: an SDK guest exiting through `platform_exit` or `std::process::exit`, or a bare ELF that reaches `j .` first. The tracer records no write to the word, but `jolt-witness`'s `final_ram_state` sets its `RamValFinal` slot to 1 from the panic flag alone, while initial RAM and the increments give 0 | (38) stays `sorry`. The fix proposed in the issue changes only the SDK's exit paths, so a bare ELF stays unprovable |
| [#1950](https://github.com/a16z/jolt/issues/1950), [#1951](https://github.com/a16z/jolt/issues/1951) item 2 | A store to the termination word is recorded but the device ignores it, so a later load reads 0 (`bug-report/ram-val-termination/`) | (37) stays `sorry`; `HonestTrace.matches_outputs` leaves the termination word out |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 3 | A load from a nonzero address below the lowest address: the tracer runs it, the prover panics | such runs have no `HonestTrace.prover_config` (WARNING) |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 4 | `ram_K` is one slot too small when the highest touched slot is a power of two (`bug-report/ram-k-off-by-one/`). The verifier's maximum is also one word short: `compute_max_ram_k` rounds `total_bytes / 8` down. When `heap_end` is not a multiple of 8 (`program_size` is not rounded), a program may access the word that straddles `heap_end`, and an honest run that does so gets no proof. The issue proposes `touched + 1` together with `div_ceil(8)` | FIXME: `HonestTrace.prover_config` uses the fixed formula `touched + 1`, so Lean differs from Rust here. Blocks the upper half of the verifier's RAM-size check (`ramSizeBounds`, via `HonestTrace.witness_params_ram_bounds`) |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 5 | The emulator loads only some ELF section kinds into RAM, preprocessing loads every section | assumed to agree: `initialRam` TODO in `program.lean` |

## Assumptions

Premises or fields of the final theorem, with their source or reason below.

| Assumption | Where | Why |
|---|---|---|
| The PC does not wrap past 2^64 | `Rv64ProgramImage.NextPCNoWrap` | a16z, 2026-10-07: such an ELF is illegal |
| A program is never empty: its memory image loads at least one byte | `Rv64ProgramImage.ImageNonempty` (premise `imageNonempty`) | a16z, by phone, 2026-10-08. Rust's prover does not reject an empty ELF: it traces it and picks `ram_K = 4`, and only Rust's verifier rejects that size (`InvalidRamK`, minimum 16 with a 64-byte output region; `bug-report/verifier-ram-minimum/`) |
| A program does not change its own code ([#1952](https://github.com/a16z/jolt/issues/1952)) | `JoltInstance.CodeUnchanged`, over every `ValidRun`; honest traces get it from `HonestTrace.code_unchanged`. Completeness does not use it | a16z, 2026-10-07 |
| A run uses no RAM 2 GiB or more above `RAM_START` (`bug-report/final-ram-over-2gib/`) | ASSUMPTION in `finalRamWord` | a16z, 2026-10-07 |
| No spoil assert fails | `HonestTrace.SpoilAssertsPass` | by design: a failing spoil assert is meant to leave no proof |
| Rust's prover accepts the run | `HonestTrace.prover_config = some config` | by design for its own checks (last row a jump, #1968; length limit); also excludes #1951 item 3 |

## Proofs owed

Sorried theorems behind the final theorem; `#print axioms` shows `sorryAx` through them.

| Theorem | What it needs |
|---|---|
| (01) `honestWitness_ramAddrEqRs1PlusImmIfLoadStore` | false until #1949 is fixed |
| (37) `honestWitness_ramValEqInitialPlusPrefixRamInc` | false until #1950 is fixed |
| (38) `honestWitness_ramValFinalEqInitialPlusRamInc` | false until #1951 item 1 is fixed |
| `HonestTrace.witness_params_ram_bounds` (`Completeness/Helpers/VerifierSizes.lean`) | The empty program is excluded by the `ImageNonempty` assumption. Lower half: proved once the minimum computes successfully; still to prove that both bounds compute successfully. Upper half: false until #1951 item 4 is fixed, because the verifier's maximum rounds the word count down |
| `pc_map_ok_iff` (`program.lean`) | the shape of `expand_instruction`'s output; not used by the final theorem |

## Gaps in our model

- **Trusted base.** The semantics of each Jolt instruction are translated from Rust by
  hand. Native RV64 instructions are proved against Sail
  (`JoltBytecode/InstructionEquivalence`); virtual instructions have nothing to prove
  against.
- **Not modeled.** The Akita build's 4096-cycle padding floor (`prover_config` uses the
  default build's 256), program commitments (BytecodeChunk, ProgramImageInit), and
  TrustedAdvice/UntrustedAdvice witness columns and commitment protocols. Trusted
  advice contents are modeled directly as part of the instance.
- **Not modeled.** Rust can trace nonempty trusted-advice bytes without a commitment,
  then fail proving because the verifier expects zeros; Lean has no separate
  commitment-presence flag to express that mismatch.
- **Expansions.** `SourceInstruction.expand` (`expansions.lean`) uses the bytecode
  project's programs. The 53 generated ones match a fresh run of `jolt-lean-gen` on the
  current Rust exactly. LR.W, LR.D, SC.W and SC.D are that generator's output, kept in
  `expansions.lean` until it emits them, and are not proved against Sail. The older
  `JoltISA.lrwProgram`/`lrdProgram` (`Expansions/LoadReserved.lean`) follow the old
  tracer and are unused.
  The rows they emit are checked in `expansion_facts.lean`. Still relied on and not
  stated there: operand order is Rust's rs1/rs2, and `VirtualRev8W` has immediate 0.
- **SC success flag.** Rust patches SC's advice row with a reservation-success flag
  (`cpu.rs:595`); `rustAdvice` does not model it yet, so in an `HonestTrace` an SC
  always fails. This differs from Rust when a reservation covers the address.
- **Soundness execution data.** The relation is proved independent of `advice_tape`
  (`AllConstraints.advice_tape_irrelevant`). Reconstructing a consistent tape and
  per-row runtime advice remains open, including the remaining-length semantics
  of `VirtualAdviceLen`; see B6 in `methods/review_completeness_and_soundness.md`.
- **To do.** Audit the model against upstream main `629ed77b` (decoder changes #1902
  and #1958, HostIO #1973, `MemoryLayout::try_new` #1978). Fix 75 comments that cite
  `/Users/ari.biswas/...` paths. Drop the unused `ramFits`, `traceFits` and
  `bytecodeDomain` arguments. `constraints.md` still calls (16) a statement.
