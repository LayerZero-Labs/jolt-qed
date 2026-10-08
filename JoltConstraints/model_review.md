---
title: Jolt model in Lean, open issues
updated: 2026-10-08
rust: $HOME/Work-With-A16z/jolt at 8e536f19 (upstream main 629ed77b not yet audited)
---

# Open issues

The final theorem is `HonestTrace.allConstraints_rust_sizes` (`Completeness/All.lean`):
every constraint holds at the sizes Rust's prover picks, against the public I/O the
verifier checks. Everything it rests on that is not proved is listed here.

`AllConstraints joltInstance privateInputs witness` binds the constraint data to
the instance through `ConstraintContext` (`constraint_context.lean`). Bytecode,
initial RAM, public I/O and the entry slot cannot be chosen independently of
these inputs. Private advice contributes to initial RAM but is not public I/O.
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
| [#1951](https://github.com/a16z/jolt/issues/1951) item 4 | `ram_K` is one slot too small when the highest touched slot is a power of two (`bug-report/ram-k-off-by-one/`) | FIXME: `HonestTrace.prover_config` uses the fixed formula `touched + 1`, so Lean differs from Rust here |
| [#1951](https://github.com/a16z/jolt/issues/1951) item 5 | The emulator loads only some ELF section kinds into RAM, preprocessing loads every section | assumed to agree: `initialRam` TODO in `program.lean` |

## Assumptions

Premises or fields of the final theorem. Each is confirmed by a16z or holds by design.

| Assumption | Where | Why |
|---|---|---|
| The PC does not wrap past 2^64 | `Rv64ProgramImage.NextPCNoWrap` | a16z, 2026-10-07: such an ELF is illegal |
| A program does not change its own code ([#1952](https://github.com/a16z/jolt/issues/1952)) | `HonestTrace.code_unchanged` | a16z, 2026-10-07 |
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
| `lookupEntryCorrect_VirtualSRL`, `SRA`, `SRLW`, `SRAW`, `ROTR`, `ROTRW` | the shift-mask shape of the rows Rust's expansions emit; add it to `ExpansionRowsValid` once `expand` is defined |
| `expand_program_rows_valid` (`trace_interface.lean`) | define `SourceInstruction.expand` from the existing Lean expansions. Facts: a jump writes a real register and ends its instruction, an x0 write is the canonical no-op, a branch is its own native row with a 13-bit offset, earlier rows keep nextPC, register operands are canonical. Also relied on, not yet stated: operand order is Rust's rs1/rs2, `VirtualRev8W` has immediate 0, shift masks are never 0 |
| `pc_map_ok_iff` (`program.lean`) | the shape of `expand_instruction`'s output; not used by the final theorem |

## Gaps in our model

- **Trusted base.** The semantics of each Jolt instruction are translated from Rust by
  hand. Native RV64 instructions are proved against Sail
  (`JoltBytecode/InstructionEquivalence`); virtual instructions have nothing to prove
  against.
- **Not modeled.** The Akita build's 4096-cycle padding floor (`prover_config` uses the
  default build's 256), program commitments (BytecodeChunk, ProgramImageInit), and
  TrustedAdvice/UntrustedAdvice witness columns.
- **To do.** Audit the model against upstream main `629ed77b` (decoder changes #1902
  and #1958, HostIO #1973, `MemoryLayout::try_new` #1978). Fix 75 comments that cite
  `/Users/ari.biswas/...` paths. Drop the unused `ramFits`, `traceFits` and
  `bytecodeDomain` arguments. `constraints.md` still calls (16) a statement.
