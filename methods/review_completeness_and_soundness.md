---
title: Review of the completeness statement and the soundness infrastructure
date: 2026-10-08
---

# What was reviewed

- **Lean.** Branch `refactor/trace-witness`, with the trace refactor still uncommitted (it builds).
- **Rust.** The checkout at `/Users/ari.biswas/Work-with-A16z/jolt`. HEAD is `3cb4e243`, with upstream `00508a09` (#1968, which includes `8e536f19`) merged but not yet committed. Upstream `629ed77b` is not in the local clone.
- **How.** I read the code myself, and one independent agent reviewed it separately. I re-checked every agent claim marked *verified* below myself, unless it says otherwise.

Every finding is labelled:
- **verified**: checked in the code;
- **suspected**: plausible but not fully checked.

# A. Completeness

## A1. (38) is blocked upstream by #1951 item 1 (known, documented)

**Correction.** An earlier version of this review presented this as a new high-severity finding. It isn't. The theorem is a `sorry`, and `model_review.md` already pointed it at #1951. It is not a translation error: Lean matches Rust here. The problem is on the Jolt side, and it is the same kind of blocker as (01) on #1949 and (37) on #1950. The docs now say "false until #1951 item 1 is fixed".

#1951 item 1 reproduces it in Rust. It covers SDK guests that exit through `platform_exit` or `std::process::exit`, and also a bare ELF `nop; j .` built without the SDK (`F3_no_termination_write`). Every such run fails at Stage 4 on the termination word.

**The bare ELF, step by step.** A bare ELF is a RISC-V program built without the Jolt SDK. Take one whose entry code is the two instructions `nop; j .`.

1. **The tracer executes the program.** It runs `nop`, then `j .`. After `j .`, the PC is the same as before, and the tracer's stop rule ends the run (`tracer/src/lib.rs:327-337`). The trace has two rows. Neither is a store, so the trace records no RAM write. The device's panic flag stays false.
2. **The prover's size check accepts the trace.** `ProverConfig::derive_from_rows` requires only that the last row be a jump (`crates/jolt-prover/src/config.rs:112-117`, #1968). It is, so the check passes.
3. **`jolt-witness` computes the RAM columns from the trace** (`crates/jolt-witness/src/backend/trace/ram.rs`). This is a separate crate from the tracer, and it reads the tracer's output.
   - `initial_ram_state` (lines 81-130) fills the initial RAM from bytecode, advice and inputs. The termination slot is 0.
   - `RamInc` is nonzero only on rows that store. Here it is 0 on both rows.
   - `final_ram_state` (lines 188-194) computes `RamValFinal`. Because the panic flag is false, it sets the termination slot to 1, whether or not any row stored there.
4. **Constraint (38) fails at the termination slot.** (38) requires `RamValFinal = initial + Σ RamInc`, which here is `1 = 0 + 0`. The prover's own Stage 4 check rejects it with `StageClaimSumcheckFailed`, so no proof is produced.

**Where the 1 comes from.** The tracer never records a 1 for the termination word, and it could not: the device ignores stores to that word (#1950). The 1 is written by `jolt-witness` at witness generation, based only on the panic flag. It is there because, for a run that did not panic, the verifier's public I/O has termination = 1 (`PublicIoMemory::new`), and constraint (26) requires `RamValFinal` to equal the public I/O on that slot. So (26) and (38) together require some trace row to have stored 1 to the termination word. The tracer's stop rule requires no such store. The tracer treats the run as finished, but no witness built from it can satisfy both constraints.

**Lean does the same.** `finalRamWord` sets the slot to 1 when there is no panic (`witness_helpers/ram_state.lean:78`), `initialRamWordFromState` gives 0 there, and no row adds an increment. So the honest witness gives `1 = 0` in (38) (`Constraints/RamValFinalEqInitialPlusRamInc.lean:16`). The slot is inside `ramSize`, because the prover's `ram_K` covers the program image, which lies above the I/O region.

The fix proposed in #1951 makes the SDK's exit paths store 1 to the termination word, so it covers SDK guests only. A bare ELF that reaches `j .` without writing the word would still be accepted by the prover and then fail to prove. Whether that needs a further fix depends on whether Jolt promises completeness for any ELF or only for SDK-built guests. That is worth asking a16z on the issue.

**Suspected follow-on.** A store to the panic word sets `panic := true` whatever value it writes (`JoltBytecode/JoltISA/JoltDevice.lean:212`), but the final panic word is always 1. A store of any value other than 1 to the panic word, or to the termination word, may break (38) the same way. Check this alongside #1951 item 2.

## A3. Sorries behind the final theorem

- (01): false until #1949 is fixed.
- (37): false until #1950 is fixed.
- (38): false until #1951 item 1 is fixed (A1).
- The six shift `lookupEntryCorrect_*` lemmas: they need the shift-mask shape of the rows Rust's expansions emit.
- `expand_program_rows_valid`: cannot be proved while `SourceInstruction.expand` is `opaque` (`program.lean:142`). Until then the whole model is parametric in an uninterpreted expansion.
- `pc_map_ok_iff` is not used by the final theorem.

# B. Soundness infrastructure

## B3. The relation is stricter than the verifier on chunk widths (medium, verified by search)

`WitnessParams.proverChunkConfig` (`witness.lean:107`) fixes the chunk widths to the prover's choice: 4/16 below 2^25 cycles, else 8/32. The verifier takes `proof.one_hot_config` (`verifier.rs:344`). The only check I found is the structural one in `JoltFormulaDimensions::try_from` (`crates/jolt-claims/src/protocols/jolt/geometry/dimensions.rs:381-412`). Nothing ties the widths to `log_T`.

A soundness theorem would therefore not cover proofs with other widths that the verifier accepts. Moving `proverChunkConfig` out of `WitnessParams` into a completeness-only fact would fix this.

## B4. The field is unconstrained (medium, verified)

`F` is any `Field`, and nothing in `JoltConstraints` mentions `CharP` or `ringChar`. Completeness is fine over any field. Soundness needs a large characteristic to turn field values back into 64-bit words and 128-bit lookup indices; over GF(2) the equations say almost nothing.

**Akita:** the Akita build uses a 128-bit field (`jolt-akita/src/adapters.rs:38`), while lookup indices are 128 bits. The user confirmed this on 2026-10-08. A premise "characteristic > 2^128" would therefore exclude Akita.

**Decision (2026-10-08).** This is a non-succinct relation, without a PCS, and we keep `F` generic. Field requirements are added only when a soundness lemma needs them, as we specialise:

- Each lemma states the smallest condition it uses, as a bound on `ringChar F` (for example `2^64 < ringChar F` to recover a 64-bit word), not as a fixed field. The final soundness theorem then takes the largest bound its lemmas use.
- We use the most generic condition that works. We pull Jolt's actual field (BN254's scalar field) only if some step needs more than a size bound.
- When the first lemma needs a characteristic above 2^128, record there that Akita is excluded from that point on.

Completeness is unaffected, because it already holds over any field.

## B5. Private inputs (verified)

`initialRam` contains the program image, trusted advice, untrusted advice and public inputs.

Trusted advice is part of the instance (`JoltInstance.trusted_advice`); in Jolt
the verifier holds a commitment to it (`verifier.rs:41`), and we model its contents
directly. This does not claim that the verifier learns those bytes, and no PCS
is needed in this non-succinct relation. `JoltPrivateInputs` contains only untrusted advice and the
execution tape. `initial_state` loads trusted advice from the instance, so the
prover cannot change it while keeping the instance fixed. This is proved by
`JoltInstance.initial_states_agree_on_trusted_advice` (`advice_inputs.lean`).

Not modeled: Rust can trace nonempty trusted-advice bytes without a commitment,
then fail proving because the verifier expects zeros; Lean has no separate
commitment-presence flag to express that mismatch.

`AllConstraints.advice_tape_irrelevant` proves that changing the execution tape
does not affect the relation. Per-row `runtimeAdvice` belongs to the reconstructed
trace, not the relation's inputs. A soundness conclusion must therefore allow
existential choices of these execution data, while keeping the instance's trusted
advice fixed and using the untrusted advice supplied to the relation.

**Still owed:** prove that satisfying witnesses admit consistent execution data.
Tape independence alone does not prove existence of a suitable tape. In
particular, `VirtualAdviceLen` reports remaining bytes, so the lengths and reads
must agree along the run. The local Rust lookup implementation for that
instruction uses `RangeCheck`; the necessary cross-row consistency needs an
audit before promising reconstruction under the tracer's tape semantics. This
is an unresolved soundness obligation, not an established end-to-end Rust bug.

## B6. `HonestTrace` is the wrong conclusion for soundness

Some fields of `HonestTrace` cannot be forced by any constraint:

- `code_unchanged` (`honest_trace.lean:92`) is an a16z assumption. Fetch reads the fixed bytecode, never memory.
- `stops` and `runs_until_stop` (`honest_trace.lean:99-106`) are Rust's repeated-PC stopping rule. A prover can stop at any jump after writing the termination word.
- `prover_config`'s length limit, the `ram_K` formula and the 2 GiB rule belong to the prover.

Other fields should be forceable: `expands`/`accepted` (already in the context), `initialized` except for the tape, `starts`, `linked`, per-row execution, and the outputs and panic flag (now that the verifier's size and instance checks are in the relation). The agent also says (17) and (27) force the last real row to be a JAL/JALR with NoOp padding only at the end; I have not checked that.

**Proposal:** define a separate "valid execution" predicate over `Trace`, sitting between `Trace` and `HonestTrace`, and make it the conclusion of the soundness theorem. It does not exist yet.

# C. Housekeeping (verified)

- The boundary tests never run. `.gitignore:11` ignores `/JoltConstraints/Tests`, and `JoltConstraints.lean` imports only `Completeness.All`. So `RelationBoundary.lean` and `HonestWitnessDependencies.lean` are not committed and not built by `lake build`.
- `model_review.md` cites Rust `8e536f19`. The local checkout is `3cb4e243` with an uncommitted merge of `00508a09`. Update the header once the merge is committed.
- `methods/constraint_proving.md:85-106` still refers to `JoltTraceRow`, `JoltTrace`, `compactImmediateFits` and `JoltTrace.Terminated`, none of which exist after the refactor.
- `ramAccessesValid (trace : Trace)` is only used by completeness, but it lives in the relation layer (`Constraints/RamReadData.lean`).

# Decisions for you

1. A1: ask a16z on #1951 whether completeness is promised for bare ELFs, or only for SDK guests?
2. B3: move `proverChunkConfig` out of `WitnessParams`?
3. B4: which characteristic premise, given Akita?
4. B5: trusted advice is part of the instance, modeled directly; reconstructing consistent tape/runtime advice remains open.
5. B6: the shape of the "valid execution" predicate that soundness concludes.
