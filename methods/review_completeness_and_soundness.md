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
- `witness_params_ram_bounds`: the upper half is false until #1951 item 4 is fixed, because the verifier's maximum RAM size rounds down. The lower half is proved. Still to prove: both bounds compute. An empty program is excluded by the a16z assumption `ImageNonempty`.
- Closed: `expand_program_rows_valid` and the six shift `lookupEntryCorrect_*` lemmas, proved from `SourceInstruction.expand` (`expansion_facts.lean`).

# B. Soundness infrastructure

Closed: B1/B2 (verifier checks in the relation), B3 (chunk widths: only Rust's
structural checks are in `WitnessParams`; the prover's choice is the
completeness-only `ProverChunkConfig`), B4 (field: keep `F` generic, add
`ringChar` bounds lemma by lemma; Akita's prime is about 2^128 − 2^32), B5
(trusted advice is part of the instance; the relation ignores the tape).

## B6. The soundness statement

**The language, agreed.** Jolt's own claim: `x ∈ L` iff for some prover inputs
(untrusted advice and tape), Rust's run of the program reaches the PC stall and
its final device has `x`'s outputs (trailing zeros dropped) and panic flag. In Lean
this is "there exist `a` and `trace : HonestTrace x a` with `trace.matches_outputs`".
Sources: `jolt-sdk/src/host_utils.rs:318` (the claim is the tracer's final device),
`book/src/usage/guests_hosts/guests.md:144, 223` (outputs and panic flag are what
the proof attests; PC-stall exit).

**Premises, decided 2026-10-08.** `2^127 < ringChar F` (Akita's prime, about
2^128 − 2^32, and BN254's satisfy it), and the conditions on the program
`NextPCNoWrap` and `CodeUnchanged` (both a16z).

**In place.** `ValidRun` (a run with no stop rule or advice choice); `HonestTrace`
extends it with Rust's stop rule and Rust's runtime advice (`advice_from_rust`, the
division family; SC.W/SC.D to come). Self-modifying code is excluded by the
instance assumption `JoltInstance.CodeUnchanged` (a16z).

**Known not sound for this `L`** (from reading the code, not run):
1. The trace may end at any jump, not only at the PC stall. A program that stores
   1 to termination and then writes more output can be proved with its earlier output.
2. Any store to the panic address sets the device's panic flag, but the verifier
   reads the stored value. A store of 0 there can be proved as "no panic".

Both need exit behaviour SDK guests never have. To report to a16z, with `L`
justified from their book.

**Still owed:** show that a satisfying witness gives consistent execution data:
- runtime advice equal to Rust's (the bytecode project proves this direction for
  DIV, DIVU, DIVW; check the other five);
- an advice tape consistent with the reads. `VirtualAdviceLen` reports the
  remaining bytes, so lengths and reads must agree along the run; its cross-row
  consistency needs an audit.

# C. Housekeeping

Done: `ramAccessesValid` moved to `Completeness/Helpers/RamAccesses.lean`;
`constraint_proving.md` names the current trace facts; `model_review.md`'s header
states the Rust checkout as it is. Build-time check scripts are not kept in the
code (the `Checks/` folder was removed).

Still open: the Rust checkout's merge of `00508a09` is uncommitted, so update
`model_review.md`'s header once it is committed.

# Decisions for you

1. A1: ask a16z on #1951 whether completeness is promised for bare ELFs, or only for SDK guests?
