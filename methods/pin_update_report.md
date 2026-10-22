# Audit of Jolt pin `8bbb2357` → `5def437f`

The audit used the immutable Jolt commits `8bbb2357890928d8f83b00ca542879077c4d3d28` and `5def437f21a0006e13c063a03f0b5a7c9b93cd6f` in `/Users/ari.biswas/Work-with-A16z/jolt`.
The latter is `origin/main` in that checkout, and its reflog records the fetch on 2026-10-22.
The local checked-out branch and its uncommitted generator changes were not used as semantic evidence.
The range has 36 commits and 226 changed paths; 35 changed paths fall under the nine prefixes requested by `pin_update_plan.md`.
`common/` and `crates/jolt-witness/` have no changed paths.
The table below has one row for each of the 35 paths, including the two Git renames under their new names.
“Mirror” means that Lean represents the changed behavior, not necessarily that the named file is quoted verbatim.
All Jolt line references in this report refer to `5def437f` unless explicitly marked otherwise.

## Corrections and limits to the plan

The plan's source claims about `bc4bfb1f`, the merge of PR #2109, and `521e53f6` check out, with two qualifications that matter for migration.

* The statement that `InLanguage` “uses” `validate_inputs` is true only for the **instance-only** Lean predicate `JoltInstance.validate_inputs` at `JoltConstraints/program.lean:371`, inherited through `HonestTrace.valid_inputs` at `JoltConstraints/honest_trace.lean:222`.
  The newly changed Jolt check is on the **proof's trace length**, in `jolt/crates/jolt-verifier/src/verifier.rs:976-991`, called from `validate_inputs` and `validate_inputs_from_parts` at lines 379 and 1055.
  Lean's corresponding witness check is in `ConstraintContext.traceLengthBound` at `JoltConstraints/constraint_context.lean:28`, which currently has only the maximum.
  Changing the instance-only Lean predicate, or changing `InLanguage` directly, would put a proof-dependent condition in the wrong place.
* The plan says that only tests and one doc comment changed between PR #2109's initial head `d2995380` and final head `32eb430e`.
  GitHub's read-only comparison also shows a test-harness visibility change to `jolt-tracer-x86/src/native/harness.rs` (`terminal_row` became `pub` so the new integration test can call it).
  This has no production semantic effect, but “only tests and one doc comment” is not literally exhaustive.

No false staged proof statement was found in the pin plan itself.
That is an audit of the plan's claims, not an approval of helper A or of the overall soundness theorem.
The already acknowledged helper C remains false in one case after the upstream verifier fix, as explained below.

`bc4bfb1f` makes the program decoder reject nonzero encoded `rd` and emit `NormalizedOperands::default()` for HostIO (`jolt/crates/jolt-program/src/image/decode.rs:192-209,253-339`).
Jolt's interpreter decoder also rejects nonzero encoded `rd` (`jolt/tracer/src/instruction/mod.rs:1352-1363`), and `FormatNoOperands` plus `RegisterStateNoOperands` capture no operands (`jolt/tracer/src/instruction/format/format_no_operands.rs:6-29`, `jolt/tracer/src/instruction/registers/no_operands.rs:13-32`).
The encoded `rs1` and immediate fields are *ignored*, not rejected, by those decoders.
Jolt's HostIO executor still reads x10–x13 implicitly for call ID and arguments (`jolt/tracer/src/instruction/virtual_host_io.rs:19-38`); these are not normalized bytecode operands.
The absence of `rd` prevents the former `rd = x0` side-effect rewrite in `jolt/crates/jolt-program/src/expand/materialize.rs:79-89`.
Jolt's witness register backend updates a register only when `row.rd_index()` is present (`jolt/crates/jolt-witness/src/backend/trace/registers.rs:26-57`), so the new row selects no register write.
The old HostIO executor already did not mutate CPU registers; the change repairs bytecode and witness metadata rather than the host-call effect.

PR #2109 is merged as `0249591a293aa40dc4ebba92818e1367c66ea633`, with final head `32eb430efb0b887b3bce590262a33e57913b2e44`.
`Cpu::tick` now records a stall only when the PC stayed put **and** the executed row would jump to the same PC again (`jolt/tracer/src/emulator/cpu.rs:553-576`, `jolt/crates/jolt-riscv/src/row.rs:102-130`).
The tracer loops and parallel pass-one use that flag (`jolt/tracer/src/lib.rs:106-123,198-205,318-326`, `jolt/tracer/src/parallel.rs:251-273`).
Lean already encodes that fixed-point rule in `JoltInstructionRow.selfJumpRepeats` (`JoltConstraints/program.lean:134`), `TraceRow.StableStall` (`JoltConstraints/honest_trace.lean:39`), and `HonestTrace.stops/runs_until_stop` (`JoltConstraints/honest_trace.lean:230-241`).
The final PR removed an incorrect doc assertion that the last-row next-PC constraint forces a self-targeting JALR to run again; the boundary waives that check.
The present Lean stopping statement does not rely on that assertion.

`521e53f6` moved the prover's minimum padded length constant into the verifier crate and made the verifier reject a shorter proof length: 256 in the base build, 4096 with Akita (`jolt/crates/jolt-verifier/src/config.rs:109-120`, `jolt/crates/jolt-verifier/src/verifier.rs:976-991`).
Jolt's prover padding formula did not change (`jolt/crates/jolt-prover/src/config.rs:53-70`), and Lean's base `ProverConfig.checkedTraceLength` already uses 256 (`JoltConstraints/prover_config.lean:43-47`).
Lean currently accepts witness domains below 256 through `ConstraintContext.traceLengthBound`; `WitnessParams.ProverPaddedFor` has the floor but is a completeness fact, not a soundness input check (`JoltConstraints/witness_params.lean:118-135`).
Once the public verifier floor is modeled in the constraint context, helper C's “maximum below 256” counterexample disappears because such a witness is no longer verifier accepted.
Its other counterexample remains: if a legal witness has `T` actual rows, `T` is the largest power of two allowed by the instance, and all `T` rows are used, Jolt's prover rounds `T + 1` to `2T` and rejects it although Jolt's verifier can accept length `T`.
For example, the new floor still permits `T = maximum = 256`, while the prover needs 512.
`JoltInstance.soundness_prover_accepts` at `JoltConstraints/Soundness/TopLevel.lean:162` therefore remains known false, and this pin does not authorize discharging its `sorry`.

## Changed-file inventory

The “Lean / action” column gives the concrete mirror or says why there is none.
Rows marked “citation” need only source references refreshed.
The listed commits are the commits in this range that touched each file.

| Jolt path | Commit(s) | Lean / action |
|---|---|---|
| `crates/jolt-claims/Cargo.toml` | `3c07920e` | None: Rayon dependency for bytecode folding; no modeled equation changes. |
| `crates/jolt-claims/fuzz/Cargo.lock` | `189baa3e`, `3c07920e` | None: fuzz dependency resolutions, outside the witness relation. |
| `crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs` | `3c07920e` | No equation change: new `read_raf_fold_stage_values` accumulates the existing `read_raf_row_values` under the same address weights (`jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs:463-521,594-641`). Existing row formulas mirrored by `JoltConstraints/Constraints/BytecodeReadSelectors.lean:12-145`, `JoltConstraints/Constraints/BytecodeReadData.lean:22-46`, and `JoltConstraints/witness.lean:94` remain. Citation updates only. |
| `crates/jolt-claims/tests/bytecode_fold.rs` | `3c07920e` | None: tests serial/parallel fold equality and mismatched input lengths; no model source. |
| `crates/jolt-program/src/image/decode.rs` | `bc4bfb1f` | **Mirror:** HostIO now has no normalized operands and rejects nonzero encoded `rd` (`jolt/crates/jolt-program/src/image/decode.rs:204-209,332-339`). Change `JoltCustomInstruction.VirtualHostIO` (`JoltConstraints/expansion_helpers.lean:24`) and `SourceInstruction.expand` (`JoltConstraints/expansions.lean:126`) to the accepted, operandless row; see affected declarations below. |
| `crates/jolt-program/src/image/decode/tests.rs` | `bc4bfb1f` | None: regression checks that a HostIO decode has default operands (`jolt/crates/jolt-program/src/image/decode/tests.rs:344-354`). |
| `crates/jolt-program/src/preprocess/public_io.rs` | `521e53f6` | Citation: explanatory comment for the existing termination word; the `if !public_io.panic` branch is unchanged (`jolt/crates/jolt-program/src/preprocess/public_io.rs:44-57`). `JoltConstraints/program.lean:389` and `Soundness/Layer7/TerminationStore.lean:302` keep their formulas. |
| `crates/jolt-riscv/src/row.rs` | `0249591a` | Already mirrored: new `self_jump_repeats` (`jolt/crates/jolt-riscv/src/row.rs:102-130`) matches `JoltInstructionRow.selfJumpRepeats` (`JoltConstraints/program.lean:134`) and stopping proofs under `Soundness/Layer7/StallSuffix.lean` and `Stopping.lean`. Update PR citations. |
| `crates/jolt-verifier/fuzz/Cargo.lock` | `5aa807b0`, `189baa3e`, `3c07920e` | None: fuzz dependencies (including transcript/field packages); PCS and fuzz harness are outside the present relation. |
| `crates/jolt-verifier/src/config.rs` | `521e53f6` | **Mirror:** new base/Akita floor constants (`jolt/crates/jolt-verifier/src/config.rs:109-120`); base floor belongs in `ConstraintContext`/`AllConstraints`, not the instance-only `validate_inputs`. Akita remains a separate model. |
| `crates/jolt-verifier/src/error.rs` | `521e53f6` | None: `InvalidTraceLength` diagnostic now includes `min`; Lean erases error variants to Boolean/`Option`. |
| `crates/jolt-verifier/src/stages/relations.rs` | `0d031dd0` | None: test recorder's type parameter changes; no RV64 relation coefficient or constraint is changed. |
| `crates/jolt-verifier/src/stages/stage6b/bytecode_read_raf.rs` | `3c07920e` | None: calls the new fold with the same gammas and address equality weights (`jolt/crates/jolt-verifier/src/stages/stage6b/bytecode_read_raf.rs:206-238`); no change to Lean's bytecode selector equation. |
| `crates/jolt-verifier/src/verifier.rs` | `521e53f6` | **Mirror:** both validation paths call `validate_trace_length` and now require `T ≥ 256` in the base build (`jolt/crates/jolt-verifier/src/verifier.rs:375-380,976-991,1052-1059`). Strengthen the witness-domain check represented by `ConstraintContext.traceLengthBound` (`JoltConstraints/constraint_context.lean:28`), subject to Ari's decision. |
| `crates/jolt-verifier/tests/fs_inventory/absorb-sites.inventory` | `5aa807b0`, `8ccb4652`, `0d031dd0` | None: transcript inventory for Akita setup and recorder names, outside this model. |
| `crates/jolt-verifier/tests/fs_inventory/challenge-sites.inventory` | `0d031dd0` | None: recorder generic-name inventory only. |
| `crates/jolt-verifier/tests/support/akita_fixtures.rs` | `8ccb4652` | None: Akita fixture catalog profile, outside the base theorem. |
| `jolt-platform/src/exit.rs` | `0249591a` | Citation: comment drops the old `prev_pc` description; exit loop is unchanged (`jolt/jolt-platform/src/exit.rs:1-15`). The modeled termination store and stop proofs retain their behavior. |
| `jolt-sdk/macros/src/lib.rs` | `2af541b0`, `0249591a` | None to Boolean acceptance: generated verifier closure returns `Result<(), VerifierError>` instead of `.is_ok()`, and WASM propagates the same errors (`jolt/jolt-sdk/macros/src/lib.rs:252-288,1138-1164`). Its stall comment also changes; termination-store code is unchanged. Update prose/API citations. |
| `jolt-sdk/src/runtime/exit.rs` | `0249591a` | Citation: stall comment only; no change to exit instruction (`jolt/jolt-sdk/src/runtime/exit.rs:14-31`). |
| `tracer/examples/trace_bench.rs` | `32157294` | None: benchmark reads worker count before timing; no tracer semantics. |
| `tracer/examples/trace_lockstep.rs` | `0249591a` | None: example uses `has_stalled` instead of local `prev_pc`; production tracer changes are inventoried below. |
| `tracer/fuzz/Cargo.lock` | `189baa3e`, `bbd756f9` | None: fuzz dependency resolutions only. |
| `tracer/src/emulator/cpu.rs` | `0249591a` | Already mirrored: `stalled` is set after `tick` from equal PC plus `self_jump_repeats` (`jolt/tracer/src/emulator/cpu.rs:553-576`); `StableStall`, `ValidRun`, `HonestTrace` and Layer 7 stopping proofs encode this rule. Update PR citations. |
| `tracer/src/emulator/mod.rs` | `0249591a` | Already mirrored: run loop tests `has_stalled` (`jolt/tracer/src/emulator/mod.rs:106-126`) after a tick. Refresh `HonestTrace` and `program.lean` citations. |
| `tracer/src/instruction/ebreak.rs` | `0249591a` | Citation: only the comment changes; `EBREAK::exec` still sets PC to its own address (`jolt/tracer/src/instruction/ebreak.rs:22-30`). |
| `tracer/src/instruction/fence.rs` | `bc4bfb1f` | None for FENCE behavior: switches to shared no-operand format/register capture; `JoltISA.Instr.FENCE` and `Soundness/Layer5/Fence.lean:9` already have no operands/write. |
| `tracer/src/instruction/format/format_no_operands.rs` (rename from `format_fence.rs`) | `bc4bfb1f` | **Mirror via HostIO:** reused no-operand parser and default normalized row (`jolt/tracer/src/instruction/format/format_no_operands.rs:6-29`). Change HostIO representation and metadata; FENCE stays equivalent. |
| `tracer/src/instruction/format/mod.rs` | `bc4bfb1f` | None: exports renamed shared format module. |
| `tracer/src/instruction/mod.rs` | `bc4bfb1f` | **Mirror:** interpreter rejects nonzero HostIO encoded `rd` (`jolt/tracer/src/instruction/mod.rs:1352-1363`); `JoltCustomInstruction` and its expansion/decode model need the accepted instruction shape. |
| `tracer/src/instruction/registers/mod.rs` | `bc4bfb1f` | None: exports renamed shared register-state module. |
| `tracer/src/instruction/registers/no_operands.rs` (rename from `fence.rs`) | `bc4bfb1f` | **Mirror via HostIO:** empty pre/post register captures (`jolt/tracer/src/instruction/registers/no_operands.rs:13-32`); update `TraceWitness.rdValue`, `RdWa`, register selectors, and HostIO frame proofs. |
| `tracer/src/instruction/virtual_host_io.rs` | `bc4bfb1f` | **Mirror:** switches to no-operand format/capture, while `exec` still implicitly reads x10–x13 and has the same host effects (`jolt/tracer/src/instruction/virtual_host_io.rs:1-38`). Change Lean's HostIO instruction and witness metadata, preserving those implicit reads in `execHostIOWith`. |
| `tracer/src/lib.rs` | `0249591a` | Already mirrored: eager, lazy and execute-only paths use CPU's stall flag (`jolt/tracer/src/lib.rs:106-123,198-205,318-326`). Update `trace_interface.lean`, `honest_trace.lean`, and stopping-proof citations. |
| `tracer/src/parallel.rs` | `0249591a` | Already mirrored: pass one owns termination and workers replay counted ticks (`jolt/tracer/src/parallel.rs:234-274`). Citation update in `methods/soundness.md`. |

## Changed files found through existing citations outside those prefixes

An exact-path search over all Lean files and `methods/` plus `JoltConstraints/*.md` found the following additional changed paths.
The search includes source links and plain path references and excludes `pin_update_plan.md` itself.
It found no other changed file outside the requested prefixes that a Lean or selected Markdown source cites by path.

| Jolt path | Commit(s) | Lean / action |
|---|---|---|
| `Cargo.lock` | `5def437f`, `b3b4db7c`, `79dc904f`, `67afddcf`, `528777f5`, `5aa807b0`, `8ccb4652`, `189baa3e`, `fb2ec6f0`, `3c07920e`, `43c5325b`, `f45d64e0`, `bbd756f9`, `6f4eca00`, `adb20845`, `cfd1f86f` | Cited by `methods/model_update.md:599,832`. No direct Lean semantics change. The cited `dory-pcs` remains version 0.4.2 at both pins; dependency revisions elsewhere changed and are not a new proof of PCS behavior. |
| `book/src/usage/guests_hosts/guests.md` | `2af541b0`, `d9bc72b4` | Citation/prose: trusted-advice commitment provenance is clarified and the verifier example now handles `Result`; `JoltConstraints/language.lean:15` cites this document. No change to the abstract trusted-advice contents model. |
| `book/src/usage/runtime_advice.md` | `2af541b0` | Citation/prose: example now handles verifier `Result`, not a Boolean; `methods/soundness.md:273` and `JoltConstraints/model_review.md:380` cite this document. |
| `crates/jolt-prover/src/config.rs` | `521e53f6`, `8ccb4652` | Base prover policy is unchanged; the floor constant is imported from the verifier crate (`jolt/crates/jolt-prover/src/config.rs:14-18,53-70`). The other change is an Akita chunk-profile default, outside this theorem. `JoltConstraints/prover_config.lean:43-76`, `honest_trace.lean:270-299`, `witness_params.lean:114-135`, and their proof citations need review for moved line numbers only. |

The broader commit range also changes `Cargo.toml`, Akita, field, transcript, prover internals, and benchmark or workflow files.
They are not additional path citations in the selected Lean and Markdown sources.
The cited constraint coefficients and RV64 R1CS file are unchanged (`jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`), and the selected Dory PCS dependency version is unchanged.
This report does not infer cryptographic equivalence of changed dependencies from the absence of Lean path citations.

## Proposed changes for Ari's decision

**L and restrictions.**
Do not add the trace-length floor to `JoltInstance.validate_inputs` or edit `JoltInstance.InLanguage`'s formula merely because Jolt's function has the same name.
The relevant strengthening is the verifier-accepted witness domain in `ConstraintContext` (`JoltConstraints/constraint_context.lean:17-32`) and thus `AllConstraints` (`JoltConstraints/Constraints/All.lean:155`), with the base lower bound `256 ≤ params.traceLength`.
`JoltInstance.soundness_prover_accepts` (`Soundness/TopLevel.lean:162`) can then use that lower bound to exclude its first counterexample; `HonestTrace.allConstraints_corrected_sizes` (`Completeness/All.lean:179`) must supply it from the existing prover padding proof.
Because `ConstraintContext` is a core verifier-input definition and this changes the soundness theorem's antecedent, Ari should review the exact staged field and both callers before it is changed.
The Akita floor is 4096 but Akita is not part of this base theorem; a later profile-aware model would select the floor.
The full-witness counterexample still blocks proving helper C without a separate decision about the instance maximum or L.

Remove or revise `Rv64ProgramImage.HostCallRdZero` (`Soundness/Assumptions.lean:53`) and the `hostCallRdZero` field of `JoltInstance.TemporaryRestrictions` (`Soundness/Assumptions.lean:89`) only when Ari approves the new instruction representation and the revised theorem caller.
The accepted source HostIO row no longer has a destination to restrict.
`HostCallsSucceed` (`Soundness/Layer5/HostCallRestriction.lean:33`) is a different, still-open condition on whether an attempted call succeeds, and this commit does not discharge it.
The removal of the existing restriction changes an Ari-approved bundle, so this report proposes it without making the edit.

**Instruction, semantics, metadata, witness, constraints, and proofs.**
Replace the three-operand `JoltCustomInstruction.VirtualHostIO` (`JoltConstraints/expansion_helpers.lean:24`) and `JoltISA.Instr.VirtualHostIO` (`JoltBytecode/JoltISA/Instruction.lean:150`) by the source and bytecode shapes supported by the new decoders.
`SourceInstruction.expand` (`JoltConstraints/expansions.lean:126`) should emit a HostIO row with `rd = rs1 = rs2 = None` and immediate zero.
The typed `SourceInstruction` has no encoded word to check, so the rejection of nonzero encoded `rd` belongs at a decoder boundary; the source instruction constructor should represent only successfully decoded HostIO instructions.
The exact source representation needs Ari's review because source words with nonzero encoded `rs1` or immediate remain legal but are ignored.
The direct HostIO case of `Instr.rewriteNative` (`JoltBytecode/JoltISA/Instruction.lean:448-457`) must cease rewriting a phantom destination; the generic `sideEffectingDst` remains needed by other instructions.
`Instr.destination?` (`Instruction.lean:413`), `JoltMetadata.immediate` (`metadata.lean:13`), `instructionIsCanonical` (`register_encoding.lean:43`), `bytecodeRs1Register`/`bytecodeRdRegister` (`Constraints/BytecodeReadSelectors.lean:12,79`), `Rs1Ra`/`RdWa` and `rdValue` (`witness_helpers/rs1_ra.lean:16`, `rd_wa.lean:15`, `rd_value.lean:13`), and the corresponding register-value helpers must give HostIO absent operands and zero captured values.
Do not turn the implicit x10–x13 host arguments into normalized `rs1`/`rs2` selectors; `execHostIOWith` (`JoltBytecode/JoltISA/HostIO.lean:41`) still reads those registers through CPU state.

All pattern matches on the old three-argument constructor require mechanical revision, including `Semantics.execInstr` (`JoltBytecode/JoltISA/Semantics.lean:38`), `expansion_facts.lean:790,810`, `trace_interface.lean:155-166`, `expansion_temp_liveness.lean:18`, `nextpc_frame.lean:202,330-347`, the completeness register/HostIO proof helpers, and `Soundness/Layer7/TapeRebuild.lean:680,782` and `StallSuffix.lean:701`.
The proof-specific change is larger in `Soundness/Layer5/HostCallExpansion.lean:15-155` and `HostCallRegisterFrame.lean:30-340`: their temporary-40 destination arguments and `RegisterAgreementExceptHostTemp` describe the old synthetic write.
Those statements and the execution-prefix caller (`Soundness/Layer6/ExecutionPrefix.lean`) must be restaged top-down, with no false temporary-register fact carried forward.
The bytecode selector proofs in `Constraints/BytecodeReadSelectors.lean` and the completeness helpers `Completeness/Helpers/RegistersReadProofHelpers.lean`, `RegistersValProofHelpers.lean`, and `HostIOFrame.lean` also depend on the old constructor and captures.
No such Lean statement is changed by this audit.

**Citation-only work.**
Replace `d2995380` as the stopping-rule source with merged `0249591a` and refresh line numbers in `honest_trace.lean`, `program.lean`, `Soundness/Layer7/Stopping.lean`, `StallSuffix.lean`, `methods/soundness.md`, and `model_review.md`.
Refresh moved decoder, verifier, and prover-config line references where they are used, and mark historical `8bbb2357` migration records as historical rather than silently rewriting their provenance.
The public-I/O and SDK exit diffs are comment/API-documentation changes, not a new termination equation.

**Generated expansions.**
Regeneration of `JoltBytecode/JoltISA/ExpansionsAutomated.lean` is **not indicated** by this pin.
`git diff 8bbb2357 5def437f -- crates/jolt-program/src/expand/ crates/jolt-lean-gen/` is empty, and none of that file's 57 generated programs contains `VirtualHostIO`.
The changed tracer instruction files affect direct HostIO decoding and capture, not an expansion recipe.
The checked-out generator has Ari's separate uncommitted work, so it was not run or modified during this audit.

## Validation and scope of this stop

The audit compared changed-file lists and per-file commits, both pinned source trees, exact path references in 718 Lean/selected Markdown files, the existing model declarations, and GitHub's read-only PR #2109 metadata/comparison.
No Lean declaration was added or changed, so there are no new elaboration times, theorem hypotheses, or `bv_decide` uses to report.
No build was run because the sole requested artifact is this source audit and another agent is editing Lean in the shared checkout.
This report makes no statement or definition change and proposes no proof of helper C.

## Part 2A: current pin and source citations (2026-10-22)

I checked Part A of `pin_update_plan_2.md` against the Lean declarations and immutable Jolt commit `5def437f21a0006e13c063a03f0b5a7c9b93cd6f` before editing.
The pin contains merge commit `0249591a293aa40dc4ebba92818e1367c66ea633` for a16z/jolt PR #2109; the pinned tracer's stall rule is in `jolt/tracer/src/emulator/cpu.rs:553-576` and `jolt/crates/jolt-riscv/src/row.rs:106-130`.
The pinned verifier enforces the base trace-length floor at `jolt/crates/jolt-verifier/src/config.rs:109-120` and `jolt/crates/jolt-verifier/src/verifier.rs:976-991`; the pinned HostIO decoders and executor are at `jolt/crates/jolt-program/src/image/decode.rs:192-210,253-342`, `jolt/tracer/src/instruction/mod.rs:1352-1363`, and `jolt/tracer/src/instruction/virtual_host_io.rs:19-38`.
Those source facts support the sequencing and scope of Part A; I found no false claim in that part of the plan.
The old historical explanation at `methods/soundness.md:1341` did contain a wrong claim that the merged tracer starts `prev_pc` unset.
The pinned CPU initializes `stalled` to false at `jolt/tracer/src/emulator/cpu.rs:441-453`; I corrected that prose.
The older audit's warning remains: helper C is still known false without Part B's model changes, and Part A makes no claim that it can be proved.

`AGENTS.md:97`, `methods/soundness.md:231-238`, and the new top section of `methods/model_update.md:8-12` now identify `5def437f` as current.
The prior `8bbb2357` migration and its original citations remain identified as historical.
Current stopping-rule references use PR #2109's merge commit `0249591a`.
The two pin-update plans and this report retain the former head `d2995380` only as historical provenance, not as the current stopping-rule citation.

Part 2A changed no Lean declaration, theorem statement, proof, definition, or restriction; there is no old/new statement to list.
The substantive advice-proof changes already present in this shared checkout belong to the separately approved Agent 1 work, not this part.
Part 2A introduced no `sorry`, no `bv_decide`, and no new or changed proof taking more than ten seconds.

### Changed Jolt citations

The source path in each row is relative to Jolt; the right-hand line range is the range checked with `git show 5def437f:<path>`.
Where a range stayed the same, the citation was repinned from an old commit or mutable URL to `5def437f`.
The old bytecode-geometry URLs used mutable `abiswas3/jolt` main; `JoltBytecode/JoltISA/Instruction.lean:162` used commit `e012da54`, and `DeviceFrame.lean:19` and `MemoryLayout.lean:123` used `754fc882`.
Other explicit old pins in the edited comments were `8bbb2357`.

| Pinned Jolt source | Old citation → `5def437f` lines read | Lean or constraint-document locations |
|---|---|---|
| `jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs` | `358` → `360` | `JoltConstraints/constraints.md:369` |
| `jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs` | `358-378` → `360-380` | `JoltConstraints/Constraints/BytecodeRaAtEntryEqOne.lean:15`; `JoltConstraints/Constraints/PCEqBytecodeRead.lean:14` |
| `jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs` | `533` → `594` | `JoltConstraints/constraints.md:369` |
| `jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs` | `545-552` → `606-613` | `JoltConstraints/Constraints/BytecodeReadData.lean:38` |
| `jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs` | `545-557` → `606-618` | `JoltConstraints/Constraints/OpFlagsEqBytecodeRead.lean:14`; `JoltConstraints/Constraints/UnexpandedPCEqBytecodeRead.lean:14` |
| `jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs` | `551-574` → `612-635` | `JoltConstraints/Constraints/BytecodeReadData.lean:46`; `JoltConstraints/Constraints/ImmEqBytecodeRead.lean:14` |
| `jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs` | `559-594` → `620-655` | `JoltConstraints/Constraints/InstructionFlagsEqBytecodeRead.lean:14` |
| `jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs` | `598-630` → `657-689` | `JoltConstraints/Constraints/BytecodeReadSelectors.lean:11,45,78`; `JoltConstraints/Constraints/RdWaEqBytecodeRead.lean:14`; `JoltConstraints/Constraints/Rs1RaEqBytecodeRead.lean:14`; `JoltConstraints/Constraints/Rs2RaEqBytecodeRead.lean:14` |
| `jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs` | `603-609` → `662-668` | `JoltConstraints/Constraints/BytecodeReadSelectors.lean:130`; `JoltConstraints/Constraints/InstructionRafFlagEqBytecodeRead.lean:14`; `JoltConstraints/Constraints/LookupTableFlagEqBytecodeRead.lean:14` |
| `jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs` | `607-609` → `668-670` | `JoltConstraints/Constraints/BytecodeReadSelectors.lean:122` |
| `jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs` | `724-733` → `781-789` | `JoltConstraints/Constraints/BytecodeReadData.lean:22` |
| `jolt/crates/jolt-program/src/image/decode.rs` | `71-72,192-212` → `71-72,192-210` | `JoltConstraints/expansion_helpers.lean:15` |
| `jolt/crates/jolt-program/src/image/decode.rs` | `399` → `253-342` | `JoltConstraints/metadata.lean:9` |
| `jolt/crates/jolt-program/src/image/decode.rs` | `471` → `513-520` | `JoltConstraints/witness_helpers/lookup_index.lean:48` |
| `jolt/crates/jolt-program/src/image/decode.rs` | `471-485` → `253-256,513-520` | `JoltBytecode/JoltISA/Instruction.lean:162` |
| `jolt/crates/jolt-program/src/preprocess/public_io.rs` | `21-61` → `21-65` | `JoltConstraints/honest_trace.lean:333`; `JoltConstraints/program.lean:389` |
| `jolt/crates/jolt-program/src/preprocess/public_io.rs` | `42-52` → `42-56` | `JoltConstraints/Soundness/Layer5/PanicRestriction.lean:22` |
| `jolt/crates/jolt-program/src/preprocess/public_io.rs` | `47-52` → `51-56` | `JoltConstraints/Soundness/Layer5/TerminationRestriction.lean:21`; `JoltConstraints/Soundness/Layer7/TerminationStore.lean:302,323,806` |
| `jolt/crates/jolt-prover/src/config.rs` | `208-225` → `188-204` | `JoltConstraints/witness_params.lean:146` |
| `jolt/crates/jolt-prover/src/config.rs` | `208-234` → `206-214` | `JoltConstraints/verifier_sizes.lean:38` |
| `jolt/crates/jolt-prover/src/config.rs` | `29,73-81` → `63-70` | `JoltConstraints/honest_trace.lean:270` |
| `jolt/crates/jolt-prover/src/config.rs` | `36-40` → `26-30` | `JoltConstraints/honest_trace.lean:281` |
| `jolt/crates/jolt-prover/src/config.rs` | `62-149` → `52-139` | `JoltConstraints/prover_config.lean:8` |
| `jolt/crates/jolt-prover/src/config.rs` | `63-110` → `53-100` | `JoltConstraints/language.lean:19` |
| `jolt/crates/jolt-prover/src/config.rs` | `70-72` → `60-62` | `JoltConstraints/trace_facts.lean:136` |
| `jolt/crates/jolt-prover/src/config.rs` | `73-81` → `63-70` | `JoltConstraints/trace_facts.lean:93` |
| `jolt/crates/jolt-prover/src/config.rs` | `73-81,128-133` → `63-70,116-119` | `JoltConstraints/trace_facts.lean:115` |
| `jolt/crates/jolt-prover/src/config.rs` | `94-108` → `84-98` | `JoltConstraints/trace_facts.lean:208`; `JoltConstraints/witness_params.lean:92` |
| `jolt/crates/jolt-riscv/src/row.rs` | `105-132` → `106-130` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:27,1675,1880,1892,2187,2266,2396,2614,3143`; `JoltConstraints/Soundness/Layer7/TerminationStore.lean:1017` |
| `jolt/crates/jolt-verifier/src/verifier.rs` | `356-383` → `357-380` | `JoltConstraints/Soundness/Layer5/TapeTrace.lean:67`; `JoltConstraints/honest_trace.lean:221`; `JoltConstraints/program.lean:369` |
| `jolt/crates/jolt-verifier/src/verifier.rs` | `356-430` → `357-426` | `JoltConstraints/program.lean:316` |
| `jolt/crates/jolt-verifier/src/verifier.rs` | `37-42` → `38-43` | `JoltConstraints/program.lean:314` |
| `jolt/crates/jolt-verifier/src/verifier.rs` | `378-383` → `375-380` | `JoltConstraints/program.lean:345` |
| `jolt/crates/jolt-verifier/src/verifier.rs` | `436-443` → `432-439` | `JoltConstraints/honest_trace.lean:334`; `JoltConstraints/program.lean:381` |
| `jolt/crates/jolt-verifier/src/verifier.rs` | `37-42,357,436-443` → `38-43,357,432-439` | `JoltConstraints/program.lean:388` |
| `jolt/crates/jolt-verifier/src/verifier.rs` | `992-1005` → `999-1016` | `JoltConstraints/layout_facts.lean:505`; `JoltConstraints/program.lean:370` |
| `jolt/jolt-sdk/macros/src/lib.rs` | `880-887` → `880-887` | `JoltConstraints/Soundness/Layer7/Stopping.lean:15`; `JoltConstraints/Soundness/Layer7/TerminationStore.lean:975,1016` |
| `jolt/tracer/src/emulator/cpu.rs` | `1056-1105` → `1079-1128` | `JoltConstraints/Soundness/Layer5/HostCallRestriction.lean:19` |
| `jolt/tracer/src/emulator/cpu.rs` | `24-60` → `44-60` | `JoltConstraints/Soundness/Layer7/TapeRebuild.lean:29` |
| `jolt/tracer/src/emulator/cpu.rs` | `24-60,1244-1333` → `45-60,494-515,984-1018` | `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:9` |
| `jolt/tracer/src/emulator/cpu.rs` | `329-353` → `443-449` | `JoltBytecode/Assumptions.lean:215` |
| `jolt/tracer/src/emulator/cpu.rs` | `399` → `471` | `JoltBytecode/Assumptions.lean:227` |
| `jolt/tracer/src/emulator/cpu.rs` | old `prev_pc`-unset claim → `stalled = false` at `441-453` | `methods/soundness.md:1341` |
| `jolt/tracer/src/emulator/cpu.rs` | `499-528` → `443-473` | `JoltConstraints/program.lean:39` |
| `jolt/tracer/src/emulator/cpu.rs` | `504` → `448` | `JoltConstraints/execution_facts.lean:701` |
| `jolt/tracer/src/emulator/cpu.rs` | `553-578` → `553-576` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:675,1106,1372,1497,1788,2662,2720,2760,2967,2996`; `JoltConstraints/Soundness/Layer7/Stopping.lean:16`; `JoltConstraints/Soundness/Layer7/TerminationStore.lean:909` |
| `jolt/tracer/src/emulator/cpu.rs` | `622-632` → `581-620,657-679` | `JoltConstraints/Soundness/Layer5/TapeTrace.lean:34,45`; `JoltConstraints/Soundness/Layer7/StallSuffix.lean:689,824,858,882,915,997,1067,1336`; `JoltConstraints/Soundness/Layer7/TerminationStore.lean:123,257,908`; `JoltConstraints/honest_trace.lean:66,77` |
| `jolt/tracer/src/emulator/cpu.rs` | `628-632` → `657-679` | `JoltConstraints/honest_trace.lean:24`; `JoltConstraints/trace_interface.lean:22` |
| `jolt/tracer/src/emulator/mod.rs` | `242-248` → `219-225` | `JoltBytecode/JoltISA/DeviceMemory.lean:102` |
| `jolt/tracer/src/emulator/mod.rs` | `242-261` → `219-239` | `JoltConstraints/program.lean:298` |
| `jolt/tracer/src/emulator/mod.rs` | `285` → `262` | `JoltConstraints/program.lean:40` |
| `jolt/tracer/src/instruction/fence.rs` | `19-25` → `20-26` | `JoltConstraints/Soundness/Layer5/Fence.lean:9` |
| `jolt/tracer/src/instruction/mod.rs` | `207-233` → `207-233` | `JoltConstraints/Soundness/Layer7/TapeRebuild.lean:1929` |
| `jolt/tracer/src/instruction/mod.rs` | `215-241` → `215-241` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:1055`; `JoltConstraints/trace.lean:19` |
| `jolt/tracer/src/instruction/virtual_advice_load.rs` | `20-27` → `20-27` | `JoltBytecode/InstructionEquivalence/ProofSupport/InstructionFrame.lean:10` |
| `jolt/tracer/src/lib.rs` | `89-97,364-408` → `89-97,351-395` | `JoltConstraints/Soundness/Layer5/TapeTrace.lean:30`; `JoltConstraints/honest_trace.lean:62` |
| `jolt/tracer/src/lib.rs` | `327-337` → `321-325` | `JoltConstraints/Soundness/Layer5/TapeTrace.lean:34`; `JoltConstraints/honest_trace.lean:66` |
| `jolt/tracer/src/lib.rs` | `364-408` → `351-395` | `JoltConstraints/layout_facts.lean:538`; `JoltConstraints/program.lean:411`; `JoltConstraints/trace_interface.lean:56` |
| `jolt/tracer/src/lib.rs` | `379-390` → `366-377` | `JoltConstraints/layout_facts.lean:224` |
| `jolt/tracer/src/lib.rs` | `382-393` → `367-377` | `JoltConstraints/Constraints/MemoryLayout.lean:123` |
| `jolt/tracer/src/lib.rs` | `398-399` → `385-386` | `JoltConstraints/layout_facts.lean:583` |
| `jolt/tracer/src/lib.rs` | `401-404` → `388-391` | `JoltBytecode/InstructionEquivalence/ProofSupport/DeviceFrame.lean:19` |
| `jolt/tracer/src/lib.rs` | `74-131` → `74-130` | `JoltConstraints/honest_trace.lean:213` |

For the stopping-rule citation, `d2995380` (the PR's former head) became merge commit `0249591a` at `AGENTS.md:99`, `methods/soundness.md:108,1341,1353`, `methods/step_c_closing_plan.md:18`, `JoltConstraints/model_review.md:216`, `JoltConstraints/execution_conditions.lean:7`, `JoltConstraints/trace_interface.lean:132`, `JoltConstraints/program.lean:132`, `JoltConstraints/honest_trace.lean:35,228,237`, `JoltConstraints/Soundness/Layer5/TapeTrace.lean:74,83`, `JoltConstraints/Soundness/Layer5/MemoryAccessRestriction.lean:28`, and `JoltConstraints/Soundness/Layer7/TapeRebuild.lean:2131`.
The same commit substitution accompanies pinned CPU lines `553-578` → `553-576` at `JoltConstraints/Soundness/Layer7/StallSuffix.lean:675,1106,1372,1497,1788,2662,2720,2760,2967,2996`, `JoltConstraints/Soundness/Layer7/Stopping.lean:16`, and `JoltConstraints/Soundness/Layer7/TerminationStore.lean:909`.
It accompanies pinned row lines `105-132` → `106-130` at `JoltConstraints/Soundness/Layer7/StallSuffix.lean:27,1675,1880,1892,2187,2266,2396,2614,3143` and `JoltConstraints/Soundness/Layer7/TerminationStore.lean:1017`.
I also checked the tracer loops that consume the stall flag at `jolt/tracer/src/lib.rs:106-123,198-205,321-325` and `jolt/tracer/src/parallel.rs:251-273`.

### Validation

`lake build JoltBytecode JoltConstraints` completed successfully with 8,802 jobs after the final citation edits.
`git diff --check` passed, and a repository search found no active `d2995380` reference outside the historical pin plans and audit.
The build retains existing warnings and existing `sorry` declarations; Part 2A added none.

`#print axioms JoltInstance.soundness` returned `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`, and `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5`.
`#print axioms JoltInstance.completeness` returned those six plus `JoltConstraints.halfword_aligned._native.bv_decide.ax_1_5`, `JoltConstraints.lookupEntryCorrect_RangeCheckAligned._native.bv_decide.ax_1_241`, `JoltConstraints.rev8_32._native.bv_decide.ax_1_10`, `JoltConstraints.windowMaskB_entry._native.bv_decide.ax_1_5`, `JoltConstraints.windowMaskH_entry._native.bv_decide.ax_1_5`, `JoltConstraints.windowMaskW_entry._native.bv_decide.ax_1_5`, and `JoltConstraints.word_aligned._native.bv_decide.ax_1_5`.
Both theorems still have the pre-existing `sorryAx`; citation-only edits introduced no new axiom dependency.
No commit was made.

## Part 2B: verifier floor and full-length restriction (2026-10-22)

I checked Part B against the Lean code and Jolt commit `5def437f21a0006e13c063a03f0b5a7c9b93cd6f` before editing.
Jolt's base verifier rejects trace lengths below 256 and above the instance maximum at `jolt/crates/jolt-verifier/src/verifier.rs:976-991`, using the base constant at `jolt/crates/jolt-verifier/src/config.rs:109-120`; both verifier validation paths call this check at `verifier.rs:379,1055-1058`.
Jolt's prover adds a row, rounds the length to a power of two and applies the same 256 floor at `jolt/crates/jolt-prover/src/config.rs:63-70`, then rejects a padded length above the maximum at `config.rs:116-119`.
The Lean witness length is a power of two (`JoltConstraints/witness.lean:125`), and `ProverPaddedFor` already supplies the base or Akita prover floor (`witness.lean:133-142`).
No false Part B claim was found in the verifier-admissible range.
The formula `2 ^ Nat.log2 max` denotes the largest power of two at most `max` when `max` is positive; any satisfying context now requires `max ≥ 256`, so this is the range in which the restriction matters.

If the witness length is `T`, its represented trace has `n ≤ T` real rows and `T ≤ max`.
Let `M = 2 ^ Nat.log2 max`.
When `n < T`, Jolt's prover can pad to at most `T`; when `n = T < M`, it pads to `2T ≤ M`.
The previously identified length mismatch is exactly `n = T = M`, which `NoMaxLengthTrace` excludes; this arithmetic does not prove helper C's separate last-jump or RAM-address obligations.
For example, under a maximum of 1024, the restriction permits a 256-row trace and Jolt's prover pads it to 512, while it excludes a 1024-row trace.
The cited blog post records the mismatch at the older `8bbb2357` pin; the prover formula and current verifier floor above were checked again at `5def437f`.

### Declaration changes

| Declaration and location | Old statement or field | New statement or field |
|---|---|---|
| `ConstraintContext` in `JoltConstraints/constraint_context.lean:17,33` | `traceLengthBound : params.traceLength ≤ joltInstance.max_padded_trace_length.toNat` only | The same upper bound plus `traceLengthFloor : 256 ≤ params.traceLength` beside it, strengthening the context used by `AllConstraints` while leaving Akita's 4096 floor outside the base model. |
| `JoltInstance.NoMaxLengthTrace` in `JoltConstraints/Soundness/Assumptions.lean:71` | Absent | `∀ privateInputs (trace : UntrustedAnswerTrace joltInstance privateInputs), trace.rows.size ≠ 2 ^ Nat.log2 joltInstance.max_padded_trace_length.toNat`, with a docstring defining the real-row count and giving the 256/1024 example. |
| `JoltInstance.TemporaryRestrictions` in `JoltConstraints/Soundness/Assumptions.lean:83,113` | No trace-length restriction | New field `noMaxLengthTrace : joltInstance.NoMaxLengthTrace`, marked FIXME and linked to `blog/content/blog/prover-verifier-trace-length/index.md`. |
| `HonestTrace.allConstraints_corrected_sizes` in `JoltConstraints/Completeness/All.lean:179,215` | Statement unchanged; context constructor supplied only the upper bound | Statement unchanged; its proof now supplies `traceLengthFloor` from `trace.corrected_witness_params_padded`, covering both existing `ProverPaddedFor` branches. |
| `JoltInstance.soundness_prover_accepts` in `JoltConstraints/Soundness/TopLevel.lean:150-159` | No `NoMaxLengthTrace` hypothesis; conclusion `(trace.prover_config joltInstance).isSome` | Adds `(noMaxLengthTrace : joltInstance.NoMaxLengthTrace)` after the instance; the conclusion and existing hypotheses are unchanged, and the proof remains `sorry`. |
| `JoltInstance.soundness` in `JoltConstraints/Soundness/soundness.lean:26,42` | The explicit theorem statement already took `restrictions : joltInstance.TemporaryRestrictions`; its C call lacked the new field | The explicit statement is unchanged but the bundle is stronger; the C call passes `restrictions.noMaxLengthTrace`. |

No declaration was deleted, no core language definition was changed, and the `DANGER` label was removed only after the verifier floor and temporary restriction excluded the two known counterexamples.
`JoltConstraints/model_review.md:152,176,188-191` and `methods/soundness.md:95,110,118` now describe the revised obligations and still identify helper C as `sorry`.

### Source citations changed

| Location | Old reference | New reference and pinned Jolt lines checked |
|---|---|---|
| `JoltConstraints/constraint_context.lean:31-32` | None | `jolt/crates/jolt-verifier/src/verifier.rs:976-991` and `jolt/crates/jolt-verifier/src/config.rs:109-120` at `5def437f`. |
| `JoltConstraints/Soundness/Assumptions.lean:69-70` | None | `jolt/crates/jolt-prover/src/config.rs:63-70,116-119` at `5def437f`. |
| `JoltConstraints/model_review.md:188` | None | `jolt/crates/jolt-verifier/src/verifier.rs:976-991` and `jolt/crates/jolt-verifier/src/config.rs:109-120` at `5def437f`. |

No existing Jolt citation was changed in Part 2B.
No new `bv_decide` was used.
No new or changed proof took more than ten seconds; the targeted build compiled `Completeness/All.lean` in 6.0 seconds and `Soundness/TopLevel.lean` in 3.8 seconds, including their entire files.

### Validation

`lake build JoltBytecode JoltConstraints` completed successfully with 8,802 jobs, with only the repository's existing warnings.
`git diff --check` passed.
`#print axioms JoltInstance.soundness` returned `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`, and `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5`.
`#print axioms JoltInstance.completeness` returned those six plus `JoltConstraints.halfword_aligned._native.bv_decide.ax_1_5`, `JoltConstraints.lookupEntryCorrect_RangeCheckAligned._native.bv_decide.ax_1_241`, `JoltConstraints.rev8_32._native.bv_decide.ax_1_10`, `JoltConstraints.windowMaskB_entry._native.bv_decide.ax_1_5`, `JoltConstraints.windowMaskH_entry._native.bv_decide.ax_1_5`, `JoltConstraints.windowMaskW_entry._native.bv_decide.ax_1_5`, and `JoltConstraints.word_aligned._native.bv_decide.ax_1_5`.
These match Part 2A: both top-level theorems still depend on existing `sorryAx`, and Part 2B added no axiom dependency.
No commit was made.

## Part 2C: operandless HostIO (2026-10-22)

### Audit before implementation

I read the pin audit and the approved Parts 2A and 2B, checked that this checkout was on `feat/soundness` at `c62ebad`, and checked every Part C claim against the Lean code and Jolt commit `5def437f21a0006e13c063a03f0b5a7c9b93cd6f` before editing.
The working tree was clean at the start.
All Jolt evidence came from `git show 5def437f:<path>`; the separate Jolt working tree was not used or changed.
No false claim or insufficient proof change was found in Part C.

Jolt's program decoder rejects a nonzero encoded `rd` and supplies default operands for HostIO (`jolt/crates/jolt-program/src/image/decode.rs:204-209,335-339`).
Jolt's interpreter decoder has the same `rd` rejection (`jolt/tracer/src/instruction/mod.rs:1352-1363`); its `FormatNoOperands` ignores the encoded word and converts to default normalized operands (`jolt/tracer/src/instruction/format/format_no_operands.rs:6-29`).
Those defaults have no `rs1`, `rs2` or `rd` and immediate zero (`jolt/crates/jolt-riscv/src/row.rs:10-20`).
The typed Lean source constructor represents a successfully decoded instruction, so it has no encoded word to validate and no fields for the ignored `rs1` or immediate bits.

Jolt's expander performs its x0 rewrite only for `rd = Some(0)` and otherwise passes a native row through (`jolt/crates/jolt-program/src/expand/materialize.rs:79-101`).
An absent `rd` therefore avoids the rewrite.
Jolt's tracer captures no HostIO register values (`jolt/tracer/src/instruction/registers/no_operands.rs:13-32`, with the absent-value defaults at `registers/mod.rs:30-43`).
Jolt's witness backend changes the register table only for a present `rd_index()` and makes selectors only for present operand indices (`jolt/crates/jolt-witness/src/backend/trace/registers.rs:26-63`).
The bytecode selector relation also maps absent operands to zero (`jolt/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs:657-689`).

Jolt's HostIO executor still reads x10–x13 implicitly and calls its host handlers without writing a CPU register (`jolt/tracer/src/instruction/virtual_host_io.rs:19-38`, `jolt/tracer/src/emulator/cpu.rs:1079-1156`).
The existing Lean `execHostIOWith` and successful-execution frame remain applicable.
`RegisterAgreement.noWrite` applies to the new absent destination; transporting its result across equality of Sail state and virtual registers proves full post-step agreement.
The no-destination fact follows directly from the instruction constructor, so no program-wide destination lemma or replacement premise is needed.
`HostCallsSucceed` still supplies successful execution and remains a separate restriction.

The remaining need for live-register agreement was checked against the approved advice fix and the current REM expansion: quotient temporary 40 is not reset at the end of the expansion, and zero-divisor quotient advice can differ without changing the architectural result (`jolt/crates/jolt-program/src/expand/division/rem.rs:10-32`, `jolt/tracer/src/instruction/rem.rs:44-55`).
Instruction temporaries are still registers 40–47 (`jolt/crates/jolt-program/src/expand/allocator.rs:133-143`).
The general head/tail first-access lemmas are used by the control-operand proof in `Layer7/StallSuffix.lean`; they were retained.
Only the HostIO-specific liveness helpers and their now-unused `firstRow?` definition were removed.

### Definitions and theorem statements changed

Locations below are in the resulting checkout, except deletion locations, which refer to parent commit `c62ebad`.
In the tables, `.VirtualHostIO dst src imm` denotes the old bytecode constructor and `.VirtualHostIO` the new constructor.
No new declaration name, hypothesis, restriction, `sorry`, `bv_decide` use, or limit override was added.
The existing source and bytecode constructor names are retained with no arguments.

| Declaration and location | Old behavior or statement | New behavior or statement |
|---|---|---|
| `JoltISA.Instr.VirtualHostIO`, `JoltBytecode/JoltISA/Instruction.lean:150` | `(dst : Dst) (src : Src) (imm : BitVec 64 := 0)` | Operandless constructor. |
| `JoltCustomInstruction.VirtualHostIO`, `JoltConstraints/expansion_helpers.lean:28` | `(rd rs1 : regidx) (imm : BitVec 12)` | Operandless constructor for successfully decoded HostIO. |
| `SourceInstruction.expand`, `JoltConstraints/expansions.lean:15` | HostIO expands with architectural destination, source and sign-extended immediate, then native rewriting. | HostIO expands to `some (.ofNative .VirtualHostIO)`, definitionally `some (.native .VirtualHostIO)`. |
| `Instr.destination?`, `JoltBytecode/JoltISA/Instruction.lean:413` | HostIO returns `some dst`. | HostIO returns `none`. |
| `Instr.rewriteNative`, `JoltBytecode/JoltISA/Instruction.lean:448` | A special HostIO arm applies `sideEffectingDst dst`. | That arm is deleted; the absent destination leaves HostIO unchanged. Other uses of `sideEffectingDst` remain. |
| `JoltMetadata.immediate`, `JoltConstraints/metadata.lean:13` | HostIO returns `imm.toNat`. | HostIO returns zero. |
| `JoltRegisterEncoding.instructionIsCanonical`, `JoltConstraints/register_encoding.lean:43` | Checks HostIO destination and source canonicality. | Returns `true` for operandless HostIO. |
| `bytecodeRs1Register`, `bytecodeRs2Register`, `bytecodeRdRegister`, `JoltConstraints/Constraints/BytecodeReadSelectors.lean:12,46,79` | HostIO has `some (sourceRegisterAddress src)`, `none`, and `some (destinationRegisterAddress (capturedDestination dst))`, respectively. | All three return `none`; the second-source change is only constructor syntax. |
| `TraceWitness.Rs1Value`, `JoltConstraints/witness_helpers/rs1_value.lean:16` | Captures the named source's pre-state value. | Returns zero for HostIO. |
| `TraceWitness.Rs1Ra`, `JoltConstraints/witness_helpers/rs1_ra.lean:16` | Selects the named source register. | Selects no register for HostIO. |
| `TraceWitness.RdWa`, `JoltConstraints/witness_helpers/rd_wa.lean:15` | Selects HostIO's captured destination. | Selects no register for HostIO. |
| `TraceWitness.rdValue`, `JoltConstraints/witness_helpers/rd_value.lean:14` | Encodes HostIO's captured destination value. | Returns zero for HostIO in both pre- and post-state uses. |
| `ExpansionTempLiveness.readSources`, `JoltConstraints/expansion_temp_liveness.lean:18` | HostIO returns `[src]`. | HostIO returns `[]`; implicit host arguments are not normalized operands. |
| `rs1Operand?`, `rs2Operand?`, `JoltConstraints/Completeness/Helpers/RegistersReadProofHelpers.lean:19,48` | HostIO returns `some src` and `none`. | Both return `none`; the second-source change is only syntax. |
| `ExpansionFacts.virtualHostIO_native_ok`, `JoltConstraints/expansion_facts.lean:793` | Takes `rd rs1 imm` and proves `ExpandedOk` for their native HostIO row. | Takes no operands and proves `ExpandedOk (.ofNative JoltISA.Instr.VirtualHostIO)`. |
| `JoltInstance.TemporaryRestrictions`, `JoltConstraints/Soundness/Assumptions.lean:74` | Contains `hostCallRdZero : joltInstance.program.HostCallRdZero`. | Removes that field and its FIXME; all other fields remain. |
| `JoltInstance.HostCallsSucceed`, `JoltConstraints/Soundness/Layer5/HostCallRestriction.lean:33` | Successful-execution condition matches the three-argument constructor. | The same condition matches the operandless constructor. |
| `host_call_exec_sail_frame`, `JoltConstraints/Soundness/Layer5/HostCallRestriction.lean:51` | Takes `dst src imm answer` and equality to the three-argument HostIO. | Takes `answer` and equality to operandless HostIO; the execution and Sail/virtual-register frame conclusion is unchanged. |
| `host_call_selected_step`, `JoltConstraints/Soundness/Layer5/HostCallRegisterFrame.lean:26` | Takes `restrictedDestination : program.HostCallRdZero`, implicit destination/source/immediate, and a three-argument HostIO equality; returns execution and `RegisterAgreementExceptHostTemp`. | Removes that restriction and those operand parameters, requires `row.instruction = .VirtualHostIO`, and returns execution and full `RegisterAgreement witness ⟨t.val + 1, nextCycle⟩ post`. All other hypotheses remain. |
| `withRuntimeAdvice_hostIO`, `JoltConstraints/trace_interface.lean:164` | Takes three operand parameters and preserves their HostIO constructor. | Takes only runtime advice and `instruction = .VirtualHostIO`, and concludes `instruction.withRuntimeAdvice advice = .VirtualHostIO`. |
| `JoltPCFrame.ordinary_instruction`, `JoltConstraints/Completeness/Helpers/TracePCProofHelpers.lean:155`; `JoltNextPCFrame.ordinary_instruction`, `JoltConstraints/nextpc_frame.lean:202` | HostIO exclusion is `∀ dst src imm, instr ≠ .VirtualHostIO dst src imm`. | Exclusion is `instr ≠ .VirtualHostIO`; all other hypotheses and conclusions remain. |
| `swap_execInstr_nonhost`, `JoltConstraints/Soundness/Layer7/TapeRebuild.lean:680` | The same quantified HostIO exclusion. | `instr ≠ .VirtualHostIO`; its other hypothesis and `SwapInvariant` conclusion remain. |

`host_call_selected_step` uses the existing `RegisterAgreement.noWrite`, then transports register values with the retained private `sourceValue_of_host_frame` at `HostCallRegisterFrame.lean:14`.
`execHostIOWith`, `RegisterAgreement`, `RegisterAgreement.noWrite`, `InLanguage`, and the explicit top-level theorem statements were not edited.
The soundness theorem's restriction bundle is weaker because the obsolete destination field is gone.
The existing prefix theorem and helpers C and D remain `sorry`.

### Mechanical proof and pattern updates

The following declarations retain their statements, apart from the instruction types now having an operandless HostIO constructor.
Only the corresponding constructor arm, its arguments, or its direct caller was updated.

| Declaration | Location |
|---|---|
| `JoltISA.execInstr` | `JoltBytecode/JoltISA/Semantics.lean:38` |
| `JoltISA.InstrWritesNoProtectedVReg`; `JoltISA.execInstr_preserves_protected` | `JoltBytecode/InstructionEquivalence/ProofSupport/Basic.lean:171,776` |
| `JoltISA.Instr.WritesProtectedVReg` | `JoltBytecode/InstructionEquivalence/ProofSupport/ProtectedVRegWrites.lean:25` |
| `TraceWitness.Rs2Ra`; `TraceWitness.Rs2Value` | `JoltConstraints/witness_helpers/rs2_ra.lean:16`; `JoltConstraints/witness_helpers/rs2_value.lean:16` |
| `TraceWitness.instructionLookupIndex` | `JoltConstraints/witness_helpers/lookup_index.lean:25` |
| `ExpansionFacts.expand_ok` | `JoltConstraints/expansion_facts.lean:813` |
| `HonestTraceRow.hostIOPreservesPC` | `JoltConstraints/trace_interface.lean:171` |
| `JoltPCFrame.instruction` | `JoltConstraints/Completeness/Helpers/TracePCProofHelpers.lean:230` |
| `JoltNextPCFrame.instruction` | `JoltConstraints/nextpc_frame.lean:336` |
| `JoltNextPCFrame.hostIOFrame_of_exec` | `JoltConstraints/Completeness/Helpers/HostIOFrame.lean:95` |
| `register42_instruction_preserves_other` | `JoltConstraints/Completeness/Helpers/RegistersValProofHelpers.lean:617` |
| `swap_execInstr_nonload` | `JoltConstraints/Soundness/Layer7/TapeRebuild.lean:782` |
| `noncontrol_tape_next_pc`; `tape_row_preserves_pc` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:859,883` |

`ExpansionTempLiveness.tempsReadAfterWrite` at `JoltConstraints/expansion_temp_liveness.lean:80` has only a docstring change: its example is now quotient advice left by REM, with its formula unchanged.
The requested live-register paragraph at `methods/soundness.md:138` explains that HostIO preserves full agreement and division scratch values still require live-register agreement.
The deleted restriction's current assumption-table row was also removed from `JoltConstraints/model_review.md:148`; the historical pin audit and dated history entries remain intact.
No other section of `methods/soundness.md` was changed.

### Deleted declarations

These were solely for the old synthetic HostIO destination and are not replaced by new hypotheses.
The table gives their old locations at `c62ebad` and the removed statement's role.

| Deleted declaration | Old location | Removed statement or definition |
|---|---|---|
| `Rv64ProgramImage.HostCallRdZero` | `JoltConstraints/Soundness/Assumptions.lean:54` | Every source HostIO has `isX0 rd = true`. |
| `host_call_rewrite_register_is_40` | `JoltConstraints/Soundness/Layer5/HostCallRegisterFrame.lean:25` | `rdZeroRewriteVReg = BitVec.ofNat 7 40`. |
| `host_call_zero_destination_is_temp` | Same file, line 30 | An x0-destination source HostIO expands with destination `.vreg rdZeroRewriteVReg`. |
| `RegisterAgreement.host_call_other` | Same file, line 40 | Post-step agreement at all registers except the selected HostIO destination. |
| `RegisterAgreementExceptHostTemp` | Same file, line 75 | Register presence and table/state agreement away from register 40. |
| `RegisterAgreementExceptHostTemp.read` | Same file, line 86 | Read agreement for a canonical source whose address is not 40. |
| `RegisterAgreementExceptHostTemp.noWrite` | Same file, line 101 | A destination-free row preserves agreement excluding register 40. |
| `RegisterAgreementExceptHostTemp.write_temp` | Same file, line 126 | A constrained write to register 40 restores full agreement. |
| `RegisterAgreementExceptHostTemp.write` | Same file, line 172 | A constrained destination write preserves agreement excluding register 40. |
| `source_available_of_not_read` | Same file, line 212 | A canonical operand in a row not reading the HostIO temporary has address other than 40. |
| `RegisterAgreementExceptHostTemp.read_first_row` | Same file, line 235 | First-row reads of a checked source expansion are available under the exception relation. |
| `RegisterAgreement.host_call_except_temp` | Same file, line 253 | A temporary-destination HostIO step produces the exception relation. |
| `host_source_native_destination` | `JoltConstraints/Soundness/Layer5/HostCallExpansion.lean:15` | A restricted native HostIO expansion has the rewritten temporary destination. |
| `NotHostIO` | Same file, line 38 | Predicate excluding HostIO rows. |
| `sequenceRowOk_no_host` | Same file, line 42 | A checked sequence row satisfies `NotHostIO`. |
| `rowsOk_no_host` | Same file, line 48 | Every member of a checked sequence satisfies `NotHostIO`. |
| `host_not_in_sequence` | Same file, line 75 | A source expansion sequence contains no HostIO. |
| `host_expanded_destination` | Same file, line 83 | A HostIO in one restricted source row's stamped expansion has the temporary destination. |
| `host_program_destination` | Same file, line 124 | `HostCallRdZero` forces every expanded HostIO destination to the rewrite temporary. |
| `ExpansionTempLiveness.hostTemp_firstAccessIsWrite` | `JoltConstraints/expansion_temp_liveness.lean:85` | The temporary-liveness check includes `rdZeroRewriteVReg`. |
| `ExpansionTempLiveness.firstRow?` | Same file, line 118 | Returns the first instruction of a native or sequence expansion. |
| `ExpansionTempLiveness.hostTemp_firstRow_noRead` | Same file, line 124 | A checked expansion's first row does not read the HostIO rewrite temporary. |

`HostCallExpansion.lean` was deleted together with its sole import in `HostCallRegisterFrame.lean`.
A repository-wide Lean search found no remaining reference to the removed restriction, exception relation, destination lemmas or HostIO liveness helpers.
The general `firstAccessIsWrite_head_no_read` and `firstAccessIsWrite_tail` remain used by `StallSuffix.lean`.

### Source citations changed or added

Every new source reference below is at `5def437f`, and the listed Jolt lines were read at that commit.
Unchanged source references were left as they were.

| Location | Old reference | New reference / checked Jolt lines |
|---|---|---|
| `JoltBytecode/JoltISA/Instruction.lean:145` | Local path `tracer/src/instruction/virtual_host_io.rs:8` and `format/format_i.rs:72` describing captured operands. | `jolt/tracer/src/instruction/virtual_host_io.rs:9-38` and `jolt/tracer/src/instruction/format/format_no_operands.rs:6-29`. |
| `JoltConstraints/expansion_helpers.lean:24` | No constructor-specific citation; `FormatI` comment. | `jolt/crates/jolt-program/src/image/decode.rs:204-209,335-339`. |
| `JoltConstraints/expansions.lean:125` | `jolt/tracer/src/instruction/format/format_i.rs:18-24` for sign extension. | `jolt/crates/jolt-program/src/image/decode.rs:335-339` for absent operands. |
| `JoltConstraints/expansion_facts.lean:790` | None. | `jolt/crates/jolt-program/src/expand/materialize.rs:79-101`. |
| `JoltConstraints/Soundness/Layer5/HostCallRegisterFrame.lean:20` | None in the selected-step docstring. | `jolt/tracer/src/instruction/virtual_host_io.rs:9-38` and `jolt/crates/jolt-witness/src/backend/trace/registers.rs:26-57`. |
| `JoltConstraints/Soundness/Layer5/HostCallRestriction.lean:16-19` | Pin label `8bbb2357`; `jolt/tracer/src/instruction/virtual_host_io.rs:19-39`. | Pin label `5def437f`; `virtual_host_io.rs:9-38`. Rechecked the unchanged accompanying ranges `jolt/crates/jolt-riscv/src/instructions/virt/host_io.rs:3-6` and `jolt/tracer/src/emulator/cpu.rs:1079-1128`. |
| `JoltConstraints/witness_helpers/rd_value.lean:12` | No HostIO-specific citation; comment claimed a captured destination. | `jolt/tracer/src/instruction/registers/no_operands.rs:13-32`. |
| `JoltConstraints/witness_helpers/rd_wa.lean:14` | No HostIO-specific citation; comment claimed a captured destination. | `jolt/crates/jolt-program/src/image/decode.rs:335-339`. |

### Validation and proof timings

`lake build JoltBytecode JoltConstraints` completed successfully with 8,801 jobs.
The initial build caught one remaining `rename_i` that expected the old HostIO operands in `tape_row_preserves_pc`; it was removed before the successful final build.
Two now-redundant `intros` tactics in PC-frame callers were also removed.
The final build retains existing repository warnings and existing `sorry` declarations.
`git diff --check` passed, and a diff search found no added `sorry`, `bv_decide`, `native_decide`, `decide +kernel`, or `maxHeartbeats` setting.

`#print axioms JoltInstance.soundness` returned `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`, and `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5`.
`#print axioms JoltInstance.completeness` returned those six plus `JoltConstraints.halfword_aligned._native.bv_decide.ax_1_5`, `JoltConstraints.lookupEntryCorrect_RangeCheckAligned._native.bv_decide.ax_1_241`, `JoltConstraints.rev8_32._native.bv_decide.ax_1_10`, `JoltConstraints.windowMaskB_entry._native.bv_decide.ax_1_5`, `JoltConstraints.windowMaskH_entry._native.bv_decide.ax_1_5`, `JoltConstraints.windowMaskW_entry._native.bv_decide.ax_1_5`, and `JoltConstraints.word_aligned._native.bv_decide.ax_1_5`.
Both lists exactly match Part 2B.
A dependency traversal from soundness found only the same three declarations directly using `sorryAx`: `soundness_execution_prefix_agreement`, `soundness_prover_accepts`, and `soundness_spoil_asserts_pass`.
Both `host_call_selected_step` and `host_call_exec_sail_frame` have axiom lists `[propext, sys_enable_experimental_extensions, Classical.choice, Quot.sound]`, with no `sorryAx` or `bv_decide` axiom.
No new `bv_decide` entry is needed in `model_review.md`.

Every changed proof was profiled with `lake env lean -j1 -Dtrace.Elab.async=true -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 <file>`.
All eleven profiled files type-checked successfully.
The following numbers are Lean's proof-elaboration times, excluding imports and file startup; no changed proof exceeded ten seconds.
There are no new hand-written declarations to time.

| Changed proof (locations above) | Elaboration time |
|---|---|
| `JoltISA.execInstr_preserves_protected` | 1.836 s |
| `JoltNextPCFrame.hostIOFrame_of_exec` | 0.042 s |
| `register42_instruction_preserves_other` | 5.287 s |
| `JoltPCFrame.ordinary_instruction` | 8.107 s |
| `JoltPCFrame.instruction` | 0.097 s |
| `JoltConstraints.Soundness.host_call_selected_step` | 0.210 s |
| `JoltConstraints.Soundness.host_call_exec_sail_frame` | 0.010 s |
| `JoltInstance.noncontrol_tape_next_pc` | 0.569 s |
| `JoltInstance.tape_row_preserves_pc` | 0.026 s |
| `JoltConstraints.Soundness.swap_execInstr_nonhost` | 0.535 s |
| `JoltConstraints.Soundness.swap_execInstr_nonload` | 0.006 s |
| `ExpansionFacts.virtualHostIO_native_ok` | 0.057 s |
| `ExpansionFacts.expand_ok` | 0.235 s |
| `JoltNextPCFrame.ordinary_instruction` | 4.969 s |
| `JoltNextPCFrame.instruction` | 0.391 s |
| `withRuntimeAdvice_hostIO` | < 0.001 s |
| `HonestTraceRow.hostIOPreservesPC` | 0.019 s |

The entries above one second are existing generic instruction dispatchers whose HostIO arms or exclusions changed mechanically.
Their shared proofs were retained; splitting them into extra constructor-specific proofs for timing would add proof structure beyond the operandless migration.
The substantive HostIO register step takes 0.210 seconds and directly uses the existing no-write and state-frame facts.


The successful build log is `/private/tmp/pin-2c-build-final.log`, the axiom audit log is `/private/tmp/pin-2c-axioms.log`, and per-file profiling logs are `/private/tmp/pin-2c-profile-0.log` through `/private/tmp/pin-2c-profile-10.log`.
No commit was made.
Work stopped after appending this Part 2C report.

