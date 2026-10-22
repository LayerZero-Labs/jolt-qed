# Pin update: `8bbb2357` to `5def437f`, part 2 (implementation)

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, then `methods/pin_update_report.md` (the audit, part 1), whose findings this plan implements.
Start only after the advice fix (`methods/advice_fix_plan.md`) is finished and Ari has approved its report: both change `Soundness/Layer7/StallSuffix.lean`.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code and Jolt before relying on it, and stop and report if one is wrong.

Ari's decision (2026-10-22): the model follows Jolt.
Model Jolt's main at `5def437f21a0006e13c063a03f0b5a7c9b93cd6f`.
Read it with `git -C /Users/ari.biswas/Work-with-A16z/jolt show 5def437f:<path>`; the working tree there holds Ari's own work, so do not read from it or modify it.

Do one part at a time, in order.
After each part, build, add that part's section to the report (see "Before you stop"), and stop; Ari will tell you when to continue.
If a part needs a change this plan does not list, beyond mechanical pattern-match updates, stop and report it.

## Part A: the pin and citations

- Record `5def437f` as the current pin in `AGENTS.md`, in `methods/soundness.md`, and in a new section at the top of `methods/model_update.md`.
  Keep the earlier `8bbb2357` records, marked as historical; do not rewrite their provenance.
- Cite the stopping rule at the merge of a16z/jolt PR #2109, `0249591a`, instead of the PR head `d2995380`, in every file that mentions `d2995380` (find them with a repository-wide search).
- Refresh the line numbers of citations into the files the audit lists as changed.
  Citations into unchanged files need no edit.

## Part B: the verifier's trace-length floor

Jolt's verifier now rejects a proof whose padded trace length is below 256 in the base build (`crates/jolt-verifier/src/verifier.rs:976-991`, `crates/jolt-verifier/src/config.rs:109-120`; commit `521e53f6`).
The model's verifier-side check on the witness length is `ConstraintContext.traceLengthBound` (`JoltConstraints/constraint_context.lean:28`).

- Add a field to `ConstraintContext` next to it: `256 ≤ params.traceLength`, citing those lines.
  Model only the base build; Akita (4096) is out of scope.
- Completeness must supply the new field: `HonestTrace.allConstraints_corrected_sizes` (`JoltConstraints/Completeness/All.lean:179`) builds a context; prove the floor there from the prover's padding (`ProverConfig.checkedTraceLength`, `JoltConstraints/prover_config.lean:43-47`, and `WitnessParams.ProverPaddedFor`, `JoltConstraints/witness_params.lean`).
- Add a temporary restriction for helper C's other counterexample, approved by Ari on 2026-10-22.
  The case: a witness of length `T`, the largest power of two at most the instance's maximum (`max_padded_trace_length`), with all `T` rows real.
  Jolt's verifier accepts it, but Jolt's prover pads to `padded_trace_length T = 2T` (`JoltConstraints/honest_trace.lean:271`), above the maximum, and refuses; the claim is true but not in L.
  Add a field to `JoltInstance.TemporaryRestrictions` (`Soundness/Assumptions.lean:65`): for every set of private inputs and every `UntrustedAnswerTrace` of the program, the number of rows is not `M`, where `M` is the largest power of two at most `max_padded_trace_length` (for example `2 ^ Nat.log 2 max`).
  Exclude only that row count: a run of 256 rows under a maximum of 1024 is fine, because the prover pads it to 512.
  Write it as a FIXME in the style of the other fields, linking `blog/content/blog/prover-verifier-trace-length/index.md`, and saying that it is a mismatch between Jolt's prover and verifier, to be removed when Jolt resolves it.
  Give the new definition a docstring with this example.
- With the floor and this restriction, helper C (`soundness_prover_accepts`, `Soundness/TopLevel.lean:162`) is no longer known to be false.
  Pass it the restriction (it is a caller-provable fact from the restrictions bundle), keep it as `sorry`, and do not prove it.
  Remove its ⚠️ DANGER docstring and replace it with a plain docstring that says which facts the proof will use: the last-jump check, the RAM-address check, and the padded length from the floor, the witness length bound and the new restriction.
  Remove the DANGER comment above `JoltInstance.soundness` (`Soundness/soundness.lean:26-28`), and update the matching text in `JoltConstraints/model_review.md` ("Proofs owed", including the paragraph that says C remains assumed) and in `methods/soundness.md` ("Current top-level status").

## Part C: HostIO has no operands

Jolt now decodes `VirtualHostIO` with no operands and rejects a nonzero encoded rd (`crates/jolt-program/src/image/decode.rs:204-209,332-339`, `tracer/src/instruction/mod.rs:1352-1363`; commit `bc4bfb1f`).
Its row names no register, so no register changes; its executor still reads x10 to x13 directly (`tracer/src/instruction/virtual_host_io.rs:19-38`).

- Make the constructor operandless in both instruction types: `JoltCustomInstruction.VirtualHostIO` (`JoltConstraints/expansion_helpers.lean:24`) and `JoltISA.Instr.VirtualHostIO` (`JoltBytecode/JoltISA/Instruction.lean:150`).
  The encoded rs1 and immediate fields are ignored by Jolt's decoders, so the model has no fields for them.
- `SourceInstruction.expand` (`JoltConstraints/expansions.lean:126`) emits the operandless row.
  Remove HostIO's case from `Instr.rewriteNative` (`Instruction.lean:448-457`); keep `sideEffectingDst` for the other instructions that use it.
- Give HostIO no destination and no source in `Instr.destination?`, the metadata, register canonicality, the bytecode register selectors (`Constraints/BytecodeReadSelectors.lean`), the witness helpers (`Rs1Value`, `Rs1Ra`, `RdWa`, `rdValue`) and `ExpansionTempLiveness.readSources`.
  Keep `execHostIOWith` (`JoltBytecode/JoltISA/HostIO.lean:41`) reading x10 to x13 from the state; these are not operands.
- Delete the restriction `Rv64ProgramImage.HostCallRdZero` (`Soundness/Assumptions.lean:53`) and its field `hostCallRdZero` in `TemporaryRestrictions` (line 89), with Ari's approval given above.
  `HostCallsSucceed` (`Soundness/Layer5/HostCallRestriction.lean:33`) is a different condition and stays.
- Restate `host_call_selected_step` (`Soundness/Layer5/HostCallRegisterFrame.lean:285`) to return full `RegisterAgreement`, using `RegisterAgreement.noWrite` (`Soundness/Layer5/Registers.lean:156`), as for any row with no destination.
  Then delete what only served the old temporary-40 write: `RegisterAgreementExceptHostTemp` and its lemmas, `host_program_destination` and its helpers in `HostCallExpansion.lean`, and `hostTemp_firstAccessIsWrite` and `hostTemp_firstRow_noRead` in `expansion_temp_liveness.lean` if nothing else uses them.
  Follow `AGENTS.md`: delete every lemma no proof uses.
- Update every other pattern match on the old constructor; the audit lists them (JoltBytecode semantics and frames, `expansion_facts.lean`, `trace_interface.lean`, `nextpc_frame.lean`, the completeness register and HostIO helpers, `Layer7/TapeRebuild.lean`, `Layer7/StallSuffix.lean`).
- In `methods/soundness.md`, section "Register agreement must be over live registers": HostIO no longer writes a register.
  Say that scratch registers 40 to 47 can still differ between the witness and the honest run after a division expansion (see `methods/advice_fix_plan.md`), which is why live-register agreement is still needed.
  Change nothing else in that section.

## Before you stop (after each part)

Build `JoltBytecode` and `JoltConstraints`.
Run `#print axioms JoltInstance.soundness` and `#print axioms JoltInstance.completeness`: no new `sorryAx` may appear.
Add a section "Part 2A", "Part 2B" or "Part 2C" to `methods/pin_update_report.md` with:
- each changed or deleted declaration, with file and line, and the old and new statement where it changed;
- for each citation you changed, the old and new reference, and the Jolt lines you read to check it;
- any new or changed proof that takes more than about ten seconds;
- any new `bv_decide` (also added to the list in `JoltConstraints/model_review.md`);
- the build results and both axiom audits.

Do not commit.
Then stop until Ari tells you to continue.
