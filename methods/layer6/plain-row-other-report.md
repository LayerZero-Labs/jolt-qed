# Remaining plain rows: audit report

This pass stopped during the required audit of `methods/layer6/plain-row-other.md`, before editing Lean code.
The requested readings were completed, including Part B of `stage-4a-report.md`, `stage-6b-report.md`, and the `Proofs` section of `row-step-report.md`.
`plain_row_step_other` remains staged at `JoltConstraints/Soundness/Layer6/PlainRow.lean:1210`, with its statement and `sorry` body unchanged.
The findings below concern the plan; they are not a counterexample to the theorem.

## Incorrect description of the existing pipeline

Item 1 says that `ArithmeticExecution`, `arithmetic_execution`, `arithmetic_row_observations`, and `plain_row_ram` are written for `DivisionArithmeticRow` and should be generalized to a per-kind execution contract.
That description does not match two of the declarations.

- `ArithmeticExecution` at `PlainRow.lean:561` already takes an arbitrary `Instr` and has no `DivisionArithmeticRow` premise.
  It does specialize execution to tape answer zero at line 564, and it has no tape-answer encoding field, which matters for the planned `VirtualAdviceLoad` case.
- `plain_row_ram` at `PlainRow.lean:744` already takes `PlainRow` at line 753, not `DivisionArithmeticRow`.
  Its proof uses the absence of load/store flags and a RAM access, independently of an execution contract.

The division-specific premises are in `arithmetic_execution` at `PlainRow.lean:634` and `arithmetic_row_observations` at line 782.
The corrected plan should retain the general RAM lemma, distinguish the execution contract from the division dispatch, and generalize the contract's tape-answer portion for tape loads.

## Observation reuse and edit scope

Item 1 asks to reuse `representsRows_push_operands` instead of writing another observation proof.
That theorem exists at `JoltConstraints/Soundness/Layer6/RowStepCommon.lean:62` and supplies the general append observations described in the plan.
However, `RowStepCommon.lean:1` imports `PlainRow.lean`.
Its proof calls `representsRows_push_selected` at line 82, whose proof calls `PlainRow.lean`'s `representsRows_push` at `RowStepCommon.lean:54`.
Importing `RowStepCommon` into `PlainRow` to use that theorem would therefore create an import cycle.
Putting the new caller in another module imported by `PlainRow` would retain the same cycle.

The plan permits editing `PlainRow.lean`, new Layer 6 files, and the specified Layer 5 files; it does not permit editing the existing `RowStepCommon.lean`.
The proposed correction is to allow an import/extraction edit to `RowStepCommon.lean` as well.
The shared observation prerequisites can then move out of `PlainRow` into a lower-level module, with `RowStepCommon` importing that module and `PlainRow` importing `RowStepCommon`.
Existing theorem statements and proofs can be retained during that extraction, and the append proof can reuse `representsRows_push_operands` without duplication.
No extraction or import change was attempted under the current scope.

## Validation and remaining work

The audit stopped at item 1, following the instruction to stop and report an incorrect plan claim before implementation.
The remaining kind-by-kind claims have not been fully audited, and this report does not certify them.
No Lean declaration, statement, hypothesis, definition, proof limit, or axiom was changed.
No new `sorry` or `bv_decide` use was added, and no proof was timed.
No build or `#print axioms` command was run because no Lean code changed and the requested proof remains staged.
The only file written by this task is this report.
No protected file was edited and no commit was made.

## Implementation after the corrected plan

This pass follows the correction in `973bdd9` and Ari's authorization to move the three observation helpers and update their importers.
It completes every scalar case and stops at item 4 of the plan: the branch and VirtualAdviceLoad step modules are not committed.
At the final check, the other agent's untracked `Branch.lean` contains `branch_step`, while `AdviceLoad.lean` is absent.
Those dependencies were not imported or edited by this task.

`plain_row_step_other` now has a proof body with its original statement unchanged.
Its only remaining `sorryAx` dependencies are the two named stages `branch_plain_row_step` and `tape_plain_row_step`.
Thus the theorem is not yet fully proved.
No counterexample to the scalar cases or further blocking error in the corrected plan was found.
This pass does not certify the unfinished branch or tape-load implementations.

### Shared append and execution

`ExpansionState.selectedRow`, `representsRows_push_selected`, and `representsRows_push_operands` moved into `PlainRow.lean` with their complete declaration blocks byte-for-byte unchanged.
`RowStepCommon.lean` had no remaining declarations and was deleted.
The import lines in `RamCutAgreement.lean` and `RowStepJalr.lean` now import `PlainRow` directly.
The other agent's changes to the body of `RowStepJalr.lean` were preserved.

`ArithmeticExecution` and `plain_row_ram` are reused unchanged, including their proof or structure bodies.
The former still uses tape answer zero.
The new `append_plain_execution` accepts an explicit answer and its tape-read encoding, so the common append proof can also serve the eventual tape-load case without altering `ArithmeticExecution`.
It reuses `plain_row_ram`, the relocated `representsRows_push_operands`, `representsPrefix_push`, and `append_expansion_row`.
Both the existing division specialization and the new scalar path use this append proof.

The division-specific `arithmetic_row_observations` was removed.
`row_operand_observations` replaces it with a proof for arbitrary instructions whose explicit sources are live.
It connects `readSources` to the two existing operand selectors once, uses their canonicality lemmas and `RegisterAgreementOn.read`, and supplies the raw operand observations required by `representsRows_push_operands`.
The local `nonAdviceWrite` packer was extracted from `arithmetic_execution` into the shared `arithmeticExecution_nonAdviceWrite`; the division dispatch's statement is unchanged.

`PlainWriteKind` and `OtherScalarKind` group the remaining scalar rows by existing Layer 5 families.
Their destination/source certificate is proved once and reused in the execution dispatcher.
`otherScalarKind?` records the constructor-to-family mapping, and `other_row_classification` verifies that a remaining checked plain row is scalar, a branch, or a tape load.
The two immediate rotations are rejected using the existing `immShiftOk` fact.

The plan's porting option was used for `ImmediatePowerMask` and `XorRotation`.
Their Layer 5 rules now use live-register agreement, so their fifteen constructors need no non-reachability argument in this proof.
All 47 reachable scalar constructors listed in the stage 6b report are connected to their existing family rules.
AUIPC obtains its PC premise from `untrusted_prepared_pc` applied to the prospective row's `RawRowEntry`.
FENCE uses `fence_register_step`, extracted from `fence_step`; the original RAM-aware theorem derives its execution and register result from that helper and retains its statement.

Register shifts use `expand_program_shiftPairs` and `RawRowEntry` to identify the previous executed row and its post-state.
`run.executes` supplies the execution certificate, and the existing `fed_mask` theorem supplies the mask shape.
`maskProducer_exec` removes runtime advice and the ignored tape answer for the producer before applying that theorem.
No mask-shape premise was added to the target or to an expansion invariant.
The proof does not infer execution merely from a standalone row or post-state.

### Declaration inventory

Locations below refer to the final working-tree snapshot over `973bdd9`.
Names in the Layer 6 tables are in namespace `JoltInstance`; private helpers are marked.
Only declarations moved, added, removed, or changed by this task are listed.

| File under `JoltConstraints/Soundness/Layer6/` | Declaration and line | Change |
| --- | --- | --- |
| `PlainRow.lean` | `ExpansionState.selectedRow`, 462; `representsRows_push_selected`, 487; `representsRows_push_operands`, 512 | Moved unchanged from `RowStepCommon`. |
| `PlainRow.lean` | private `arithmeticExecution_nonAdviceWrite`, 714 | Extract the shared register-write packer. |
| `PlainRow.lean` | private `arithmetic_execution`, 733 | Reuse the extracted packer; statement unchanged. |
| `PlainRow.lean` | private `plainWrite_execution`, 820; private `otherScalar_execution`, 890 | Connect scalar families to `ArithmeticExecution`. |
| `PlainRow.lean` | former private `arithmetic_row_observations` | Removed; replaced by the general operand proof. |
| `PlainRow.lean` | private `append_plain_execution`, 1320 | Shared plain-row append and extension packaging. |
| `PlainRow.lean` | private `maskProducer_exec`, 1371; private `prepared_shift_mask`, 1384 | Recover the executed producer's mask. |
| `PlainRow.lean` | `arithmetic_plain_row_step`, 1423 | Reuse the shared append; statement unchanged. |
| `PlainRow.lean` | private `other_row_classification`, 1460 | Verify the remaining-kind classification. |
| `PlainRow.lean` | private `branch_plain_row_step`, 1475; private `tape_plain_row_step`, 1490 | The two named remaining stages, each with a whole-declaration `sorry` body. |
| `PlainRow.lean` | `plain_row_step_other`, 1509 | Proved from completed scalar cases and the two remaining stages; statement unchanged. |
| `PlainRowOperands.lean` | private `readSources_eq_operands`, 11; private `operand_value`, 16; `row_operand_observations`, 31 | General live-source observation proof. |
| `PlainRowKinds.lean` | `PlainWriteKind`, 30; `.instruction`, 51; `.destination`, 71; `.sources`, 91; `.shape`, 112; `.noTape`, 137 | Writing-family descriptions and shared certificates. |
| `PlainRowKinds.lean` | `OtherScalarKind`, 160; `.instruction`, 169; `.noTape`, 177; `otherScalarKind?`, 189 | Scalar families and the constructor mapping. |

The Layer 5 changes are in namespace `JoltConstraints.Soundness`.

| File under `JoltConstraints/Soundness/Layer5/` | Declaration and line | Statement or proof change |
| --- | --- | --- |
| `ImmediatePowerMask.lean` | `immediatePowerMask_step`, 141 | Replace full agreement with `RegisterAgreementOn live`; return agreement on `live` plus the destination. |
| `XorRotation.lean` | private `xorRotation_write_value`, 89; `xorRotation_step`, 127 | Use live agreement and require both sources live; the step returns agreement on `live` plus the destination. |
| `Fence.lean` | `fence_register_step`, 31 | Extract execution and live-register preservation without the unused RAM premise. |
| `Fence.lean` | `fence_step`, 47 | Reuse the extraction; original statement unchanged. |

The Layer 5 liveness premises come from `expansion_sources_live` at the caller.
The two remaining stages specialize the target to a branch or tape-load kind; their callers prove those kind premises using the classification and exact selected-row identity.
No premise was added to `plain_row_step_other`, and no language, restriction, core definition, or approved expansion invariant changed.
No proved declaration was replaced with `sorry`.

### Validation and stopping point

`lake build JoltConstraints.Soundness.Layer6.RowStep` passed with 8,730 jobs.
It built `PlainRow` in about 9.0 seconds and `RowStep` in about 4.5 seconds, including the concurrent JAL/JALR/HostIO work.
The Layer 5 ports and both new support modules also built successfully.
The full `JoltConstraints` target was not run.
The final build log is `/private/tmp/plain-row-other-rowstep-build.log`.

`#print axioms JoltInstance.plain_row_step_other` reports `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`.
A recursive dependency audit asserts that its only declarations directly using `sorryAx` are exactly `branch_plain_row_step` and `tape_plain_row_step`.
The same audit finds no reachable `sorryAx` in `arithmetic_plain_row_step`, `representsRows_push_operands`, `row_operand_observations`, `immediatePowerMask_step`, `xorRotation_step`, `fence_step`, or `fence_register_step`.
The audit source and output are `/private/tmp/plain-row-other-axioms.lean` and `/private/tmp/plain-row-other-axioms.log`.

Statement comparisons passed for the target, `arithmetic_plain_row_step`, `arithmetic_execution`, and `fence_step`.
Exact full-declaration comparisons passed for `ArithmeticExecution`, `plain_row_ram`, and the three relocated declarations.
Whitespace checks passed for the edited files and both new modules.

No measured proof exceeded ten seconds.
The final `PlainRow` profile's slowest proof is the unchanged `trace_push_observations`, at about 1.21 seconds.
The new classification takes about 0.61 seconds, and the target proof takes about 0.35 seconds.
The profile is `/private/tmp/plain-row-other-profile.log`.
All new proof bodies are under about sixty lines; the existing division dispatch retains its earlier family cases.
There are no new `bv_decide`, `native_decide`, `decide +kernel`, or axiom declarations, and no proof limits were raised.

This task edited `PlainRow.lean`, the two new Layer 6 support files, the three Layer 5 files in the table, the authorized import lines, and this report, and deleted the emptied `RowStepCommon.lean`.
Concurrent changes elsewhere, including visibility changes in `PlainRow.lean` made by another agent, are not attributed to this task.
No commit was made.
Work stops at the plan's branch/tape dependency boundary.

## Branch and tape re-audit: execution-helper destination gap

This pass stops before implementation under Ari's instruction to report incorrect plan claims.
The proposed reuse in item 3 needs an additional destination-shape fact or a generalization outside the plan's visibility-only permission for `AdviceExpansion.lean`.
No counterexample to `branch_plain_row_step`, `tape_plain_row_step`, or an actual source expansion was found.

### Exact gap and checked case

`JoltConstraints.Soundness.adviceLoad_step` at `JoltConstraints/Soundness/Layer5/AdviceExpansion.lean:67` takes an architectural `rd : regidx` and executes only `.VirtualAdviceLoad (sideEffectingRdZeroDst rd) byteCount`.
`JoltISA.sideEffectingRdZeroDst` at `JoltBytecode/JoltISA/Instruction.lean:388` produces a nonzero architectural destination or virtual register 40.
It does not cover arbitrary canonical virtual destinations.

In contrast, the selected tape row in `JoltInstance.tape_plain_row_step` at `JoltConstraints/Soundness/Layer6/PlainRow.lean:1490` supplies an arbitrary `destination : Dst`.
Applying the proposed execution helper requires the additional fact `∃ rd, destination = sideEffectingRdZeroDst rd`.
Neither canonicality nor `advicePairsOk` supplies this fact for full-width loads.
Adding only the planned byte-count condition does not supply it either.

The kernel-checked reproducer `/private/tmp/plain-row-tape-destination-audit.lean` establishes:

```lean
ExpansionFacts.nativeRowOk (.VirtualAdviceLoad (.vreg 41) 8) = true
ExpansionFacts.sequenceOk [.VirtualAdviceLoad (.vreg 41) 8] = true
¬ ∃ rd, Dst.vreg 41 = sideEffectingRdZeroDst rd
```

The accepted row already has a valid byte count, so the proposed width conjunct leaves this case accepted.
The last proof splits only on the x0 rewrite condition, without enumerating registers or instruction kinds.
This refutes deriving the required destination shape from the checker facts; it does not claim that an actual source expansion emits this row.
The existing narrow-load shape extraction at `JoltConstraints/Soundness/Layer7/TapeRebuild.lean:969` requires `width.toNat < 8`, so it does not resolve the eight-byte case.
The same reproducer verifies the already documented acceptance of `.VirtualAdviceLoad (.xreg (.Regidx 1)) 9` by both checkers.

The pinned Jolt sources confirm the intended tape behavior.
At `5def437f`, `jolt/tracer/src/instruction/virtual_advice_load.rs` (`VirtualAdviceLoad::exec`) checks byte counts 1, 2, 4 or 8 and writes the read word to the destination.
`jolt/crates/jolt-riscv/src/instructions/virt/advice_load.rs` assigns `Advice` and `WriteLookupOutputToRD`, and `jolt/crates/jolt-lookup-tables/src/instructions/virt/advice_load.rs` assigns the `RangeCheck` lookup.
`jolt/crates/jolt-program/src/expand/memory/shared.rs` (`expand_advice_load`) emits the source destination, with extra arithmetic rows for narrow loads.
The Lean `adviceldProgramAuto` at `JoltBytecode/JoltISA/ExpansionsAutomated.lean:1193` uses only the rewritten source destinations, so a stronger expansion fact is plausible but is not supplied by the proposed checker argument.

### Proposed correction for review

Generalize `adviceLoad_step` in place to a canonical `destination : Dst`, retaining the same valid-width premise.
Its execution conclusion would be:

```lean
execWithTapeAnswer (.VirtualAdviceLoad destination byteCount) answer pre =
  .ok RETIRE_SUCCESS
    (afterWriteDst destination answer
      { pre with adviceTape :=
          { pre.adviceTape with
              readPosition := pre.adviceTape.readPosition + byteCount.toNat } })
```

The new local premise would be `JoltRegisterEncoding.destinationIsCanonical destination = true`, which the selected-row caller can prove from its existing row canonicality.
`writeDst_afterWriteDst` at `JoltConstraints/Soundness/Layer5/RegisterWrite.lean:37` already supplies the general successful write, so this avoids a destination-reachability proof and a duplicate execution proof.
Update the existing caller `narrowAdviceProgram_exec` at `AdviceExpansion.lean:96` to specialize the general helper to `sideEffectingRdZeroDst rd`, preserving that caller's statement.
This is a proposed helper statement change, not an implemented change or an added assumption of soundness.
It requires expanding the plan's permission beyond visibility changes in `AdviceExpansion.lean`.

### Validation and unchanged work

`lake build JoltConstraints` passed with 8,826 jobs; the log is `/private/tmp/plain-row-branch-tape-audit-build.log`.
`lake env lean /private/tmp/plain-row-tape-destination-audit.lean` passed.
Its `#print axioms JoltInstance.plain_row_step_other` still reports `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`.
Both named stages, `branch_plain_row_step` at `PlainRow.lean:1475` and `tape_plain_row_step` at `PlainRow.lean:1490`, remain unchanged with `sorry` bodies.
The byte-count checker change and new `AdviceLoad.lean` are not implemented.

Only this report was edited in the repository by this pass.
No declarations, hypotheses, definitions, `bv_decide` uses, proof limits, or commits were added or changed.
There are no new repository proofs to profile; the baseline build does not establish fresh per-proof timings.
The other agent's division files and concurrent report changes were left untouched.

## Completion after the tape-load correction

This pass follows Ari's correction to item 3 and completes `branch_plain_row_step` and `tape_plain_row_step` with their staged statements unchanged.
`#print axioms JoltInstance.plain_row_step_other` now reports only `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
No further incorrect claim or false staged statement was found in the corrected plan.

### Implementation and source checks

The branch case applies `branch_step` and `append_plain_execution`.
`rawEntry_state` extracts the existing raw-entry decomposition once: the prepared state is the run's final state or its `advance_pc` preparation.
Both `rawEntry_prepared` and the branch's compressed-instruction premise use this decomposition.
Both `UntrustedAnswerRun.final_compressed_enabled` and `prepared_compressed_enabled` are used, so neither is deleted and `Branch.lean` is unchanged.
A branch has no destination, so its `rowLive` predicate reduces to the previous live set.
The branch memory/device frame uses `StatePreservation.Preserves`, `preservation_auto`, read purity and `jump_to_shape`, after classification by the existing six-branch lemma.
It uses an execution certificate and does not infer behavior from a standalone post-state.

`advicePairsOk` now requires each tape-load byte count to be 1, 2, 4 or 8.
The existing native and sequence checkers include it, and all existing `expand_ok` proofs compile with the stronger check.
`advicePairsOk_width` extracts the width for any member of a checked instruction list.
`expanded_adviceLoad_width` lifts that fact through `expand_instruction_property` and `expand_program_source_of_row`, without a per-source proof or a destination-shape condition.
`advicePairsOk_head` in tape reconstruction now projects the existing narrow-pair condition past the new width conjunct.

`rangeCheck_write_value` is the single shared derivation of the witness's 64-bit written word from a selected range-check lookup and the write-lookup-output flag.
Both `advice_step` and the new `adviceLoad_register_step` use it.
The tape step takes any destination and derives its canonicality from the selected bytecode row.
It advances `adviceTape.readPosition` before writing, transports register agreement to that state using the unchanged `sail` and `vregs`, and applies `writeDst_afterWriteDst` and `RegisterAgreementOn.write` there.
It does not apply `registerWriteOn_step` or reuse `AdviceExpansion.adviceLoad_step`.
The destination write and tape-cursor update preserve memory and `jolt_device`, supplying the shared append premises.
`AdviceExpansion.lean` remains unchanged.

The pinned checks at `5def437f` included Jolt's tracer `BEQ::exec` in `jolt/tracer/src/instruction/beq.rs`, which conditionally updates PC without a register write.
Jolt's tracer `VirtualAdviceLoad::exec`, the advice-load lookup implementation, and `expand_advice_load` were checked in the preceding audit and agree with the corrected construction.
This pass also checked `RangeCheckTable::materialize_entry` in `jolt/crates/jolt-lookup-tables/src/tables/range_check.rs` and the VirtualAdvice flags in `jolt/crates/jolt-riscv/src/instructions/virt/advice.rs`.
The shared lookup returns the low 64-bit word and both advice instructions carry `WriteLookupOutputToRD`.

### Declaration inventory and statement changes

Locations refer to this working-tree snapshot.
The Layer 5 declarations are in `JoltConstraints.Soundness`, the Layer 6 declarations are in `JoltInstance`, and the checker declarations are in `ExpansionFacts`.

| File | Declaration and line | Change |
| --- | --- | --- |
| `JoltConstraints/expansion_facts.lean` | `advicePairsOk`, 138; `advicePairsOk_width`, 164 | Add the authorized byte-count check and derive member widths. |
| `JoltConstraints/Soundness/Layer5/Advice.lean` | `rangeCheck_write_value`, 22; `advice_step`, 57 | Extract the shared value proof; retain the original step statement. |
| `JoltConstraints/Soundness/Layer5/AdviceLoad.lean` | `expanded_adviceLoad_width`, 19; `adviceLoad_register_step`, 48 | New bytecode-only width lift and selected tape-load step. |
| `JoltConstraints/Soundness/Layer6/PlainRow.lean` | private `rawEntry_state`, 1048; `rawEntry_prepared`, 1070 | Extract the shared state decomposition; retain the original preparation statement. |
| Same file | private `branch_plain_metadata`, 1486; private `branch_execution_frame`, 1493 | Branch destination/advice metadata and memory/device preservation. |
| Same file | private `branch_plain_row_step`, 1528; private `tape_plain_row_step`, 1574 | Replace both whole-declaration `sorry` bodies with proofs. |
| Same file | `plain_row_step_other`, 1616 | Update its docstring; statement and proof body are unchanged and now have no admitted dependency. |
| `JoltConstraints/Soundness/Layer7/TapeRebuild.lean` | private `advicePairsOk_head`, 969 | Adjust the pair-condition projection; statement unchanged. |

Exact statement comparisons passed for `advice_step`, `rawEntry_prepared`, both completed stages, `plain_row_step_other`, and `advicePairsOk_head`.
No hypothesis was added to any existing theorem.
The new shared value lemma takes the local range-check table and write-flag equalities, both proved by its callers from their instruction identities.
The new tape step derives width and destination canonicality internally; neither is a new soundness premise.
The only changed definition is the authorized proof checker `advicePairsOk`; the language, semantics, restrictions and expansion invariant are unchanged.
`JoltConstraints.lean` and `PlainRow.lean` import `AdviceLoad`, and `PlainRow.lean` also imports the existing branch step.
The plain-row status was updated in `methods/soundness.md` and removed from the outstanding-gap table in `JoltConstraints/model_review.md`.

### Validation and remaining build limitation

The kernel-checked audit `/private/tmp/plain-row-complete-audit.lean` passes; its output is `/private/tmp/plain-row-complete-audit.log`.
It checks that native and sequence entry points reject a nine-byte load, that a three-byte load fails even with a matching following multiply, and that both entry points still accept an eight-byte load into virtual register 41.
The same audit prints axioms for the two width lemmas, the shared range-check lemma, both Layer 5 advice steps and `plain_row_step_other`; none reaches `sorryAx`.
`lake env lean JoltConstraints/Soundness/Layer6/PlainRow.lean` passes, and the full-build attempt successfully built `PlainRow`, `RowStep`, `AdviceLoad` and `TapeRebuild`.
The explicit targeted build `lake build JoltConstraints.Soundness.Layer6.RowStep JoltConstraints.Soundness.Layer7.TapeRebuild` passes with 8,739 jobs; its log is `/private/tmp/plain-row-complete-targeted-build.log`.

`lake build JoltConstraints` was attempted, but the aggregate target does not currently pass because the other agent's `DivisionLayout.lean:46:12` reaches the recursion-depth limit in `simp`.
An earlier attempt also reported unknown `Encoded.VirtualShiftDataB/H/W` names in that file; the other agent removed those names before the final retry.
The final aggregate log is `/private/tmp/plain-row-complete-build-final.log`; the earlier log is `/private/tmp/plain-row-complete-build.log`.
No division file or proof limit was edited to work around that failure.

Every new or changed proof body is under sixty lines; the longest new proof is the 33-line branch append.
Profiling all five changed Lean modules with `-j1 -Dtrace.profiler=true -Dtrace.profiler.threshold=1000` found no proof exceeding ten seconds.
The slowest profiled proof was the existing checker theorem `ExpansionFacts.csrrs_ok`, at about 7.52 seconds; all new proofs were below the one-second reporting threshold.
The profile logs are `/private/tmp/plain-row-complete-profile.log`, `/private/tmp/plain-row-advice-profile.log`, `/private/tmp/plain-row-advice-load-profile.log`, `/private/tmp/plain-row-checker-profile.log`, and `/private/tmp/plain-row-tape-rebuild-profile.log`.
No new `sorry`, `bv_decide`, `native_decide`, `decide +kernel`, axiom declaration or proof-limit setting was introduced.
No commit was made.
