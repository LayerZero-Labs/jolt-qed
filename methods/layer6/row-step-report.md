# Row-step staging: stopped during the plan audit

The audit stopped before any Lean edits or staged declarations.
The JAL recipe in `methods/layer6/row-step.md:23` incorrectly treats facts about an already executed run row as supplying the prepared-state facts needed to execute the next row.
This is a gap in the proposed application of the lemmas, not a counterexample to `row_step`.

## The incorrect application

The plan says that `untrusted_row_pc` and `untrusted_row_next_pc` give the PC and prepared `nextPC` needed by `jal_step`.
Their actual statements in `JoltConstraints/Soundness/Layer7/StallSuffix.lean:971` and `JoltConstraints/Soundness/Layer7/StallSuffix.lean:1053` both require `i : Fin run.rows.size`.
Their conclusions concern `run.rows[i].preState`, so the row must already belong to the certified execution.

In contrast, `ExpansionState.next` in `JoltConstraints/Soundness/Layer6/PrefixState.lean:142` supplies a bytecode index `next`, a prepared state `pre`, witness selection, and the entry/linkage condition for a row that has not yet been appended.
It does not supply an existing run-row index for that state.
In particular, the next trace position is `run.rows.size`, which cannot inhabit `Fin run.rows.size`.
At the empty prefix there is no existing run-row index at all.

Applying the two cited lemmas to an extended run would be circular in this execution construction.
`appendUntrustedRow` in `JoltConstraints/Soundness/Layer6/PlainRow.lean:338` requires the new row's successful `execWithTapeAnswer` execution as an input.
`jal_step` in `JoltConstraints/Soundness/Layer5/Jal.lean:95` is intended to supply that execution, but first requires the PC and prepared `nextPC` facts at lines 108–110.

## Missing fact and proposed correction

The missing adapter should derive PC preparation for a prospective row from `RawRowEntry run next pre`, defined in `JoltConstraints/Soundness/Layer6/PlainRow.lean:808`, using the existing prefix's execution certificate.
Its intended conclusions are:

```lean
pre.sail.regs.get? Register.PC = some run.bytecode[next].address
pre.sail.regs.get? Register.nextPC =
  some (run.bytecode[next].address +
    if source_is_compressed run.bytecode next then 2 else 4)
```

These facts must be proved before constructing the appended execution, without assuming the new row already runs.
At a source boundary the entry condition provides `advance_pc` directly.
For an interior row the argument must use the previous executed row, its execution frame, and the bytecode layout.
The subsequent JAL application also needs the terminal-row relation between `source_is_compressed` and `row.is_compressed`, together with the existing no-wrap assumption.
This is a proposed correction for review; no such lemma was staged or proved during this task.

There is a separate interface adaptation to record in a corrected plan: `jal_step` requires full `RegisterAgreement`, whereas `ExpansionState.registers` supplies `RegisterAgreementOn (ExpansionLive ...)`.
`host_call_selected_step` in `JoltConstraints/Soundness/Layer5/HostCallRegisterFrame.lean:30` likewise requires full agreement and a following witness cycle.
The staged steps must obtain suitable live-register versions or reuse the narrower underlying execution facts; they cannot simply add full agreement as a new hypothesis.
These interface differences do not by themselves establish that the proposed steps are false.

## Scope and validation

Read `AGENTS.md`, `methods/layer6/reuse.md`, Part B of `methods/layer6/stage-4a-report.md`, `methods/layer6/device-memory-report.md`, and the row-step plan, and inspected the relevant declarations.
The audit stopped on the JAL application above, as the task requires when a plan claim is wrong.
No complete approval of the remaining staging plan is claimed.

Only this report was added by this task.
`JoltInstance.row_step` in `JoltConstraints/Soundness/Layer6/RowStep.lean:15` remains unchanged, including its existing `sorry`.
No per-kind steps were staged or proved.
No existing statement, definition, hypothesis, proof limit, or axiom was changed.
There are no new `bv_decide` uses and no new proof timings to report.
The module build and `#print axioms` were not run after this audit failure because implementation stopped before any Lean changes.
The other agents' files were not edited, and no commit was made.

## Resumed staging after the corrected plan

This section records the completed staging after Ari authorized the prepared-state extraction and Claude corrected the plan.
It supersedes the stopped status above; the first audit is retained as history.
`JoltInstance.row_step` is now proved from the existing plain-row rule and seven new staged steps.
The seven steps remain `sorry` and have not been proved.

### Re-audit and preparation

The corrected PC argument checks against the execution and linkage code.
The extracted induction proves PC and nextPC together for a prospective state after any prefix of an existing run, including the entire run.
It executes only the already retained predecessor when using `tape_row_preserves_pc` and `ordinary_tape_next_pc`.
`BytecodeLayout.next` and `source_compressed_next` transport its source address and compression flag to the prospective row.
At a source boundary, the entry clause supplies `advance_pc` directly.
Neither the extracted lemma nor its Layer 6 wrapper assumes execution of the prospective row.

The internal prefix lemma omits the no-stall conjunct because the old run-row theorems apply even to runs that contain earlier stalls.
The public whole-prefix form accepts the full entry clause, including that conjunct, and the Layer 6 wrapper is a one-line application.
The two old run-row theorems are projections of the same extracted prefix lemma and retain their exact statements.
`StallSuffix.lean` does not import or mention the `RawRowEntry` definition in a theorem type.

`PlainRow` excludes exactly LD, SD, VirtualHostIO, JAL and JALR.
`ExpansionRows.RowOk.ends` proves that HostIO and both jump kinds cannot be nonterminal rows of their source expansion.
An unfinished block can nevertheless select its terminal row: `done < count` permits `done + 1 = count`.
For example, a singleton JAL is selected with `done = 0`, and ECALL's final JALR is selected after its setup rows.
The JAL, JALR and HostIO stages therefore require the terminal equation, which their caller proves from layout.
LD and SD have both ordinary-RAM and below-RAM cases; the caller splits on the actual prepared state's effective address.

The pinned checks included `jolt/crates/jolt-program/src/expand/metadata.rs` (`stamp_sequence_metadata`) and `jolt/crates/jolt-program/src/expand/control_flow/ecall.rs` (`expand_ecall`) at `5def437f`.
The sequence stamp puts compression only on the final row, and ECALL ends with a JALR to the virtual mtvec register.
The extracted preparation fact uses `source_is_compressed`, not an interior row's `is_compressed`.
The later JAL proof must use `source_compressed_of_last` and the existing `assumptions.pcNoWrap` before applying its field-valued link equation.
No address uniqueness assumption is inferred from a source address: the dispatcher identifies the row by `first.val + done` and bytecode equality from the two expansion certificates.

### Shared append contract

`PlainRowExtension` at `JoltConstraints/Soundness/Layer6/PlainRow.lean:1108` already has no plain-row hypothesis, so its definition is unchanged and all seven stages return it.
The restrictive part was the append constructor's zero-RAM-address premise.
`append_expansion_row_of_termination` extracts that constructor with an explicit conditional termination-table obligation for the appended trace.
That obligation applies only if no retained or newly appended row stores to termination, so it does not incorrectly require zero after a termination store.
The old `append_expansion_row` keeps its statement and derives the obligation from `ramVal_succ_of_address_zero` and the old invariant.
There is one shared state-construction proof, rather than separate memory and plain append proofs.

### Staged statements and their remaining work

All seven declarations are in `JoltConstraints/Soundness/Layer6/RowStepKinds.lean` and return `PlainRowExtension witness context run first done bound`.
Their common inputs are the field bound, existing assumptions and restrictions, constraint equations, certified run, `ExpansionState`, unfinished bound, honest prefix advice, selected row index, `RawRowEntry`, and `RegisterAgreementOn (ExpansionLive ...)` at its prepared state.
The index, entry, trace bound and prepared register agreement are established by the caller; full `RegisterAgreement` is never assumed.
The jump stages additionally receive the prepared PC and nextPC facts, and all three terminal kinds receive the terminal equation proved by the caller.
No premise was added to `row_step` or to any existing theorem.

| Declaration and line | Case and reason for expecting a proof | Existing facts and work left for the proving stage |
| --- | --- | --- |
| `ld_ram_row_step`, line 89 | LD at or above `RAM_START_ADDRESS`; the checked load reads the ordinary RAM word already represented at the cut. | Port `ld_ram_step` to live agreement, obtain base liveness with `expansion_sources_live`, recover ordinary RAM agreement from the cut, and supply row observations and termination preservation to the shared append constructor. |
| `ld_device_row_step`, line 99 | LD below RAM; the existing device rule relates the device read and destination write to the witness. | Use `ld_device_step`, the existing tracer restrictions, live base, and cut RAM/device/termination agreements; assemble observations and the returned invariant. |
| `sd_ram_row_step`, line 109 | SD at or above `RAM_START_ADDRESS`; interpreter memory and the selected witness word receive the same store value. | Port `sd_ram_step_agreement` to live base/source agreement, obtain both source-liveness facts, and preserve the device and conditional termination portions of the cut. |
| `sd_device_row_step`, line 120 | SD below RAM; the existing device rule updates the device and witness image together, with a conditional termination obligation. | Use `sd_device_step`, the existing restrictions and live source facts, then pass its memory result to the generalized append constructor. |
| `host_row_step`, line 130 | Terminal VirtualHostIO; the existing `HostCallsSucceed` restriction supplies execution and the host-call frames preserve registers. | Reuse `host_call_exec_sail_frame` and port the register part of `host_call_selected_step` to live agreement; handle its next-cycle requirement within the proof instead of assuming a following cycle in this stage. |
| `jal_row_step`, line 147 | Terminal JAL; preparation is proved before execution, and no-wrap comes from the existing assumptions. | Port `jal_step` to live agreement, use `source_compressed_of_last`, and supply zero-RAM observations and the append invariant. |
| `jalr_row_step`, line 157 | Terminal JALR; its base is live by the exact expansion's source-read certificate, including virtual-register bases such as ECALL's mtvec. | No Layer 5 step exists yet; use `selected_jalr_lookup_target`, `selected_jalr_next_target`, `selected_jump_link_write_value`, and the interpreter semantics to establish the execution and live-register update. |

These are staging justifications, not completed proofs of the local execution rules.
In particular, the RAM, JAL and HostIO ports from full to live agreement remain work for the next approved stage.
The device rules already accept live agreement; their current downstream device-region obligations remain outside this task.

### Proved and extracted declarations

All names below are in namespace `JoltInstance`; private declarations are marked explicitly.
Every new helper is used by the resulting proof graph.

| File | Declaration and line | Change |
| --- | --- | --- |
| `JoltConstraints/Soundness/Layer7/StallSuffix.lean` | private `source_compressed_next`, 971 | Existing statement and proof retained before the shared extraction. |
| Same file | private `prefix_back_succ`, 1000 | Identifies the last row of an array prefix. |
| Same file | private `untrusted_entry_at`, 1006 | Derives an existing row's entry clause at its preceding prefix. |
| Same file | private `prepared_pc_link`, 1028 | Extracts the shared predecessor-execution and source-boundary argument. |
| Same file | private `untrusted_prepared_pc_at`, 1065 | One induction proves both prepared PC facts at an arbitrary prefix cut. |
| Same file | `untrusted_prepared_pc`, 1103 | Public whole-prefix form with the entry/linkage clause written out. |
| Same file | `untrusted_row_pc`, 1138; `untrusted_row_next_pc`, 1152 | Existing statements derived from the shared prefix lemma. |
| `JoltConstraints/Soundness/Layer6/PlainRow.lean` | `rawEntry_prepared`, 864 | Made public in place; statement and proof unchanged. |
| Same file | private `append_interior_next`, 889 | Extracts next-row selection and entry preparation after a nonterminal append. |
| Same file | private `real_push`, 922 | Extracts preservation of non-padding status under one append. |
| Same file | `append_expansion_row_of_termination`, 941 | General append constructor parameterized by conditional termination preservation. |
| Same file | private `append_expansion_row`, 1033 | Original statement derived from the general constructor. |
| `JoltConstraints/Soundness/Layer6/RowStepKinds.lean` | `RawRowEntry.prepared_pc`, 15 | One-line Layer 6 wrapper for the prepared-state theorem. |
| Same file | `row_kind`, 26 | Single classification into plain rows and the five exclusions. |
| Same file | `expansion_nonordinary_terminal`, 47 | Layout and countdown proof of the terminal equation. |
| `JoltConstraints/Soundness/Layer6/RowStep.lean` | `honestAdvice_push`, 18 | Earlier honest advice is unchanged by extraction stability; the new row's advice is none by `runtimeAdvice_agrees_of_noAdvice`. |
| Same file | private `row_extension`, 37 | Dispatches once on the small classification and supplies every staged premise. |
| Same file | `row_step`, 92 | Proved with its original statement; `noAdvice` supplies the new row's absent-advice fact. |

The longest new or rewritten proof body is the shared append constructor at 55 lines; the dispatcher is 38 lines and `row_step` is 17 lines.
No existing proved fact was replaced by `sorry`.
`PlainRowExtension`, `RawRowEntry`, `ExpansionState`, all model definitions, assumptions and restrictions are unchanged.
An exact source-signature comparison also confirmed unchanged statements for `row_step`, both old PC theorems, `rawEntry_prepared`, `append_expansion_row`, `arithmetic_plain_row_step`, `plain_row_step_other`, and `plain_row_step`.

### Validation and axiom audit

`lake build JoltConstraints.Soundness.Layer6.RowStep` passed, including the edited `StallSuffix` and `PlainRow` modules and the new `RowStepKinds` module.
The final target build completed successfully with 8679 jobs; the final `RowStep` compilation took about 4.6 seconds.
The full repository target was not required or run.
`git diff --check` passed for the edited existing Lean files.

`#print axioms JoltInstance.row_step` reports exactly:

```text
[propext, sorryAx, sys_enable_experimental_extensions, Classical.choice, Quot.sound]
```

A recursive dependency audit found exactly these eight reachable declarations that directly use `sorryAx`:

```text
JoltInstance.ld_ram_row_step
JoltInstance.ld_device_row_step
JoltInstance.sd_ram_row_step
JoltInstance.sd_device_row_step
JoltInstance.host_row_step
JoltInstance.jal_row_step
JoltInstance.jalr_row_step
JoltInstance.plain_row_step_other
```

`plain_row_step_other` is the pre-existing staged gap at `JoltConstraints/Soundness/Layer6/PlainRow.lean:1199`.
`row_step` has no direct `sorryAx` use.
The audit separately confirmed that the prepared-state theorem, both existing PC theorems, the generalized append constructor, the RawRowEntry wrapper, the terminal-position lemma and the advice-append lemma have no reachable `sorryAx` dependency.
The audit script is `/private/tmp/row-step-axioms.lean`, with output in `/private/tmp/row-step-axioms.log`.

Profiling all four affected Lean modules with `lake env lean -j1 -Dtrace.Elab.async=true -Dtrace.Elab.command=true -Dtrace.profiler=true -Dtrace.profiler.threshold=1000` completed successfully.
No profiled proof exceeded ten seconds.
Among the changed proofs, the generalized append constructor took about 0.46 seconds, the dispatcher 0.32 seconds, and `row_step` 0.31 seconds.
The logs are `/private/tmp/row-step-stall-profile.log`, `/private/tmp/row-step-plain-profile.log`, `/private/tmp/row-step-kinds-profile.log`, and `/private/tmp/row-step-profile.log`.
There are no new `bv_decide`, `native_decide`, `decide +kernel`, or axiom declarations, and no proof limits were raised.

Only `RowStep.lean`, the new `RowStepKinds.lean`, the permitted extractions/publicization in `PlainRow.lean`, the PC extraction in `StallSuffix.lean`, and this report were edited by this task.
The other agents' files were not edited, and no commit was made.
Work stops here for review of the seven staged steps.

## Proofs

The resumed proving pass completed `jalr_row_step`, `ld_ram_row_step`, `sd_ram_row_step`, `ld_device_row_step`, and `sd_device_row_step` with their staged statements unchanged.
All five have no reachable `sorryAx` dependency.
Ari authorized publicizing the five shared helpers after the first pass stopped at the edit-scope boundary.
The Layer 5 `jalr_step` from that first pass is committed in `ea2e553`; this resumed pass made no commit.
No false staged statement or counterexample was found during the re-audit or the proofs.

### JALR and the shared append

`append_jalr_row` at `JoltConstraints/Soundness/Layer6/RowStepJalr.lean:13` connects the committed Layer 5 execution lemma to the shared append constructor.
It obtains the selected slot from `ExpansionState.next`, base liveness from `expansion_sources_live`, and canonical register encodings from the checked bytecode row.
The row's `RowOk.ends` fact supplies its zero countdown, `source_compressed_of_last` converts the prepared nextPC flag, and `terminal_link_no_wrap` uses the existing `assumptions.pcNoWrap`.
The interpreter reads the old base before writing the link, including aliased operands and virtual bases such as ECALL's mtvec.
The pinned execution check was `jolt/tracer/src/instruction/jalr.rs` (`JALR::exec`) at `5def437f`.

The local JALR execution and append do not assume a following witness cycle.
`selected_jalr_next_target` requires a following real cycle, so it is not applied unconditionally.
The terminal append invariant has no interior-next obligation, and this proof uses the interpreter's actual computed target without adding a target-equation premise.
The zero RAM address, unchanged memory/device, register update, row observations and conditional termination invariant are passed to the existing shared append proofs.
The staged `pc` and `terminal` premises remain in `jalr_row_step`'s statement even though the stronger implementation does not need them as separate inputs.

The following helpers were made public in place, each with a docstring.
An exact source comparison confirmed that every statement and proof below is unchanged.

| File | Declaration and line |
| --- | --- |
| `JoltConstraints/Soundness/Layer6/PlainRow.lean` | `expansionLive_after`, 288 |
| Same file | `representsRows_push`, 415 |
| Same file | `representsPrefix_push`, 478 |
| Same file | `append_expansion_row`, 1044 |
| `JoltConstraints/Soundness/Layer5/RamInitialization.lean` | `overlayRamBytes_below_word`, 90 |

### RAM agreement and the memory steps

`ramAgreement_iff` at `JoltConstraints/Soundness/Layer6/RamCutAgreement.lean:86` proves once that an initialized run's image agreement outside termination is equivalent to ordinary-RAM agreement at its final state together with `DeviceRamAgreement`.
It applies to any table column, so the same fact handles both the next `RamVal` column and `RamValFinal`.
`finalRamWord_ordinary` proves the required image identity from the generated layout, validated input size, retained advice/input buffers, and bounded final output buffer.
It reuses `UntrustedAnswerRun.final_device_same`, `UntrustedAnswerRun.final_outputs_fit_layout`, the existing layout facts and the newly public overlay lemma.
The proof also excludes the panic and termination flag overlays from ordinary RAM.
It does not assert the identity for an arbitrary trace lacking initialization and execution certificates.

`ExpansionState.memoryAt` uses the reverse direction to recover both agreements before execution, transporting ordinary RAM through `RawRowEntry`'s memory frame.
`ordinary_memory_step` proves once that an access in ordinary RAM has no table effect on device words, preserves their image, and keeps termination zero when there was no earlier termination store.
The load/store rules supply the ordinary-RAM update; the shared proof handles the device and termination portions.
For device accesses, the existing `ld_device_step` and `sd_device_step` supply their corresponding memory contracts.
Their current proofs built successfully during this task and were not edited.

`append_memory_row` constructs a certified appended run before using the common RAM bridge, so the final-image frame facts do not assume the expansion invariant being constructed.
It combines the ordinary and device agreements at either cut, then applies `append_expansion_row_of_termination`.
The termination obligation is conditional on the absence of an SD touching termination anywhere in the appended prefix.
The generic `exists_fin_push` fact separates old rows from the new row without duplicating the append proof.
`memory_step_mono` lets the ordinary-RAM rules include the newly appended row in that conditional store event.

`load_row_execution` and `store_row_execution` split once on whether the actual effective address is in ordinary RAM and normalize the two Layer 5 results to a shared contract.
`append_ld_row` and `append_sd_row` then prove the respective extension without an address-region hypothesis.
Consequently the RAM and device stages for each instruction are applications of the same family theorem; their original region hypotheses are retained unchanged.
All four stages use `ramAgreement_iff` through the common append proof.
The pinned instruction checks were `jolt/tracer/src/instruction/ld.rs` (`LD::exec`) and `jolt/tracer/src/instruction/sd.rs` (`SD::exec`) at `5def437f`.

### Statement changes and proof-support declarations

The only existing theorem statement changes are the authorized Layer 5 live-register ports and the private helper needed by them.
No assumption or restriction of the program, core definition, or Layer 6 staged statement was changed.

| File | Declaration and line | Authorized interface change |
| --- | --- | --- |
| `JoltConstraints/Soundness/Layer5/LoadDoubleword.lean` | `ld_ram_step`, 39 | Replace full agreement by `RegisterAgreementOn live`; add base liveness; return agreement on `live` plus the destination. |
| `JoltConstraints/Soundness/Layer5/StoreDoubleword.lean` | private `sd_write_value`, 48 | Replace full agreement by live agreement and require source liveness. |
| Same file | `sd_ram_step`, 69 | Replace full agreement by live agreement; require base and source liveness; preserve the same live set. |
| `JoltConstraints/Soundness/Layer5/RamStoreAgreement.lean` | `sd_ram_step_agreement`, 20 | Port its input and output agreement in the same way as `sd_ram_step`, passing both liveness facts to that rule. |

The callers prove all added liveness premises from the existing expansion source-read certificate.
The execution, RAM-value, memory-update, checked-address and final-column portions of these statements are unchanged.
No full-agreement wrapper was retained because no remaining caller needs one.

All new declarations below are in namespace `JoltInstance`; private helpers are marked.
Every new helper is used by the five completed proof dependencies.

| File under `JoltConstraints/Soundness/Layer6/` | Declaration and line | Role |
| --- | --- | --- |
| `RowStepCommon.lean` | `ExpansionState.selectedRow`, 12 | Recover the exact row and selected slot. |
| Same file | `representsRows_push_selected`, 37 | Add the selected PC to supplied operand/RAM observations. |
| Same file | `representsRows_push_operands`, 62 | Transport operand and effective-address values through the append, reusing `rs1Value_real` and `rs2Value_real`. |
| `RowStepJalr.lean` | `append_jalr_row`, 13 | Complete the JALR extension. |
| `RamCutAgreement.lean` | private `remap_below_ram`, 10 | Exclude a device flag address from an ordinary-RAM index. |
| Same file | `finalRamWord_ordinary`, 28 | Identify the final ordinary-RAM image with the byte map. |
| Same file | private `ordinary_index_ne_termination`, 69 | Exclude termination from the ordinary-RAM portion. |
| Same file | `ramAgreement_iff`, 86 | Combine or split the two memory agreements. |
| Same file | `ordinary_memory_step`, 111 | Preserve device words and conditional termination zero for a RAM access. |
| `MemoryRowAppend.lean` | `ExpansionState.memoryAt`, 11 | Recover the prepared state's memory agreements. |
| Same file | `memory_step_mono`, 30 | Weaken the conditional termination obligation by enlarging its store event. |
| Same file | private `exists_fin_push`, 39 | Split a property of an appended array element into old/new cases. |
| Same file | `append_memory_row`, 49 | Assemble the common memory-row extension. |
| `MemoryRowExecution.lean` | `load_row_execution`, 33; `store_row_execution`, 68 | Normalize the RAM/device execution contracts for each instruction family. |
| `RowStepMemory.lean` | `append_ld_row`, 31; `append_sd_row`, 71 | Supply the selected operands, address, execution and live-register update to the shared append. |
| `RowStepKinds.lean` | `ld_ram_row_step`, 91; `ld_device_row_step`, 102; `sd_ram_row_step`, 113; `sd_device_row_step`, 125; `jalr_row_step`, 163 | Replace only these five staged bodies with the completed proofs. |

`RowStepKinds.lean` received targeted body replacements and imports for the new modules.
Its two terminal-stage bodies were not edited by this pass.
The five requested staged signatures were compared exactly with the committed source and are unchanged.
The helper visibility changes also preserve their exact original statements and proofs.
No existing proved fact was replaced by `sorry`, and no new `sorry` was introduced.

### Validation and axiom audit

`lake build JoltConstraints.Soundness.Layer6.RowStep` passed with 8703 jobs, including all new modules and the live-register RAM ports.
The final `RowStepMemory`, `RowStepKinds`, and `RowStep` compilations took about 4.7, 5.2, and 4.3 seconds respectively.
The three ported Layer 5 modules built in about 3.7–4.7 seconds each.
The full repository target was not run.
The build log is `/private/tmp/row-step-proofs-build.log`.
Whitespace checks found no errors in the edited existing files or the new modules.

`#print axioms` and a recursive dependency walk were run for all five steps, `ramAgreement_iff`, and the three public Layer 5 RAM rules.
Each reports exactly:

```text
[propext, sys_enable_experimental_extensions, Classical.choice, Quot.sound]
```

Each recursive walk found no declaration directly using `sorryAx`.
At this audit point, `row_step` itself still reaches exactly `host_row_step`, `jal_row_step`, and the pre-existing `plain_row_step_other` as direct `sorryAx` users.
JAL and HostIO are the other agent's work; their status may change independently after this audit.
The audit source and output are `/private/tmp/row-step-proofs-axioms.lean` and `/private/tmp/row-step-proofs-axioms.log`.

No new or ported proof exceeded ten seconds in the measured module builds.
The publicization build of the entire `PlainRow` module took about ten seconds, so that module was also profiled with command/proof timing enabled.
Its slowest individual proof was the unchanged private `arithmetic_row_observations`, at about 1.69 seconds; the general append constructor took about 0.41 seconds.
The profile is `/private/tmp/row-step-proofs-plain-profile.log`.
There are no new `bv_decide`, `native_decide`, `decide +kernel`, or axiom declarations, and no proof limits were raised.

This resumed pass edited the five authorized publicizations, the three Layer 5 RAM files, the five owned `RowStepKinds` bodies and imports, the six new Layer 6 support modules, and this report section.
`RamAgreement.lean` did not need an edit: the RAM/device bridge lives in Layer 6, above both agreement definitions.
The committed `Jalr.lean` was reused unchanged.
The protected files, JAL/HostIO proofs, and the other agent's report section were not edited.
Work stops here with the five requested steps complete and no commit made.

## JAL and HostIO

This pass stopped during the required plan audit, before editing Lean code.
Neither `jal_row_step` nor `host_row_step` was proved, and their staged statements and `sorry` bodies are unchanged.
The Layer 5 ports were not started.

The requested separate `RowStepTerminal.lean` cannot reuse the append observation proofs under the permitted edit scope.
`representsRows_push` is private in `JoltConstraints/Soundness/Layer6/PlainRow.lean:410`, and `representsPrefix_push` is private there at line 470.
Those are the only shared append lemmas that establish the `RepresentsPrefix` obligation passed to the public `append_expansion_row_of_termination` at `PlainRow.lean:941`.
`expansionLive_after` at line 286 is private too, so the terminal step's next-register agreement cannot use the existing live-set transition from the new file.
The previous proving pass recorded the same visibility problem for JALR, and these declarations remain private in the current code.
The plan permits editing `Jal.lean`, `HostCallRegisterFrame.lean`, the new `RowStepTerminal.lean`, and the two `RowStepKinds.lean` bodies, but excludes `PlainRow.lean`.
Re-proving the generic append and live-set arguments in the new file would duplicate the existing proofs, contrary to `AGENTS.md`.

The proposed correction is to permit publicizing `representsRows_push`, `representsPrefix_push`, and `expansionLive_after` in `PlainRow.lean`, with their statements and proofs unchanged and docstrings added.
The JAL and HostIO step statements need no added hypotheses: `state.next` supplies the selected slot and HostIO `NextStep`, while the terminal JAL can use prepared PC, `source_compressed_of_last`, and `assumptions.pcNoWrap`.
This audit found a file-scope mistake in the plan, not a counterexample to either staged statement.
No build or axiom check was run because no Lean code changed.
No commit was made.

### Resumed Layer 5 ports

The earlier file-scope blocker is resolved for the resumed task: another agent has made `expansionLive_after`, `representsRows_push`, and `representsPrefix_push` public in the working tree.
This pass did not edit `PlainRow.lean` and did not start the Layer 6 JAL or HostIO row steps.

`JoltConstraints.Soundness.RegisterAgreementOn.setNextPC` is now the shared frame theorem at `JoltConstraints/Soundness/Layer5/Jal.lean:81`.
Its statement takes `RegisterAgreementOn live` and returns agreement on the same live set after updating Sail's `nextPC`.
The former full-agreement `RegisterAgreement.setNextPC` was removed because no proof uses it; the frame proof was generalized in place.

`JoltConstraints.Soundness.jal_step` at `JoltConstraints/Soundness/Layer5/Jal.lean:97` now takes `RegisterAgreementOn live` instead of full `RegisterAgreement` and returns agreement on `live` plus the JAL destination.
The successful execution and link-value conclusions, selected row, no-wrap, PC and nextPC premises are unchanged.
The proof still uses the same constrained link value, `RegisterAgreementOn.write`, and the generalized nextPC frame theorem.
No source-register liveness premise was added because JAL has no source register.

`JoltConstraints.Soundness.host_call_selected_step` at `JoltConstraints/Soundness/Layer5/HostCallRegisterFrame.lean:30` now takes and returns `RegisterAgreementOn live` instead of full agreement.
Its successful execution conclusion and all other premises, including the required following-cycle bound, are unchanged.
The existing HostIO Sail and virtual-register frame proof is reused with `RegisterAgreementOn.noWrite`.
No full-agreement wrapper was retained because a repository-wide call-site search found no proof using either old step signature or the old full nextPC frame theorem.

`lake build JoltConstraints.Soundness.Layer5.Jal JoltConstraints.Soundness.Layer5.HostCallRegisterFrame` passed; the two module builds took 5.3 and 4.9 seconds respectively.
`#print axioms JoltConstraints.Soundness.jal_step` and `#print axioms JoltConstraints.Soundness.host_call_selected_step` both report `[propext, sys_enable_experimental_extensions, Classical.choice, Quot.sound]`, with no `sorryAx`.
The axiom-check source is `/private/tmp/row-step-layer5-ports-axioms.lean`.
`git diff --check` passed for both edited Lean files.
No new `bv_decide` use, axiom, `sorry`, or proof limit was added, and neither ported proof took more than ten seconds.
Only `Jal.lean`, `HostCallRegisterFrame.lean`, and this report were edited by this pass.
No commit was made.
