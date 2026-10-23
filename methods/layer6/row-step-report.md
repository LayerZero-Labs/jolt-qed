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

This proving pass stopped at a file-scope dependency after completing the new Layer 5 JALR execution lemma.
The five requested Layer 6 steps remain unchanged, including their existing `sorry`s.
No counterexample to a staged step was found in this pass.
The remaining work has not been completed or certified by this report.

### JALR execution

`JoltConstraints.Soundness.jalr_step` is new at `JoltConstraints/Soundness/Layer5/Jalr.lean:19`.
It takes agreement on a live-register predicate and liveness of the JALR base, and proves the exact successful execution, the witness link write, and next-column agreement on the old live registers plus the destination.
The target uses the old base even when destination and base alias, adds the immediate with 64-bit wrapping, and clears bit zero.
Virtual bases use the same canonical register-read argument as architectural bases.
The pinned check was `jolt/tracer/src/instruction/jalr.rs` (`JALR::exec`) at `5def437f`.

The new lemma explicitly requires prepared `nextPC` and the no-wrap equality for the link.
These are obligations already available to the staged terminal JALR caller through its preparation premise, `source_compressed_of_last`, and `terminal_link_no_wrap` with `assumptions.pcNoWrap`; no premise was added to that caller.
The link equation reuses `selected_jump_link_write_value`.
The register frame reuses `register42_nextPC_preserves_sourceValue`, and the write uses `RegisterAgreementOn.write`.
There is no architectural-register-only execution assumption and no assumption of a following cycle.

The plan's target helpers were also checked.
`selected_jalr_next_target` requires a following real cycle, so it cannot be applied unconditionally at the terminal witness cycle.
The local execution lemma does not need that equation: it computes the interpreter target directly, while its next-column register conclusion is conditional on the next column existing.
This is an interface distinction, not a discovered false staged statement.

### Scope dependency and remaining work

The existing shared append helpers are private in `JoltConstraints/Soundness/Layer6/PlainRow.lean`: `expansionLive_after` at line 286, `representsRows_push` at line 410, `representsPrefix_push` at line 470, and `append_expansion_row` at line 1033.
The current task's edit list does not include that file.
The proposed resolution is to make those four declarations public, adding docstrings while leaving their statements and proofs unchanged.
This would let the JALR proof reuse the same observation, cut, liveness and termination arguments as the existing arithmetic append.
The alternative of copying those arguments conflicts with `AGENTS.md`: “Before writing a second proof that looks like an earlier one, stop.”
Permission for this visibility change was requested and had not been received when this section was written.

The RAM bridge needs the initialized run's layout and device-frame bounds in addition to the two agreement predicates, because `finalRamWord` overlays device buffers on the ordinary-RAM image.
The existing `UntrustedAnswerRun.final_device_same` and `UntrustedAnswerRun.final_outputs_fit_layout` provide the execution-dependent frame and output bound.
The reusable overlay-disjointness fact, `overlayRamBytes_below_word`, is private at `JoltConstraints/Soundness/Layer5/RamInitialization.lean:87`, another file outside the current edit list.
Permission was also requested to make that declaration public with its statement and proof unchanged.
No duplicate overlay proof was written.

The live-register ports of `ld_ram_step`, `sd_ram_step`, and `sd_ram_step_agreement`, the common cut-RAM bridge, and all five requested Layer 6 proofs remain to be done.
The device-step signatures already accept live agreement and return the conditional termination obligation needed by the general append constructor.
Their changing proofs were read but not edited.
The new Layer 5 JALR lemma is ready for its staged caller but is not yet wired into `jalr_row_step` because of the scope dependency above.

### Validation and changes

`lake build JoltConstraints.Soundness.Layer5.Jalr` passed, with the new module taking about 3.7 seconds.
`#print axioms JoltConstraints.Soundness.jalr_step` reports `[propext, sys_enable_experimental_extensions, Classical.choice, Quot.sound]`, with no `sorryAx`.
The audit source is `/private/tmp/row-step-proofs-jalr-audit.lean` and the build log is `/private/tmp/row-step-proofs-jalr.log`.
No new proof exceeded ten seconds in the module build.
There are no new uses of `bv_decide`, `native_decide`, or `decide +kernel`, no new axiom declarations, and no raised proof limits.
No existing statement, definition, or hypothesis was changed.
Only the new `Jalr.lean` and this report were edited by this proving pass.
The other agents' files were not edited, and no commit was made.
