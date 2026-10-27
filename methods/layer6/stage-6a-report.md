# Layer 6, stage 6a report: plan audit stopped

The file split prescribed in `methods/layer6/stage-6a.md:9` cannot use `arithmetic_exec_eq` unchanged from `DivisionAppend.lean`.
The plan requires that theorem for the honest row executions at `methods/layer6/stage-6a.md:23-25`.
Its declaration is `private theorem arithmetic_exec_eq` in `JoltConstraints/Soundness/Layer6/DivisionBlock.lean:204`.
Moving it unchanged into `DivisionDefs.lean` would leave it private to that module, so `DivisionAppend.lean` could not reference it.
I confirmed the visibility rule with `#check JoltInstance.arithmetic_exec_eq` in a separate file importing `DivisionBlock`; Lean reported `Unknown constant`.

The plan needs a visibility change: make `arithmetic_exec_eq` public in `DivisionDefs.lean`, retaining its statement and proof, or provide a public theorem there with the same result.
This conflicts with the instruction to move it unchanged, so I stopped for review as the plan requires.
The rest of the plan has not been fully audited.

No Lean declaration was added or changed.
No proof was staged, proved, or profiled; no `bv_decide` was added.
The aggregate build and `#print axioms JoltInstance.division_append_honest` were not run because implementation stopped at the audit finding.
My only repository edit is this report.
Another agent's concurrent edit to `JoltConstraints/Soundness/Layer7/StallSuffix.lean` is present and untouched.
No commit was made.

## Continuation after the corrected plan

Commit `1df8c85` resolves the visibility problem above by allowing a moved private helper used from another file to become public with the same statement and a docstring.
I resumed the audit and found no further incorrect plan claim in the code checked before implementation.
The eight `*ProgramAuto` division programs in `JoltBytecode/JoltISA/ExpansionsAutomated.lean` write only virtual instruction temporaries before their final architectural destination write, and none has an LD or SD row.
`ArithmeticAdviceSequence.arithmetic` and `DivisionArithmeticRow` also exclude memory accesses from the block identified by the staged layout theorem.
`RepresentsRows` compares only non-temporary operand values, while `ExpansionLive` reduces to non-temporary registers when the block is complete.
`DivisionFinalAgreement` equates the final Sail state and device, which are the components used by `TraceWitness.finalRamWord`.
`UntrustedAnswerRun.NextStep` supplies honest advice for the retained prefix and the prepared entry state.
`honestTracerAdviceAtStepN` uses the source instruction and the first row's pre-state, and `honestTracerAdviceAtStepN_extract` preserves an earlier row's advice after appending.
I checked the corresponding pinned Jolt code at `5def437f`: `jolt/crates/jolt-program/src/expand/division/rem.rs` (`expand_rem`), `division/divuw.rs` (`expand_divuw`), `jolt/crates/jolt-program/src/expand/metadata.rs` (`stamp_sequence_metadata`), and `jolt/tracer/src/instruction/mod.rs` (`trace_inline_sequence_with_advice`).
These checks do not establish the new Lean proof obligations.

I moved the existing division declarations into `DivisionDefs.lean` and changed only the visibility and docstring of `arithmetic_exec_eq`.
The existing declarations in `DivisionBlock.lean` retained their statements and proof bodies.
I added `DivisionReplayRows` and three named staged lemmas in `DivisionAppend.lean` for row construction, completed-state transfer, and the new rows' honest advice.
The intended caller `division_append_honest` remains a `sorry`; the new staged lemmas are not yet used by it.
I stopped implementation when Ari requested a report.

### Declarations

Locations are relative to `JoltConstraints/Soundness/Layer6/`.
“Moved” means the existing statement and proof body moved unchanged from `DivisionBlock.lean`.
Existing staged statements retain their `sorry`.

| Declaration | Location | Status |
| --- | --- | --- |
| `DivisionKind` | `DivisionDefs.lean:16` | Moved |
| `DivisionKind.source` | `DivisionDefs.lean:23` | Moved |
| `DivisionKind.program` | `DivisionDefs.lean:38` | Moved |
| `DivisionKind.result` | `DivisionDefs.lean:53` | Moved |
| `DivisionKind.honestAdvice` | `DivisionDefs.lean:68` | Moved |
| `expansionInstructions` | `DivisionDefs.lean:75` | Moved |
| `patchAdviceWord` | `DivisionDefs.lean:83` | Moved |
| `ArithmeticAdviceSequence` | `DivisionDefs.lean:93` | Moved |
| `division_expansion_layout` | `DivisionDefs.lean:109` | Moved, existing staged statement |
| `witnessWord` | `DivisionDefs.lean:127` | Moved private definition |
| `witnessWord_of_encoded` | `DivisionDefs.lean:135` | Moved private proof |
| `single_advice_index` | `DivisionDefs.lean:150` | Moved private proof |
| `patchAdviceWord_runtime` | `DivisionDefs.lean:181` | Moved private proof |
| `runtime_advice_isSome` | `DivisionDefs.lean:199` | Moved private proof |
| `arithmetic_exec_eq` | `DivisionDefs.lean:207` | Moved proved lemma; made public and added docstring; statement unchanged |
| `expansionInstructions_at` | `DivisionDefs.lean:214` | Moved private proof |
| `arithmetic_advice_row_run` | `DivisionDefs.lean:226` | Moved private proof |
| `arithmetic_advice_suffix_run` | `DivisionDefs.lean:265` | Moved private proof |
| `arithmetic_advice_sequence_run` | `DivisionDefs.lean:361` | Moved proof |
| `division_program_result` | `DivisionDefs.lean:402` | Moved, existing staged statement |
| `DivisionFinalAgreement` | `DivisionDefs.lean:415` | Moved |
| `DivisionReplayRows` | `DivisionAppend.lean:17` | New structure; not yet built |
| `division_replay_rows` | `DivisionAppend.lean:35` | New staged lemma; not yet built |
| `division_replay_complete` | `DivisionAppend.lean:62` | New staged lemma; not yet built |
| `division_replay_honest_new` | `DivisionAppend.lean:91` | New staged lemma; not yet built |
| `division_program_honest` | `DivisionBlock.lean:20` | Existing staged statement, statement unchanged |
| `division_append_honest` | `DivisionBlock.lean:41` | Existing staged statement, statement unchanged |
| `division_block` | `DivisionBlock.lean:81` | Existing proof, statement unchanged |

The three new staged lemmas use only caller data: the row constructor uses `state`, `shape`, `entry`, and `honestRun`; the completion transfer uses the candidate's `complete` invariant and `same`; the advice lemma uses the source lookup and replay rows.
No existing theorem received a new hypothesis or statement change.
No `bv_decide`, `native_decide`, `decide +kernel`, axiom, or proof-limit change was added.
No proof was measured above ten seconds; the new staged lemmas have no proofs to profile.

### Validation and remaining work

`lake build JoltConstraints.Soundness.Layer6.DivisionBlock` passed immediately after the file split and before adding the staged declarations to `DivisionAppend.lean`.
That build checked `DivisionDefs.lean` and the new import chain, with `DivisionDefs.lean` building in 4.8 seconds.
The next `lake build JoltConstraints.Soundness.Layer6.DivisionAppend` failed while building another agent's in-progress `Layer7/StallSuffix.lean`, before checking `DivisionAppend.lean`.
I left `StallSuffix.lean` and `TerminalNextPC.lean` untouched.
The new staged declarations and the aggregate `JoltConstraints` build have not passed a build.
I did not run `#print axioms JoltInstance.division_append_honest` because its caller still has its original `sorry` and the new module did not build.
`git diff --check` passed for tracked changes; the new files were not type-checked.
The proof work remaining is to check the new staged statements in Lean, prove `division_append_honest` from them and the old-prefix advice fact, then rebuild and audit axioms.
No commit was made.

## Completion of the Stage 6a caller

The three staged replay lemmas now build in Lean with their `sorry`s still at theorem level.
`division_replay_honest_new` has the added hypothesis `context.bytecode[first].starts_source = true` at `DivisionAppend.lean:133`.
Its caller proves this with `state.starts`; no existing theorem statement changed.
The other two staged statements are unchanged.

`RunExtends.honestAdvice_before` at `DivisionAppend.lean:36` is a new proved lemma.
It uses `RunExtends` to identify the retained row prefix and `honestTracerAdviceAtStepN_extract` to preserve the tracer's advice calculation for each earlier row.
Its proof introduces no new axiom or `bv_decide` use.

`division_append_honest` at `DivisionBlock.lean:41` is now proved with its original statement unchanged.
It obtains the replay from `division_replay_rows`, transfers the completed expansion invariant through `division_replay_complete`, gets old-row advice from `entry` and `RunExtends.honestAdvice_before`, and gets new-row advice from `division_replay_honest_new` using `state.starts`.
The existing `nonzero` hypothesis remains in the unchanged statement and is unused by this caller proof.
Each new proof is under 60 lines.

`lake build JoltConstraints.Soundness.Layer6.DivisionAppend JoltConstraints.Soundness.Layer6.DivisionDefs` passed with 8,679 jobs.
`lake build JoltConstraints.Soundness.Layer6.DivisionBlock` passed with 8,680 jobs.
The first aggregate build attempt failed in another agent's unfinished `TerminalNextPC.lean` at line 545; no Stage 6a file caused that failure.
After that file built again, `lake build JoltConstraints` passed with 8,810 jobs.
The aggregate log is `/private/tmp/layer6-stage6a-aggregate-build.log`.
No proof was observed taking more than about ten seconds; the changed modules built in at most 4.2 seconds each on the final targeted builds.
`git diff --check` passed.

`#print axioms JoltInstance.division_append_honest` reports `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`.
A transitive constant-dependency check found exactly three reachable declarations directly using `sorryAx`: `division_replay_rows`, `division_replay_complete`, and `division_replay_honest_new`.
The proved `RunExtends.honestAdvice_before` has no reachable direct `sorryAx` user.
The axiom checks are in `/private/tmp/layer6-stage6a-axioms.lean` and `/private/tmp/layer6-stage6a-direct-sorries.lean`.
No new `bv_decide`, `native_decide`, `decide +kernel`, axiom declaration, or proof-limit change was made.

At Ari's request, I reran only `lake build JoltConstraints.Soundness.Layer6.DivisionBlock` against the final files; it passed with 8,680 jobs.
I then reran the axiom checks from files importing only `DivisionBlock`; both passed and confirmed the same three direct staged dependencies.
The targeted build log is `/private/tmp/layer6-stage6a-division-build.log`, and the axiom outputs are `/private/tmp/layer6-stage6a-axioms.log` and `/private/tmp/layer6-stage6a-direct-sorries.log`.
I did not rerun the aggregate build after this request.

I did not edit the other agent's `TerminalNextPC.lean`, `StallSuffix.lean`, `LastJump.lean`, or Layer 5 files.
Their concurrent changes, including the untracked `methods/layer6/stage-6c.md`, remain untouched.
No commit was made.
Work stops with the three named replay lemmas staged for Ari's review.
