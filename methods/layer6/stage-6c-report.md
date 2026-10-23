# Layer 6, stage 6c report

## Plan audit

I read `AGENTS.md`, `methods/layer6/reuse.md`, `methods/layer6/stage-6a-report.md`, and `methods/layer6/stage-6c.md` in that order before implementation.
I checked the Stage 6c claims against the current Lean code and found no incorrect claim.
`execProgram_instr_run_retire_inv` in `JoltBytecode/InstructionEquivalence/ProofSupport/Lemmas.lean:50` splits a successful program execution into its first instruction and the tail.
`appendUntrustedRow` in `JoltConstraints/Soundness/Layer6/PlainRow.lean:338` requires exactly the execution, initial-entry, and predecessor-linkage facts described by the plan.
`UntrustedAnswerRun.NextStep.ready` in `Layer5/MemoryAccessRestriction.lean:29` supplies the first prepared entry, while `expansion_row_remaining` and `expand_program_layout.next` give the interior countdown and consecutive row layout.
`arithmetic_exec_eq` in `Layer6/DivisionDefs.lean:207` equates ordinary and relaxed execution for `DivisionArithmeticRow`.
The existing `arithmetic_advice_suffix_run` in `Layer6/DivisionDefs.lean:269` uses a witness-side instruction induction, so its program-splitting pattern is relevant but its witness advice result cannot construct the honest replay directly.

The eight generated division programs in `JoltBytecode/JoltISA/ExpansionsAutomated.lean` contain no LD or SD and write only instruction temporaries before the final architectural destination.
`ArithmeticAdviceSequence.arithmetic` and `DivisionArithmeticRow` exclude memory and host operations.
`RepresentsRows` in `Layer6/ExecutionPrefix.lean:21` compares non-temporary source operands, and `ExpansionLive` in `Layer6/PrefixState.lean:84` reduces to persistent registers after the expansion completes.
`DivisionFinalAgreement` in `Layer6/DivisionDefs.lean:419` contains the final Sail state and device equality needed for `TraceWitness.finalRamWord`.
These facts support the proposed completion transfer, but that transfer remains unproved.

For new-row advice, `honestTracerAdviceAtStepN` in `JoltConstraints/honest_trace.lean:194` uses the expansion's first row, that row's pre-state, the source instruction, and the number of earlier advice rows.
`ArithmeticAdviceSequence.singleAdvice` gives one advice row, and the proved helper `division_source_advice_single` shows each division source supplies the corresponding singleton advice list.
The bytecode layout and source-advice behavior agree with pinned Jolt commit `5def437f` in `jolt/crates/jolt-program/src/expand/metadata.rs` (`stamp_sequence_metadata`) and `jolt/tracer/src/instruction/mod.rs` (`trace_inline_sequence_with_advice`).

## Proof completed

`division_replay_honest_new` is proved with its existing statement, including the already approved `starts` hypothesis.
Its proof identifies the source's first row, proves later block rows do not start another expansion, maps replay rows to expansion instructions, and shows the one advice row has zero earlier advice rows.
It then computes the tracer's advice from the source instruction and the replay's first pre-state.
No premise or staged statement changed.

| Declaration | Location | Change |
| --- | --- | --- |
| `division_source_advice_single` | `DivisionAppend.lean:201` | New private proof of the singleton division advice list. |
| `division_block_later_not_start` | `DivisionAppend.lean:207` | New private proof from countdown and bytecode layout. |
| `expansion_start_of_segment` | `DivisionAppend.lean:239` | New private general start-index proof. |
| `division_replay_start_flag` | `DivisionAppend.lean:546` | New private replay start-flag proof. |
| `division_replay_start_at` | `DivisionAppend.lean:604` | New private expansion-start proof. |
| `division_replay_instruction_at` | `DivisionAppend.lean:633` | New private bytecode-to-instruction proof. |
| `division_replay_advice_flag` | `DivisionAppend.lean:677` | New private advice-flag proof. |
| `division_replay_advice_before_zero` | `DivisionAppend.lean:697` | New private single-advice index proof. |
| `division_replay_first_source` | `DivisionAppend.lean:740` | New private first-row pre-state and source proof. |
| `division_replay_honest_new` | `DivisionAppend.lean:866` | Existing staged theorem proved; statement unchanged. |
| `expansion_row_remaining` | `PlainRow.lean:250` | Existing private theorem made public in place with a docstring; statement and proof unchanged. |
| `single_advice_index` | `DivisionDefs.lean:152` | Existing private theorem made public in place with a docstring; statement and proof unchanged. |
| `expansionInstructions_at` | `DivisionDefs.lean:218` | Existing private theorem made public in place with a docstring; statement and proof unchanged. |

At that review, the three visibility changes were the only changes outside `DivisionAppend.lean`.
No new `bv_decide`, `native_decide`, `decide +kernel`, axiom, proof limit, or hypothesis was added.
No individual changed module build exceeded ten seconds: `PlainRow` took 8.7 seconds, `DivisionDefs` 4.5 seconds, and `DivisionAppend` 6.3 seconds on the targeted build.

## Earlier row-construction blocker, now resolved

At the previous review, `division_replay_rows` and `division_replay_complete` retained their theorem-level `sorry`s.
The immediate gap was constructing an instruction-indexed runtime advice value whose patched instruction is `patchAdviceWord q instruction`.
The user approved generalizing the existing two-branch `zeroRuntimeAdvice` definition in place and using the existing patch lemmas.
The resulting constructor and patch proof now compile, and `division_replay_rows` is proved.

## Previous validation and repository state

`lake build JoltConstraints.Soundness.Layer6.DivisionBlock` passed with 8,680 jobs.
`lake build JoltConstraints` also passed with 8,811 jobs while the other agent's edits were present.
The axiom check from a file importing only `DivisionBlock` reports no `sorryAx` for `division_replay_honest_new`.
At that revision, `#print axioms JoltInstance.division_append_honest` reported `sorryAx` through `division_replay_rows` and `division_replay_complete`.
`git diff --check` passed.
I did not edit Layer 5, `TerminalNextPC.lean`, `StallSuffix.lean`, `LastJump.lean`, or the other agent's new files.
No commit was made.

## Continuation: replay rows proved

I re-read `AGENTS.md`, `methods/layer6/reuse.md`, this stage plan, and this report before continuing.
The user's correction about the dependent runtime advice split matches `PlainRow.lean` and `DivisionDefs.lean`.
The staged statements of `division_replay_rows`, `division_replay_complete`, and `division_replay_honest_new` were not changed.

`division_replay_rows` at `DivisionAppend.lean:805` is now proved.
The proof splits the honest program run at its first instruction, appends a certified row, and then inducts over the remaining instructions.
For every interior append it derives the predecessor from the replay's last row, proves the countdown is nonzero, and links the next row's pre-state to the previous post-state.
The `runtimeAdviceFor` value patches the VirtualAdvice row to the honest word, and other arithmetic rows ignore it.
The invariant records the exact bytecode index, initial pre-state, final post-state, and advice observation of each appended row.

| Declaration | Location | Change |
| --- | --- | --- |
| `runtimeAdviceFor` | `PlainRow.lean:612` | Generalized the existing private `zeroRuntimeAdvice` in place to take a word; made it public with a docstring. Its existing caller passes zero. |
| `finalTraceState_back` | `PlainRow.lean:457` | Made the existing private fact public in place with a docstring; statement and proof unchanged. |
| `rawEntry_starts` | `PlainRow.lean:828` | Made the existing private fact public in place with a docstring; statement and proof unchanged. |
| `rawEntry_linked` | `PlainRow.lean:842` | Made the existing private fact public in place with a docstring; statement and proof unchanged. |
| `runtimeAdviceFor_patch` | `DivisionAppend.lean:13` | New private proof that the generalized advice constructs `patchAdviceWord q`. |
| `runtimeAdviceFor_observation` | `DivisionAppend.lean:25` | New private proof of the advice observation. |
| `divisionReplayStep` | `DivisionAppend.lean:33` | New private row constructor. |
| `divisionReplayStep_exec` | `DivisionAppend.lean:39` | New private execution certificate using `arithmetic_exec_eq`. |
| `division_replay_append_one` | `DivisionAppend.lean:61` | New private certified append and row observation. |
| `division_replay_interior_entry` | `DivisionAppend.lean:91` | New private countdown linkage fact. |
| `division_next_step_raw_entry` | `DivisionAppend.lean:113` | New private adapter from `NextStep` to `RawRowEntry`. |
| `division_replay_first_row` | `DivisionAppend.lean:129` | New private split and append of the first instruction. |
| `DivisionReplayRows.push` | `DivisionAppend.lean:278` | New private append preservation proof. |
| `division_replay_next_entry` | `DivisionAppend.lean:355` | New private predecessor and prepared state proof. |
| `division_replay_first_state` | `DivisionAppend.lean:406` | New private one-row replay invariant. |
| `division_replay_suffix` | `DivisionAppend.lean:470` | New private instruction-list induction. |
| `division_replay_rows` | `DivisionAppend.lean:805` | Existing staged theorem proved; statement unchanged. |

`patchAdviceWord_runtime` at `DivisionDefs.lean:186` and `runtime_advice_isSome` at `DivisionDefs.lean:206` were already public in the current revision and were reused without a new diff to that file.
No new `bv_decide`, `native_decide`, `decide +kernel`, axiom, proof limit, or hypothesis was added.
The `DivisionReplayRows.push`, first-row, and suffix helper proofs exceed the plan's approximate 60-line preference; they are separated by purpose, and I did not compress them into broad tactic splits.
No individual changed-module proof exceeded about ten seconds in the targeted builds.

## Completion transfer blocked by existing private frame proof

The plan's instruction to prove the division frame once over the instruction list is outdated against the current code.
`DivisionPrograms.lean:45` defines `DivisionFrame`, and `DivisionPrograms.lean:122`, `:134`, and `:177` already prove the per-instruction frame, program frame, and generated-program row safety, respectively.
Those declarations are private, and `DivisionPrograms.lean` belongs to the other agent's edit scope.
The completion transfer needs these frame facts for candidate and replay prefixes before the last architectural write, so reproducing the frame proof in `DivisionAppend.lean` would violate the repository instruction to extract shared work before writing a second similar proof.
I stopped before changing `division_replay_complete` at `DivisionAppend.lean:837`; it retains its existing theorem-level `sorry`.
A reusable public prefix frame theorem from the owning file, with its supporting relation exposed as needed, is the concrete dependency for continuing this proof.
I did not add a premise to `division_replay_complete` or stage an unproved duplicate frame lemma.

## Current validation

`lake build JoltConstraints.Soundness.Layer6.DivisionBlock` passed with 8,681 jobs.
`lake build JoltConstraints` passed with 8,814 jobs while the other agent's Layer 5 edits were present.
The axiom check from a file importing only `DivisionBlock` shows `division_replay_rows` has no `sorryAx`.
`division_append_honest` still has `sorryAx`, now through the remaining `division_replay_complete` gap.
`git diff --check` passed.
I did not edit `DivisionPrograms.lean`, `DivisionBlock.lean`, Layer 5, `TerminalNextPC.lean`, `StallSuffix.lean`, or `LastJump.lean`.
I made no commit.

## Continuation: public frame facts and the remaining completion gap

I re-read `AGENTS.md`, the stage 6c plan, and this report before this continuation.
I checked the proposed reuse against `DivisionPrograms.lean`, `DivisionAppend.lean`, `ExpansionState`, `RepresentsRows`, and the generated division programs.
The generated programs do place their architectural write on the last row, including the one-row `rd = x0` case.
The existing frame facts do not express that placement.

I made the existing declarations below public in place in `DivisionPrograms.lean`.
Their statements and proof bodies are unchanged.
Each newly public theorem received a docstring; the four definitions already had docstrings.

| Declaration | Line | Change |
| --- | ---: | --- |
| `DivisionFrame` | 48 | Private definition made public. |
| `divisionFrame_refl` | 57 | Private theorem made public; docstring added. |
| `divisionFrame_trans` | 62 | Private theorem made public; docstring added. |
| `DivisionDestinationSafe` | 75 | Private definition made public. |
| `DivisionInstructionSafe` | 81 | Private definition made public. |
| `divisionInstructionSafe_parts` | 89 | Private theorem made public; docstring added. |
| `DivisionRows` | 101 | Private definition made public. |
| `divisionFrame_instr` | 143 | Private theorem made public; docstring added. |
| `divisionFrame_program` | 158 | Private theorem made public; docstring added. |
| `division_program_rows` | 192 | Private theorem made public; docstring added. |

`DivisionFrame` at `DivisionPrograms.lean:48` relates the device, advice tape, host settings, and persistent virtual registers, but has no Sail-state condition.
`DivisionDestinationSafe` at `DivisionPrograms.lean:75` accepts every `.xreg` destination, and `DivisionRows` therefore permits an architectural write before the final row.
Consequently `divisionFrame_instr` and `divisionFrame_program` cannot establish equality of candidate and replay Sail registers at an interior row.
`RepresentsRows.rs1` and `.rs2` at `ExecutionPrefix.lean:29` and `:34` require that equality when a row reads a non-temporary architectural register.
The precise missing fact is that every proper prefix of each generated division program leaves the Sail state equal to its entry Sail state.
It would need a shared prefix preservation proof, including the generated program's last-write placement, before the row observations can be transferred.
Adding that proof in `DivisionPrograms.lean` would exceed the visibility-only changes authorized for that file; reproducing its instruction-family case analysis in `DivisionAppend.lean` would duplicate the existing frame proof contrary to `AGENTS.md`.

I left `division_replay_complete` at `DivisionAppend.lean:837` with its original theorem-level `sorry` and did not change its statement or add a new premise.
I removed the exploratory private helpers from `DivisionAppend.lean` because no proved declaration used them, leaving no diff in that file.
No new `bv_decide`, axiom, proof limit, or staged statement was added.

`lake build JoltConstraints.Soundness.Layer6.DivisionBlock` passed with 8,681 jobs; its changed modules each built in under ten seconds.
An axiom check from a file importing only `DivisionBlock` reports `sorryAx` for `JoltInstance.division_append_honest`, through the remaining `division_replay_complete` gap.
`git diff --check` passed before this report update.
I did not run the full aggregate build while other agents were editing Layer 5 files.
I did not edit those files or commit.

## Continuation: shared prefix frame proved, completion transfer still open

I re-read `AGENTS.md`, the stage 6c plan, the reuse guide, and this report.
I verified the frame generalization against `rX_bits_pure` in `JoltBytecode/InstructionEquivalence/ProofSupport/RegisterAccess.lean:133` and the eight generated programs in `JoltBytecode/JoltISA/ExpansionsAutomated.lean`.
The proper-prefix claim is true: the generated program's only architectural destination is its last row, including the single-row `rd = x0` path.

`DivisionPrograms.lean` now has one parameterized preservation proof.
`keepSail = false` allows the original architectural destination class and recovers the unchanged statements of `divisionFrame_instr` and `divisionFrame_program`.
`keepSail = true` permits only instruction-temporary destinations or no destination and also preserves the Sail state.
The program-shape check proves full-row safety and proper-prefix safety together in one split over the eight division kinds.

| Declaration | Location | Change |
| --- | --- | --- |
| `DivisionFrameFor`, `DivisionDestinationSafeFor`, `DivisionInstructionSafeFor`, `DivisionRowsFor` | `DivisionPrograms.lean:105` | New private parameterized frame and destination predicates. |
| `divisionFrameFor_refl`, `divisionFrameFor_trans` | `DivisionPrograms.lean:120` | New private relation laws used by the shared proof. |
| `divisionFrame_read`, `divisionFrame_write` | `DivisionPrograms.lean:129`, `:142` | Generalized existing private proofs over `keepSail`; their statements changed. |
| `divisionFrame_instr_for`, `divisionFrame_program_for` | `DivisionPrograms.lean:167`, `:195` | New private shared instruction and program preservation proofs. |
| `divisionFrame_instr`, `divisionFrame_program` | `DivisionPrograms.lean:182`, `:231` | Existing public statements unchanged; proofs now project the shared result. |
| `DivisionRows.forFalse` | `DivisionPrograms.lean:214` | New private conversion for the original destination class. |
| `division_program_rows_shape` | `DivisionPrograms.lean:250` | New private combined check of all rows and proper-prefix rows for all eight programs. |
| `division_program_rows` | `DivisionPrograms.lean:270` | Existing public statement unchanged; proof now projects the combined check. |
| `DivisionRowsFor.take`, `divisionProgram_instrs_seq` | `DivisionPrograms.lean:275`, `:293` | New private list/program facts for a proper prefix. |
| `division_program_prefix_frame` | `DivisionPrograms.lean:306` | New proved public theorem: a successful run of any proper generated-program prefix preserves `DivisionFrame` and Sail equality. |
| `division_expansion_instruction_at` | `DivisionAppend.lean:633` | New private shared bytecode lookup fact. |
| `division_replay_instruction_at` | `DivisionAppend.lean:667` | Statement unchanged; proof now uses the shared lookup fact. |

The new `division_program_prefix_frame` theorem has no `sorryAx` in its axiom output.
No approved public statement, core model definition, or hypothesis changed.
No new `bv_decide`, `native_decide`, `decide +kernel`, proof limit, or axiom was added.
No changed-module proof took more than about ten seconds.

I also proved, during exploration, that the candidate's first appended row starts at `pre`, that every candidate and replay interior pre-state retains the prefix frame, and that equal final Sail/device states give equal `finalRamWord` values.
I removed those helpers because `division_replay_complete` still has its theorem-level `sorry`, so no proved declaration used them.

The remaining obstacle is row-observation transfer in `RepresentsRows.rs1` and `.rs2`.
The prefix frame gives equality of `sourceValue` for every non-temporary operand, but the bridge from `TraceWitness.Rs1Value` and `.Rs2Value` to that source value is proved only for `HonestTrace` by `rs1Value_real` and `rs2Value_real` in `JoltConstraints/Completeness/Helpers/RegistersReadProofHelpers.lean:143` and `:175`.
The candidate and replay are `UntrustedAnswerRun`, so those theorems cannot be applied.
Reproducing their instruction case proofs in `DivisionAppend.lean` would copy an existing proof, which `AGENTS.md` requires me to stop before doing.
Generalizing the two existing facts over `Trace` in their owning file needs authorization beyond this task's two-file edit scope; I asked for that scope change and did not assume approval.
This is a proof reuse and edit-scope blocker, not evidence that `division_replay_complete` is false.

`division_replay_complete` at `DivisionAppend.lean:849` remains at its original theorem-level `sorry` with the same statement.
`lake build JoltConstraints.Soundness.Layer6.DivisionBlock` passed with 8,681 jobs.
An axiom check from a file importing only `DivisionBlock` still reports `sorryAx` for `JoltInstance.division_append_honest` through that gap.
The new prefix theorem's axiom check reports only `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`.
`git diff --check` passed before this report update.
I did not edit the other agent's Layer 5 files or commit.
