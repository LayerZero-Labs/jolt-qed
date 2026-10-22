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
| `division_source_advice_single` | `DivisionAppend.lean:13` | New private proof of the singleton division advice list. |
| `division_block_later_not_start` | `DivisionAppend.lean:19` | New private proof from countdown and bytecode layout. |
| `expansion_start_of_segment` | `DivisionAppend.lean:51` | New private general start-index proof. |
| `division_replay_start_flag` | `DivisionAppend.lean:90` | New private replay start-flag proof. |
| `division_replay_start_at` | `DivisionAppend.lean:148` | New private expansion-start proof. |
| `division_replay_instruction_at` | `DivisionAppend.lean:177` | New private bytecode-to-instruction proof. |
| `division_replay_advice_flag` | `DivisionAppend.lean:221` | New private advice-flag proof. |
| `division_replay_advice_before_zero` | `DivisionAppend.lean:241` | New private single-advice index proof. |
| `division_replay_first_source` | `DivisionAppend.lean:284` | New private first-row pre-state and source proof. |
| `division_replay_honest_new` | `DivisionAppend.lean:405` | Existing staged theorem proved; statement unchanged. |
| `expansion_row_remaining` | `PlainRow.lean:250` | Existing private theorem made public in place with a docstring; statement and proof unchanged. |
| `single_advice_index` | `DivisionDefs.lean:152` | Existing private theorem made public in place with a docstring; statement and proof unchanged. |
| `expansionInstructions_at` | `DivisionDefs.lean:218` | Existing private theorem made public in place with a docstring; statement and proof unchanged. |

The three visibility changes are the only changes outside `DivisionAppend.lean`.
No new `bv_decide`, `native_decide`, `decide +kernel`, axiom, proof limit, or hypothesis was added.
No individual changed module build exceeded ten seconds: `PlainRow` took 8.7 seconds, `DivisionDefs` 4.5 seconds, and `DivisionAppend` 6.3 seconds on the targeted build.

## Remaining row-construction blocker

`division_replay_rows` at `DivisionAppend.lean:349` and `division_replay_complete` at `DivisionAppend.lean:376` retain their existing theorem-level `sorry`s.
I stopped while starting `division_replay_rows`, before attempting `division_replay_complete`.
The immediate goal is to construct, for an arbitrary bytecode instruction and honest word `q`, a value `advice : instruction.RuntimeAdvice` satisfying `instruction.withRuntimeAdvice advice = patchAdviceWord q instruction`.
That value is needed to make a `TraceRow` that `appendUntrustedRow` can certify.
I tried a private definition with a VirtualAdvice branch returning `q` and a wildcard branch returning `()`, followed by a proof that the patched instruction agrees.
Lean rejected the wildcard branch because its dependent result type remained `instruction.RuntimeAdvice`, and a `split <;> rfl` proof did not close the other branch.
I removed that incomplete definition and proof.
A broad constructor split would violate the `AGENTS.md` instruction to discuss such a split first.
The proposed next step is a narrow, proved helper that constructs runtime advice and proves the patch equation by classifying VirtualAdvice separately from the remaining instructions, followed by the planned row induction.
No new `sorry` or false statement was introduced for this blocker.

## Validation and repository state

`lake build JoltConstraints.Soundness.Layer6.DivisionBlock` passed with 8,680 jobs.
`lake build JoltConstraints` also passed with 8,811 jobs while the other agent's edits were present.
The axiom check from a file importing only `DivisionBlock` reports no `sorryAx` for `division_replay_honest_new`.
`#print axioms JoltInstance.division_append_honest` still reports `sorryAx`; a direct dependency traversal identifies exactly `division_replay_rows` and `division_replay_complete` as its remaining direct `sorryAx` users.
`git diff --check` passed.
I did not edit Layer 5, `TerminalNextPC.lean`, `StallSuffix.lean`, `LastJump.lean`, or the other agent's new files.
No commit was made.
