# Layer 6: the remaining plain rows

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md`, the Part B section of `methods/layer6/stage-4a-report.md`, `methods/layer6/stage-6b-report.md` and the "Proofs" section of `methods/layer6/row-step-report.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Another agent is writing the branch and `VirtualAdviceLoad` steps in new files `Soundness/Layer5/Branch.lean` and `Soundness/Layer5/AdviceLoad.lean`, editing `TerminalNextPC.lean` and `DivisionDefs.lean`; another is porting `Jal.lean` and `HostCallRegisterFrame.lean`.
Do not edit those files.
Edit `PlainRow.lean`, new Layer 6 files, and Layer 5 step files other than those named above.

## The task

Prove `plain_row_step_other` (`PlainRow.lean`) without changing its statement: every plain row kind outside the twelve division kinds appends with `PlainRowExtension`.

1. Generalize the Part B pipeline in place: `ArithmeticExecution`, `arithmetic_execution`, `arithmetic_row_observations` and `plain_row_ram` are written for `DivisionArithmeticRow`.
   Make them take a per-kind execution contract instead, so `arithmetic_plain_row_step` and the new cases come from one append proof.
   The row-step work added `representsRows_push_operands` (`RowStepCommon.lean`), which may already be the general observation lemma; reuse it rather than writing another.
2. Classify the remaining plain kinds once, as the stage 6b report lists them, and give each its ported Layer 5 step (stage 6b).
3. Stage 6b found that `ImmediatePowerMask`, `XorRotation`, `VirtualROTRI` and `VirtualROTRIW` are never emitted by an expansion.
   Either port those two families as stage 6b did (mechanical, and then no reachability fact is needed), or prove once from the expansion checker that those kinds never occur (`ExpansionFacts.immShiftOk` already rejects the two rotations); choose whichever is shorter, and say which in the report.
4. Branches and `VirtualAdviceLoad` use the other agent's new steps.
   Wire every other kind first; if those two steps are not committed yet when you reach them, stop and report, leaving only those cases open.

Keep each proof under about 60 lines.
If a kind's step is false as stated for some row, stop and report the exact case.

## Before you stop

Build `JoltConstraints.Soundness.Layer6.RowStep` (or the whole of `JoltConstraints` if the other agents' files build).
Run `#print axioms JoltInstance.plain_row_step_other`; it should not reach `sorryAx` unless you stopped at item 4.
Write `methods/layer6/plain-row-other-report.md` with each new or changed declaration (file and line), each statement change, any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.

## Corrections after the first audit (plain-row-other report)

`plain_row_ram` already handles every plain row and `ArithmeticExecution` has no division-kind premise; reuse them as they are, and generalize only the pieces that actually require `DivisionArithmeticRow`.
`RowStepCommon.lean` imports `PlainRow.lean`, so `PlainRow.lean` cannot use it: move `ExpansionState.selectedRow`, `representsRows_push_selected` and `representsRows_push_operands` from `RowStepCommon.lean` into `PlainRow.lean` with statements and proofs unchanged, delete `RowStepCommon.lean` if it is left empty, and update its importers' import lines.
You may edit `RowStepCommon.lean` and those import lines for this.
