# Layer 7, helper D: spoil asserts pass

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md` and `methods/layer6/reuse.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Two other agents work in the same checkout: one in `Soundness/Layer6/DivisionAppend.lean`, `DivisionDefs.lean` and `PlainRow.lean`, one in Layer 5 files other than `AssertionsBinary.lean`.
Edit only `Soundness/TopLevel.lean`, one new file `Soundness/Layer7/SpoilAsserts.lean`, and `Soundness/Layer5/AssertionsBinary.lean` for the extraction in step 2.
If the others' unfinished edits break the full build, build your own modules instead.

## Why

`JoltInstance.soundness_spoil_asserts_pass` (D, `Soundness/TopLevel.lean`) is one of Layer 7's two open helpers.
L requires that no spoil assert in the trace fails (`Trace.SpoilAssertsPass`, `JoltConstraints/language.lean`).
A spoil assert is a `VirtualAssertEQ` with a nonzero immediate; Jolt's tracer only warns when its sides differ (`jolt/tracer/src/instruction/virtual_assert_eq.rs`), so the trace's own execution does not give equal sides.
The witness's constraints do.

## The task

Prove D without changing its statement, with the work in `SpoilAsserts.lean`.
The argument: at a trace row whose instruction is `VirtualAssertEQ lhs rhs imm` with `imm ≠ 0`, the witness selects that row (`selected_represented_row`, `Layer7/StallSuffix.lean`), the assert's lookup and assert constraints force the witness's two operand values equal, and `Represents` identifies those values with `sourceValue lhs` and `sourceValue rhs` at the row's pre-state.

1. `Represents` compares operand values only for registers that are not instruction temporaries (`RepresentsRows.rs1`, `.rs2`, `Layer6/ExecutionPrefix.lean`).
   So first prove that a bytecode row with `VirtualAssertEQ` and a nonzero immediate reads no temporary.
   Such a row comes from the guest's own custom instruction, which decodes to architectural registers (`JoltConstraints/expansions.lean`, the `VirtualAssertEQ` case); expansions emit `VirtualAssertEQ` only with immediate 0 (see the comment above `Trace.SpoilAssertsPass`).
   Check both claims in the code and at the pin (`jolt/crates/jolt-program/src/expand/`), prove this once over expanded bytecode, as `expanded_control_read_not_temporary` (`StallSuffix.lean`) does for control reads, and stop and report if either claim is false.
2. `binaryAssertion_passes` (`Layer5/AssertionsBinary.lean`, private) already derives the equality from the constraints, but from register agreement.
   Extract the part that starts from the witness's two operand values as words, make it public, and have `binaryAssertion_passes` use it; then D uses the same part with the values from `Represents`.
   Do not copy the constraint argument.
3. Prove D from these over every row of the trace.

Keep each proof under about 60 lines.
If a step needs a fact that is not a short proof and is not named here or in `reuse.md`, stage it as its own lemma with `sorry`, and stop and report.

## Before you stop

Build `JoltConstraints` (or your own modules if another agent's edits break it).
Run `#print axioms JoltInstance.soundness_spoil_asserts_pass`; it should not reach `sorryAx` unless you staged a lemma.
Write `methods/layer7/helper-d-report.md` with each new or changed declaration (file and line), any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.
