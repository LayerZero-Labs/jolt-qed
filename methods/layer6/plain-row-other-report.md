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
