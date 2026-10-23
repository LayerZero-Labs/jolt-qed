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
