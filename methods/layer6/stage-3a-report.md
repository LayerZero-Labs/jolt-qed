# Layer 6, stage 3a report

## Part A

Read `AGENTS.md`, `stage-2-report.md`, `reuse.md`, and `stage-3a.md` in the requested order, then checked Part A's claims against the code before editing.
The audit found no Part A blocker: `PrefixAgreement.lean` contained the six listed definitions and structures, five staged lemmas, and two proved callers, and both requested register helpers follow from the existing agreement fields.
The new import structure is acyclic.

Moved the declarations as specified:

- `JoltConstraints/Soundness/Layer6/PrefixState.lean`: `BoundaryState` (line 26), `expansionRowCount` (64), `ExpansionHasAdvice` (72), `ExpansionLive` (82), `RunExtends` (95), and `ExpansionState` (113).
- `JoltConstraints/Soundness/Layer6/BoundaryStart.lean`: `boundaryState_empty` (line 16) and `expansion_start` (30), still staged with `sorry`.
- `JoltConstraints/Soundness/Layer6/DivisionBlock.lean`: `division_block` (line 19), still staged with `sorry`.
- `JoltConstraints/Soundness/Layer6/RowStep.lean`: `row_step` (line 15), still staged with `sorry`.
- `JoltConstraints/Soundness/Layer6/ExpansionFinish.lean`: `expansion_finish` (line 16), still staged with `sorry`.
- `JoltConstraints/Soundness/Layer6/PrefixAgreement.lean`: retains the proved `boundary_step` (line 21) and `soundness_execution_prefix_agreement` (84), importing the four staged-lemma files.

A text comparison against the pre-edit files confirmed that all 13 existing declarations, including their docstrings, statements, and proofs, are unchanged.
`Registers.lean` differs only by these two proved helpers, each with a docstring and example:

| Declaration in `JoltConstraints/Soundness/Layer5/Registers.lean` | Meaning | Proof elaboration time |
| --- | --- | --- |
| `RegisterAgreementOn.mono`, line 44 | Restrict agreement to any smaller live set, retaining register presence. | 0.001405 s |
| `RegisterAgreement.toOn`, line 55 | Restrict full agreement to any live set, using `RegisterAgreementOn.mono`. | 0.002163 s |

Measured the new proofs with Lean's elaboration trace and profiler using `-j1`.
No new proof exceeds ten seconds.
No premises, restrictions, existing definitions, proof limits, `sorry`s, or `bv_decide` uses were added or changed.

`lake build JoltConstraints` passed (8805 jobs), and `git diff --check` passed.
`#print axioms JoltInstance.soundness` retains `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`, and the existing `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5` axiom.
A traversal of the compiled dependency graph confirmed that the reachable declarations directly using `sorryAx` are exactly `boundaryState_empty`, `expansion_start`, `row_step`, `division_block`, `expansion_finish`, `soundness_prover_accepts` (C), and `soundness_spoil_asserts_pass` (D), all in namespace `JoltInstance`.
Both new register helpers depend only on `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

Only Part A's named files were edited; an unrelated untracked `methods/layer6/stage-3b-report.md` was left untouched.
Part B was not attempted, no commit was made, and work stops here for Ari's review.
