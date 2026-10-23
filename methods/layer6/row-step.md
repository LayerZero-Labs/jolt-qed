# Layer 6: stage `row_step`

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md`, the Part B section of `methods/layer6/stage-4a-report.md`, and `methods/layer6/device-memory-report.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Edit `Soundness/Layer6/RowStep.lean` and new files under `Soundness/Layer6/`; in `PlainRow.lean` you may make a private lemma public in place or extract a general lemma from an existing proof and derive the old one from it.
Other agents work in Layer 5 files, `TapeSemantics.lean`, JoltBytecode `ProofSupport` files, `DivisionAppend.lean`, `DivisionPrograms.lean` and `RegistersReadProofHelpers.lean`; do not edit those.

## Why

`row_step` (`RowStep.lean`) appends one row of an unfinished source that has no internal advice.
It is the last large piece of Layer 6 and the critical path to closing soundness.
This stage is top-down: state one step per row kind, prove `row_step` from them, and stop for review before any step is proved.

## The task

1. Generalize the row-extension contract.
   `PlainRowExtension` (`PlainRow.lean`) records one appended row, its execution, and the next `ExpansionState`, and `append_expansion_row` (private) builds that state from per-row facts.
   Make that contract usable for every row kind, not only plain rows, by generalizing it in place; do not write a second append proof.
2. State, as lemmas with `sorry`, one row step for each kind `PlainRow` excludes, each returning the generalized contract:
   - LD and SD, split by whether the address is ordinary RAM (`ld_ram_step`, `sd_ram_step_agreement`, still on full `RegisterAgreement` and `OrdinaryRamAgreement`) or device memory (`ld_device_step`, `sd_device_step`, `DeviceMemory.lean`);
   - VirtualHostIO (`host_call_selected_step`, `HostCallsSucceed`);
   - JAL (`jal_step`, which needs the row's PC and prepared `nextPC`; `untrusted_row_pc` and `untrusted_row_next_pc` in `StallSuffix.lean` give them);
   - JALR (no Layer 5 step exists yet).
   Give each only hypotheses `row_step` has: the assumptions, the restrictions, the run, `state`, `unfinished` and `honestAdvice`.
   Check each against "Before staging a statement" in `AGENTS.md`, and in particular that a jump inside an unfinished expansion is possible at all; if a kind cannot occur at a non-terminal or terminal row, say so and state only what can occur.
3. Prove `row_step` from `plain_row_step`, these steps, and one lemma that a row without advice records the honest tracer's advice (none) when appended, so `honestAdvice` extends to the new run.
   Split on the row's kind once, with a small classification lemma, not on the whole instruction set.

Keep each proof under about 60 lines.
If any staged step looks false, stop and report the exact case.

## Before you stop

Build `JoltConstraints.Soundness.Layer6.RowStep` (or the whole of `JoltConstraints` if the other agents' files build).
Run `#print axioms JoltInstance.row_step`; it should reach `sorryAx` only through the staged steps and the existing staged lemmas they rely on.
Write `methods/layer6/row-step-report.md` with each staged statement (file and line), why you believe it is true, the existing lemmas each will use, and the build and axiom results.
Do not commit.
Then stop.
