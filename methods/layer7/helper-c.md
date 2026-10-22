# Layer 7, helper C: Jolt's prover accepts the trace (staging)

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md`, `methods/layer7/helper-d-report.md`, and the Layer 7 section of `methods/soundness.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Other agents work in the Layer 6 division files and `PlainRow.lean`; do not edit those.
Edit only `Soundness/TopLevel.lean` and one new file `Soundness/Layer7/ProverAccepts.lean`.

## Why

`JoltInstance.soundness_prover_accepts` (C, `Soundness/TopLevel.lean`) is Layer 7's last open helper.
L requires that Jolt's prover accepts the rebuilt trace: `Trace.prover_config` (`JoltConstraints/prover_config.lean`) is `some`.
C is an area where a staged statement may turn out false, so this stage only states its parts and proves C from them; a later stage proves the parts.

## The task

`deriveFromDimensions` succeeds when three things hold; stage each as its own lemma with `sorry` in `ProverAccepts.lean`, and prove C from them.

1. The trace ends in a jump: its last row's instruction is JAL or JALR (`ends_in_jump`), or it has no rows.
   `soundness_last_row_is_jump` (`Layer7/LastJump.lean`) proves this for the witness's last real row before padding, but C's trace is cut at its first stable stall, and the witness may repeat that stall before the padding (`Layer7/StallSuffix.lean`).
   Find how the stopping proof (`Layer7/Stopping.lean`) relates the trace's last row to the witness's last real row, and state the part with the hypotheses that relation needs.
   A stable stall can also be a branch (`stable_stall_control_flow`); check whether the constraints exclude a trace that ends in a branch stall, and if they do not, stop and report it with the exact case.
2. The padded length fits: `checkedTraceLength` of the row count succeeds and is at most `joltInstance.max_padded_trace_length`.
   This is where the verifier's 256-row floor (`ConstraintContext.traceLengthFloor`) and `NoMaxLengthTrace` enter; the stage-1 audit of C's two former counterexamples is in `JoltConstraints/model_review.md` under "Proofs owed".
3. The RAM size computes: `checkedRamSize` succeeds, which needs every nonzero RAM address of the trace to be at least the layout's lowest address, and the image end and the rounding not to overflow.
   `Represents` identifies each row's RAM address with the witness's (`RepresentsRows.ramAddress`); find which constraint bounds the witness's address, and say in the report whether the bound comes from the constraints or needs a restriction.

C's statement and hypotheses must not change.
If a part needs a hypothesis C does not have, stop and report it; do not add it.
Check each staged statement against "Before staging a statement" in `AGENTS.md`.

## Before you stop

Build `JoltConstraints` (or your own modules if another agent's edits break it).
Run `#print axioms JoltInstance.soundness_prover_accepts`; it should reach `sorryAx` only through the three staged parts.
Write `methods/layer7/helper-c-report.md` with each staged statement, why you believe it is true or what makes it doubtful, the existing lemmas each part will use, and the build and axiom results.
Do not commit.
Then stop.
