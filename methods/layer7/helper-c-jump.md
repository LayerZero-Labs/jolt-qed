# Layer 7, helper C: the trace ends in a jump

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md`, then `methods/layer7/helper-c-report.md`, section "1. Last jump and branch stalls", which gives the argument and the lemmas.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Edit `Soundness/Layer7/ProverAccepts.lean`; in `Soundness/Layer7/StallSuffix.lean` and `Soundness/Layer7/LastJump.lean` you may make a private lemma public in place, or extract a general lemma from an existing proof and derive the old one from it; say which in the report.
Other agents work in Layer 5 files, `DivisionAppend.lean`, `DivisionPrograms.lean` and `Completeness/Helpers/RegistersReadProofHelpers.lean`; do not edit those.

## Why

Helper C (`soundness_prover_accepts`) is proved from three parts; one is proved, and this is the hardest of the other two.
`represented_trace_ends_in_jump` says a represented completed trace is empty or ends in JAL or JALR, which Jolt's prover checks (`ProverConfig::derive_from_dimensions`).

## The task

Prove `represented_trace_ends_in_jump` without changing its statement.
The trace ends in a stable stall; `stable_stall_control_flow` (`StallSuffix.lean`) says that row is a JAL, a JALR or a branch.
JAL and JALR are jumps.
For a branch, derive a contradiction, as the report argues:

1. The stalled branch is taken with offset zero (`stall_branch_model_target`, private), so its constrained next unexpanded PC is its own source address (`stall_branch_replay_target`, private), which is nonzero.
2. If the trace's last row is the witness's last cycle, `nextUnexpandedPCEqShift` requires that PC to be zero.
3. If the next cycle is padding, its unexpanded PC is zero (`unexpanded_zero_of_padding`, private in `LastJump.lean`), so the same shift equation gives a contradiction.
4. If the next cycle is real, it replays the same branch (`stall_suffix_initial_branch`, then `stall_branch_step`), so induct forward over the witness's cycles until one of the two cases above.

The report found that this branch route does not need `NextPCNoWrap`, which C does not have; the general `stall_suffix_replays_source` needs it, so do not call that.
Prove the forward replay as its own lemma, stated over the witness's cycles from the trace's end, so the induction is in one place.
Keep each proof under about 60 lines.
If a step needs a fact that is not a short proof and is not named here or in the report, stage it as its own lemma with `sorry`, and stop and report.

## Before you stop

Build `JoltConstraints` (or your own modules if another agent's edits break it).
Run `#print axioms JoltInstance.represented_trace_ends_in_jump`; it should not reach `sorryAx`.
Add an "Ends in a jump" section to `methods/layer7/helper-c-report.md` with each new declaration (file and line), each lemma made public, any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.
