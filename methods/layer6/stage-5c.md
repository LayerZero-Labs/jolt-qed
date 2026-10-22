# Layer 6, stage 5c: the next PC after a source's last row

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md`, `methods/layer6/reuse.md` and `methods/layer6/stage-5b-report.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Another agent works in the same checkout on Layer 5 files, `DivisionBlock.lean`, `PlainRow.lean`, and makes private lemmas public in `LastJump.lean` and `StallSuffix.lean`.
Edit only `Soundness/Layer6/TerminalNextPC.lean`, `Soundness/Layer6/ExpansionFinish.lean`, `Soundness/Layer7/StallSuffix.lean` and `Soundness/Layer7/LastJump.lean`.
In the two Layer 7 files, only make a private lemma public, rename a `stall_` lemma whose statement is not specific to stalls, or extract a general lemma from an existing proof and derive the old one from it; say which in the report.
Do not edit `JoltConstraints/model_review.md` or `methods/soundness.md`.

## Cleanup first

`last_selected_slot` (`ExpansionFinish.lean`) proves what `selected_last_represented_row` (`StallSuffix.lean`) already gives.
Delete it and use the existing lemma in `boundary_successor`.

## The task

Prove `terminal_next_unexpanded_pc` (`TerminalNextPC.lean`) without changing its statement.
Split once on the last row's instruction: JAL, JALR, a branch (`instructionFlag .Branch`), or none of these (the three hypotheses of `noncontrol_next_pc`).
Prove each kind as its own lemma in `TerminalNextPC.lean`, with the Sail side (Sail's `nextPC` after the row) and the witness side (`NextUnexpandedPC` at the row's cycle) as separate steps.
Most parts exist in Layer 7, proved for the final stable stall; several are already general.

- Every kind: `selected_last_represented_row` gives the selected slot and the real cycle; `untrusted_row_pc` and `untrusted_row_next_pc` give the row's prepared `PC` and `nextPC`.
- Not JAL, JALR or a branch.
  Sail: `noncontrol_next_pc`, with `source_compressed_of_last` for the terminal row's flag.
  Witness: `selected_terminal_nonjump_flags` (`LastJump.lean`) gives the update flags, and the update equation `nextUnexpandedPCUpdateOtherwise` gives address plus 2 or 4 as a field sum; `ordinary_row_next_pc_nonzero` (`LastJump.lean`) already does this computation inside its proof, so extract the equality from it rather than redo it.
  `terminal_link_no_wrap` turns the field sum into the 64-bit word, using `noWrap`.
- JAL.
  Sail: `stall_jal_exec_target` is general despite its name.
  Witness: `stall_jal_next_target` is general and needs exactly `nextReal`.
- JALR.
  Sail: the row's execution sets `nextPC` to `jolt_jalr_target64` of the base value; `stable_jalr_target` shows how its proof reads that value, but its statement is about stalls.
  Witness: `selected_jalr_next_target`, with the base value from `represented_last_control_read`, whose operand is not a temporary (`expanded_control_read_not_temporary`).
- A branch.
  Witness: `stall_branch_lookup_decision` computes the taken bit from the two operands, which `represented_last_control_read` supplies.
  Taken: `nextUnexpandedPCEqPCPlusImmIfShouldBranch` gives address plus immediate as a field sum, and `branch_target_toNat` gives the word.
  Not taken: the update equation, as for the ordinary kind.
  Sail: `JoltNextPCFrame.BranchTaken` and `branch_not_taken` (`JoltConstraints/nextpc_frame.lean`).
  The plan first omitted the target bound that `branch_target_toNat` needs (stage 5c report).
  The real successor supplies it: the next cycle selects a real bytecode row (as in the proof of `next_cycle_of_target`), whose address is a 64-bit word at least `RAM_START_ADDRESS` (`pc_map_ok_addresses` and `bytecode_address_ok`, as in `HonestTrace.starts_at_entry`).
  By `nextUnexpandedPCEqShift`, `NextUnexpandedPC` at the branch's cycle is that address; extract this from `next_cycle_of_target` as its own lemma rather than repeat it.
  For a taken branch, the field sum of source address and immediate then equals that word, so, with the characteristic above 2^127, the unwrapped sum is that word and Sail's wrapped target equals it.

Keep each proof under about 60 lines; if one grows past that, a lemma is missing.
Do not copy a Layer 7 proof for the general case: generalize it in place and derive the stall version from it.
If a step needs a fact that is not a short proof and is not named here or in `reuse.md`, stage it as its own lemma with `sorry`, and stop and report.

## Before you stop

Build `JoltConstraints`.
Run `#print axioms JoltInstance.expansion_finish`; it should not reach `sorryAx`.
Add a "Stage 5c" section to `methods/layer6/stage-5b-report.md` with each new or changed declaration (file and line), each lemma made public or renamed, any new `bv_decide` use, any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.
