# Closing step (c): the stopping half of Layer 7

This file is for a fresh agent with no prior context.
Read `AGENTS.md` at the repository root first; its rules apply to everything below.

## What the proof is and where this fits

This repository proves in Lean that Jolt's verifier is sound: if it accepts a witness, the claimed output is what some honest run of the program produces.
The proof is top-down: `JoltInstance.soundness` (`JoltConstraints/Soundness/soundness.lean`) uses four helpers in `JoltConstraints/Soundness/TopLevel.lean`.
Helper A, `soundness_reconstruct_trace`, builds from the witness a run of the program that agrees with the witness row by row.
A is proved from two staged statements: the execution-prefix agreement (`Soundness/Layer6/ExecutionPrefix.lean`, Layers 5b to 6, out of scope here) and the stopping lemma `soundness_stopping` (`Soundness/Layer7/Stopping.lean`).

Step (c) is the stopping lemma.
It proves three things about the run cut from the witness: it is nonempty, it ends at a stable stall (`TraceRow.StableStall`, `JoltConstraints/honest_trace.lean`), and the witness cycles after the cut change no RAM word, so the witness's final RAM matches the run.
A stable stall is the last row of an instruction that jumped to its own address and would jump there again if re-run; Jolt's tracer stops there (a16z/jolt PR #2109, head `d2995380`, `JoltInstructionRow::self_jump_repeats`).

## Starting state

Start from commit `3a31d96` on branch `feat/soundness` in `/Users/ari.biswas/Lean/jolt-qed-public`.
Check that `git status` shows no modified Lean files.
Do not use the old worktrees `/Users/ari.biswas/Lean/jolt-qed-stepc-*`; they are stale.

The previous agent was stopped mid-edit.
`Soundness/Layer7/StallSuffix.lean` and `Soundness/Layer7/TerminationStore.lean` were changed after its last build and have not been built since.
Before anything else, run `lake build JoltBytecode JoltConstraints` and the axiom audit for `soundness_stopping`.
Report the result, every error, and every `sorry` outside the five gaps listed below.
If an edit is broken, fix it only if the fix is clear and changes no statement; otherwise stop and report.

Proved, with no `sorry`:

- `Soundness/Layer7/Stopping.lean`: `soundness_stopping`, assembled from the files below.
- `Soundness/Layer7/LastJump.lean`: the cut run's last row is a JAL or JALR.
- `Soundness/Layer7/TerminationStore.lean`: a "no panic" claim forces a termination store inside the run, and `TerminationThenStall` then makes the last row a stable stall.
- `Soundness/Layer6/BytecodePC.lean`: `padding_persists`, `padding_from`.
- `Soundness/Layer7/StallSuffix.lean`: the suffix invariant `StallSuffixInvariant`, its induction `stall_suffix_replays_source`, `stable_stall_control_flow`, `noncontrol_next_pc`, `stall_suffix_no_store`, `soundness_stall_suffix_zero_ram_effects`, the JAL, branch and both architectural JALR step lemmas, and the shared helpers `stall_cycle_selected_row`, `stall_next_cycle_of_target`, `stall_next_cycle_of_remaining`, `register_unchanged_of_no_write`.

Five gaps remain, all in `StallSuffix.lean`:

1. `stall_suffix_initial`: the first cycle after the cut satisfies the invariant.
2. `stall_system_jalr_step`: the replay step for a stall ending in `JALR (.vreg _) (.vreg _)`, which only ECALL and MRET emit.
3. `expanded_jalr_operand_forms`: the operand forms a JALR row can have in the expanded bytecode.
4. `expanded_virtual_jalr_source`: a fact about JALR rows with virtual destination and virtual base.
5. `stable_stall_source_no_store`: no bytecode row at a stable stall's address has the Store flag.

## The review finding that shapes this plan

Gaps 3, 4 and 5 are facts about what each source instruction expands to.
The current code proves such facts with `Soundness/Layer7/Emission.lean`: 564 lines, about 60 per-program lemmas (`terminalNoJump_*`), and a blanket case split with `all_goals try`.
That is a second per-instruction table, parallel to one the repository already has, and the tape rebuild needs a third.
This is the duplication `AGENTS.md` forbids.

The repository already has one mechanism for facts about every expansion, and it should carry all of them:

- `ExpansionFacts.sequenceOk` (`JoltConstraints/expansion_facts.lean:96`) is a Boolean check on an expansion's instruction list: `rowsOk && shiftsOk && tempsReadAfterWrite`.
- `ExpandedOk` (`expansion_facts.lean:462`) is `sequenceOk` for a sequence, and `nativeRowOk ∧ BranchOffsetOk` for a single native row.
- `expand_ok` (`expansion_facts.lean:641`) proves `ExpandedOk` for every source instruction, one line per instruction, using per-program lemmas closed by the tactic macros `pure_rows_ok` and `native_ok`.
- `ShiftPairs` and `flatten_shiftPairs` (`JoltConstraints/trace_interface.lean:536-624`) show how a list-level check becomes a fact about the whole bytecode.

Each of gaps 3 to 5 is a property of an instruction list alone, so it does not need to know which source instruction produced the list:

- `jumpEndNoStore`: if the list's last instruction is a JAL or JALR, no instruction in it has the Store flag.
  ECALL, MRET and EBREAK end in a jump and contain no store; every other sequence does not end in a jump, so it holds trivially.
- `sequenceJalrsVirtual`: every JALR inside a sequence is `JALR (.vreg _) (.vreg _)`.
  JALRs with an architectural base come only from native JALR rows.
- `virtualJalrBaseUnwritten`: for every `JALR (.vreg _) (.vreg b)` in the list, no instruction in the list writes `b`.

The tape rebuild needs one more property of the same kind, and it belongs in the same extension:

- `advicePairsOk`: every `VirtualAdviceLoad dst w` with `w.toNat < 8` has `dst = sideEffectingRdZeroDst rd` for some `rd`, is not the list's last instruction, and is immediately followed by `VirtualMULI (sideEffectingRdZeroDst rd) (adviceReadSource rd) (slliMultiplier (BitVec.ofNat 6 (64 - 8 * w.toNat)))`.
  This is the shape of `narrowAdviceProgram` (`Soundness/Layer5/AdviceExpansion.lean:23`).
  Every other sequence contains no such load, so it holds trivially.
  Also make sure no native row is a narrow `VirtualAdviceLoad`: if `nativeRowOk` does not already imply it, add it to the native check.

## Plan

### Part 1: extend the existing checker (stop for review after staging)

1. Make `sequenceOk` safe to extend.
   Five places take it apart by position (`ok.1.2` and similar): `expansion_facts.lean:753`, `trace_interface.lean:480` and `:572`, `Soundness/Layer5/HostCallExpansion.lean:80`, and `Emission.lean:403`, which is deleted in step 6.
   Add named projection lemmas (`sequenceOk_rowsOk`, `sequenceOk_shiftsOk`, `sequenceOk_tempsReadAfterWrite`) and use them at those sites.
2. Define `jumpEndNoStore`, `sequenceJalrsVirtual`, `virtualJalrBaseUnwritten` and `advicePairsOk` in `expansion_facts.lean`, next to `shiftsOk`, and add them to `sequenceOk`.
   If the native JALR operand forms (architectural base, with an architectural destination or the x0 rewrite's virtual destination) are not already implied by `nativeRowOk`, add that check to the native case in the same way.
3. Add the new definitions to the simp sets of `pure_rows_ok` and `native_ok`, so the existing per-program lemmas and `expand_ok` prove the new conjuncts with no new table.
   Measure the elaboration time of `expansion_facts.lean` before and after; report both.
4. Add one lift lemma: for `expand_instruction source = some rows`, the rows' instruction list satisfies `sequenceOk` when the source is a sequence, and is a single native row satisfying `nativeRowOk` otherwise.
   `stamp_sequence` (`JoltConstraints/program.lean:144`) keeps the instruction list in order; `stamp_sequence_instruction_member` in `StallSuffix.lean` may help, otherwise delete it.
5. Move `expanded_same_source_rows` (`StallSuffix.lean:163`) to `JoltConstraints/program_facts.lean`, next to `pc_map_ok_distinct_addresses` (`program_facts.lean:567`).
   It is a bytecode fact: in an accepted program, two rows at one address belong to one source instruction's expansion.

Stage steps 2 and 4 and the restated gaps of Part 2 with `sorry`, build, and stop for Ari's review before changing any existing proof.
These files are shared with the completeness proof; no completeness theorem statement may change.

### Part 2: the three bytecode gaps

6. Prove gaps 3, 4 and 5 from the lift lemma, `expanded_same_source_rows`, `stable_stall_control_flow` and `sequenceRowOk` (`expansion_facts.lean:29-35`, which keeps branches out of sequences, so a branch stall is always a native row).
   Restate gap 4 as what its user, `stall_system_jalr_step`, needs: for a row `JALR (.vreg _) (.vreg b)`, no bytecode row at the same address writes `b`.
   The current statement's extra conclusion, that the source is ECALL or MRET, has no other use; drop it and list the change in your report.
   Then delete `Emission.lean`, and move `expanded_arch_jalr_singleton` (used at `StallSuffix.lean:2113`) to rest on `sequenceJalrsVirtual`.

### Part 3: the two replay gaps

7. `stall_suffix_initial`: split on `stable_stall_control_flow`.
   The JAL and branch cases are `stall_suffix_initial_jal` and `stall_suffix_initial_branch`, which exist but are unused.
   Add the JALR case from `represented_last_jalr_base` and `stall_next_cycle_of_target`.
8. `stall_system_jalr_step`: use gap 4 with `register_unchanged_of_no_write` for the base, `stall_next_cycle_of_remaining` for the rows inside the expansion (constraint 18), and `stall_next_cycle_of_target` for the final JALR.

Parts 2 and 3 are independent and may be done in parallel, each in its own worktree under `/Users/ari.biswas/Lean/`.

### Part 4: cleanup before reporting

9. Split `stall_jalr_written_base_step` (124 lines) into named lemmas.
10. Use or delete `selected_source_after_stable`, `represented_read_register_succ` and `stamp_sequence_instruction_member`.
11. Update "Proofs owed" in `JoltConstraints/model_review.md` and the step (c) status line in `methods/soundness.md`.

## Final report

- The elaboration time of every declaration you added or changed, and of `expansion_facts.lean` before and after Part 1.
- The axiom audit for `JoltInstance.soundness_stopping` and `JoltInstance.soundness_reconstruct_trace`: `soundness_stopping` must be free of `sorryAx`; A may carry it only through `soundness_execution_prefix_agreement`.
- `lake build JoltBytecode JoltConstraints`.
- Every staged statement you changed, with the reason.

Then stop.

## Out of scope

- The tape rebuild (`Soundness/Layer7/TapeRebuild.lean`, branch `feat/layer7-tape-rebuild`, worktree `/Users/ari.biswas/Lean/jolt-qed-tape-rebuild`) is a separate task; do not edit it.
  It uses `advicePairsOk` from your Part 1 and lifts it to the bytecode itself; you only define the check and make `expand_ok` prove it.
- `soundness_execution_prefix_agreement` and helpers C and D.

## Sources

- Constraints: `JoltConstraints/Constraints/`, with the numbered list in `JoltConstraints/constraints.md`; constraint 18 is `NextPCEqPCPlusOneIfInline.lean`.
- Jolt's Rust code: `/Users/ari.biswas/Work-with-A16z/jolt`, pinned at `8bbb2357`; read files with `git -C /Users/ari.biswas/Work-with-A16z/jolt show 8bbb2357:<path>`.
- Expansions: `crates/jolt-program/src/expand/control_flow/{ecall,mret,ebreak}.rs` at the pin.
- Stopping rule: PR #2109, `gh pr diff 2109 --repo a16z/jolt`.
- The plan and status: `methods/soundness.md`; the remaining gaps: "Proofs owed" in `JoltConstraints/model_review.md`.
