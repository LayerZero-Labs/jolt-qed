# Agent 2: JALR and the six branches

Read `README.md` in this directory first, then `AGENTS.md`, then agent 1's Phase 0 report `methods/layer6/phase0_report.md`.
Start only after Ari has approved Phase 0.
Work in a worktree under `/Users/ari.biswas/Lean/` on a branch `layer6-agent-2`, created from the commit named in the Phase 0 report.

## Your task

Prove the `RowStep` lemmas agent 1 staged for JALR (`Layer5/Jalr.lean`) and for BEQ, BNE, BLT, BGE, BLTU and BGEU (`Layer5/Branch.lean`).
Each says: from `PrefixState n run`, a real cycle `n` whose selected row is that instruction, and a run not ended by a stable stall, the run extends by one row with `PrefixState (n + 1)`.

## What each step must show

- The run executes the row: `execWithTapeAnswer` on the instruction from the prepared pre-state succeeds.
  A branch writes no register and changes only nextPC; a JALR writes its link and sets nextPC to the target.
- The witness row matches the run row: PC, Rs1Value, Rs2Value and RamAddress.
  RamAddress is 0, since these rows do not access memory: `ramAddress_zero_of_not_load_store` (`Layer3/Access.lean:15`).
- The next cycle's state:
  - register agreement on the live set, with JALR's destination made live and unchanged registers carried over;
  - RAM and device agreement unchanged, since nothing is written: `ram_zero_effects` (`Layer1/Ram.lean:93`) and `OrdinaryRamAgreement.noAccess` (`Layer5/RamAgreement.lean:102`);
  - when the next cycle is real, the next selected row is the one at the run's new nextPC.
  JALR and branches always end their source instruction, so this is agent 1's `prefix_source_boundary`.

## Facts to reuse

Agent 1 moves these into `Layer6/ControlRows.lean` in Phase 0; use the names the Phase 0 report gives.

- JALR:
  - `selected_jalr_lookup_target` and `selected_jalr_next_target` (lookup output and next unexpanded PC);
  - `selected_jump_link_write_value` (the link the row writes, using `NextPCNoWrap`, `assumptions.pcNoWrap`);
  - `tape_jalr_target` (the run's nextPC);
  - `selected_operand_register`, `register_unchanged_of_no_write`.
- Branches:
  - the branch flags, table decision and lookup decision (`stall_branch_control_flags`, `stall_branch_table_decision`, `stall_branch_lookup_decision` before renaming);
  - `shouldBranch_eq_lookupOutput` (`Layer4/Outputs.lean:41`), and the comparison tables in `Layer4/Comparison.lean`;
  - `branch_instruction_of_flag`, and `branch_target_ne_zero` (`Layer7/LastJump.lean:115`, which agent 1 may also move).
- Both:
  - `RegisterAgreement.setNextPC` (`Layer5/Jal.lean:81`, documented as shared with branches);
  - `jal_step` (`Layer5/Jal.lean:95`) as the model for a control-flow step lemma.

Layer 7's stall proofs covered only the taken, zero-offset branch and the self-jumping JALR.
You need every case: taken and not taken, any offset, and any JALR operand form allowed by `expanded_jalr_operand_forms`.
The constraints: 15 (jump target), 16 (branch target), 17 (otherwise PC + 4 or + 2), and 14 (link write).

## Files you own

`Layer5/Jalr.lean`, `Layer5/Branch.lean`, and any new helper file under `Layer5/` whose name starts with `Jalr` or `Branch`.
Request any change to `ControlRows.lean` from agent 1.

## Report

Per-declaration timings, any helper hypotheses you added (standing approval, see `AGENTS.md`), any new `bv_decide` use, and your branch's head commit.
