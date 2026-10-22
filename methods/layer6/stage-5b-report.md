# Layer 6 stage 5b audit report

I read `AGENTS.md`, `methods/layer6/reuse.md`, and `methods/layer6/stage-5b.md` in that order and checked the proposed statements against the current Lean code and Jolt at pin `5def437f` before editing.
The proposed `terminal_next_unexpanded_pc` statement is false without a real successor cycle, so I stopped before staging it or changing any Lean file.

Consider a terminal `JAL +0` row at a nonzero accepted source address such as `0x80000000`, followed by padding.
Its certified Sail execution leaves `postState.sail.regs.get? Register.nextPC = some 0x80000000`, as `stall_jal_exec_target` in `JoltConstraints/Soundness/Layer7/StallSuffix.lean` shows.
The terminal countdown is zero, and `pcNoWrap` holds at this address.
At the JAL cycle, `nextUnexpandedPCEqShift` in `JoltConstraints/Constraints/NextUnexpandedPCEqShift.lean` makes `witness.NextUnexpandedPC` equal the padding successor's `UnexpandedPC`, which is zero.
If the JAL is at the final witness cycle, the same shift equation sets `NextUnexpandedPC` to zero directly.
`RepresentsRows` in `JoltConstraints/Soundness/Layer6/ExecutionPrefix.lean` constrains only observations of retained run rows and does not require the successor to be real.
The jump constraint does not repair this case: `ShouldJump = Jump * (1 - NextIsNoop)` is zero before padding, so `nextUnexpandedPCEqLookupIfShouldJump` does not force the JAL target.
The existing `stall_jal_next_target` in `JoltConstraints/Soundness/Layer7/StallSuffix.lean` explicitly requires `nextReal`, as does `selected_jalr_next_target`.
Jolt's witness extractor likewise reads `NextUnexpandedPc` from the successor row and uses zero for a missing successor in `jolt/crates/jolt-witness/src/witnesses/pc.rs` (`NextUnexpandedPc::extract`); its cycle window supplies a default padding row in `jolt/crates/jolt-witness/src/backend/trace/cycle.rs` (`walk_cycles`).

The missing fact is that cycle `run.rows.size` exists and is real.
That condition is already available in the proposed `boundary_successor` step, and would have to be passed into a revised terminal-PC lemma before it can prove that caller.
I did not change a statement or stage a `sorry` because `AGENTS.md` requires stopping when a staged statement would be false.
No declaration was added or changed, no build or axiom check was run, and no commit was made.
The existing concurrent edits to `DivisionBlock.lean` and `PlainRow.lean` were left untouched.

## Results after the corrected successor premise

I reread item 1 of `methods/layer6/stage-5b.md` after commit `90e7c2d` and checked its corrected statement against the four row kinds before staging it.
For a noncontrol row, `noncontrol_next_pc` supplies Sail's post-state address and `terminal_link_no_wrap` supplies the field comparison.
For JAL, the real successor makes the jump lookup active; `stall_jal_next_target` has the same successor requirement and agrees with Sail's wrapped target.
For JALR, `selected_jalr_next_target` has that requirement, and `expanded_control_read_not_temporary` allows the represented architectural base to determine Sail's target.
For a branch, the represented operands determine the branch decision and `branch_target_toNat` handles the accepted target address.
The corrected statement has no counterexample among these cases; the padding case described above is excluded by `nextReal`.
These checks used the Lean lemmas in `StallSuffix.lean` and Jolt's tracer and witness PC/flag code at the pinned `5def437f` commit.

The following declaration times are Lean asynchronous proof elaboration times in seconds.
I measured the Layer 6 files with `lake env lean -j1 -Dtrace.Elab.async=true -Dtrace.profiler=true -Dtrace.profiler.threshold=0`.
I measured `next_cycle_of_target` with the same profiler enabled only around that declaration in a temporary copy of `StallSuffix.lean`.

- `JoltConstraints/Soundness/Layer6/TerminalNextPC.lean:19`: `terminal_next_unexpanded_pc` is staged with one named `sorry`; 0.000817 s.
- `JoltConstraints/Soundness/Layer6/BytecodePC.lean:101`: `selected_interior_current_remaining` is the proved shared extraction; 0.073795 s.
- `JoltConstraints/Soundness/Layer6/BytecodePC.lean:149`: `selected_interior_predecessor` retains its statement and now uses that extraction; 0.005464 s.
- `JoltConstraints/Soundness/Layer7/StallSuffix.lean:467`: the former private `stall_next_cycle_of_target` was renamed and made public as `next_cycle_of_target`, without changing its statement or proof; 0.072918 s.
- `JoltConstraints/Soundness/Layer6/ExpansionFinish.lean:14`: `expanded_endpoint_terminal` proves the bytecode countdown reaches zero; 0.147057 s.
- `JoltConstraints/Soundness/Layer6/ExpansionFinish.lean:60`: `last_selected_slot` locates the represented final-row selector; 0.081829 s.
- `JoltConstraints/Soundness/Layer6/ExpansionFinish.lean:105`: `boundary_successor` proves the real next cycle selects a source-start row at Sail's next address; 0.045015 s.
- `JoltConstraints/Soundness/Layer6/ExpansionFinish.lean:164`: `expansion_at_boundary` proves the completed block's last row is terminal; 0.367373 s.
- `JoltConstraints/Soundness/Layer6/ExpansionFinish.lean:229`: `expansion_ready` proves the boundary's next-step field; 0.122755 s.
- `JoltConstraints/Soundness/Layer6/ExpansionFinish.lean:298`: `expansion_finish` is proved without changing its statement; 0.006608 s.

`JoltConstraints.lean:90` imports the new file.
No new `bv_decide`, `native_decide`, heartbeat increase, or unnamed proof gap was introduced.
No new proof took over ten seconds to elaborate.
`lake build JoltConstraints` succeeded with 8808 jobs after the final proof edit.
`#print axioms JoltInstance.expansion_finish` reports `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`.
The endpoint, last-selector and boundary-terminal helpers have no `sorryAx`; `boundary_successor` and `expansion_ready` reach it through `terminal_next_unexpanded_pc` alone.
I made no commit and did not edit Agent 1's concurrent Layer 5, `DivisionBlock.lean`, `PlainRow.lean`, or `LastJump.lean` work.

## Stage 5c

I reread `AGENTS.md`, `methods/layer6/reuse.md`, this report, and `methods/layer6/stage-5c.md` in order, and checked the proposed uses against the Lean declarations and Jolt at pin `5def437f`.
The plan's taken-branch step is incomplete: `branch_target_toNat` in `JoltConstraints/Completeness/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean:98` requires both the source and the wrapped target to be at least `RAM_START_ADDRESS`.
The selected current bytecode row supplies the source bound, but the plan does not name a fact deriving the target bound from the real successor and the field-valued next-PC equation.
The preliminary audit missed this extra premise; I found it while working on the branch case.
I found no counterexample to `terminal_next_unexpanded_pc`, but I have not proved its branch case and have not treated the theorem as closed.
Jolt's pinned witness extractor reads the next unexpanded PC from the successor row in `jolt/crates/jolt-witness/src/witnesses/pc.rs:99-113`, and the real-successor flags are defined in `jolt/crates/jolt-witness/src/witnesses/flags.rs:82-139`.

The following are the new or changed declarations, with Lean asynchronous proof elaboration times where their proofs changed:

- `JoltConstraints/Soundness/Layer6/ExpansionFinish.lean:64`: `boundary_successor` now uses `selected_last_represented_row` directly; 0.161 s.
- `JoltConstraints/Soundness/Layer6/ExpansionFinish.lean`: the duplicate `last_selected_slot` was deleted.
- `JoltConstraints/Soundness/Layer7/LastJump.lean:174`: `ordinary_row_next_pc_value` extracts the ordinary field-sum equality; 0.247 s.
- `JoltConstraints/Soundness/Layer7/LastJump.lean:198`: `ordinary_row_next_pc_nonzero` keeps its statement and derives its equality from that helper; 0.195 s.
- `JoltConstraints/Soundness/Layer7/LastJump.lean:513`: `selected_terminal_nonjump_flags` was made public in place, without changing its proof; 0.034 s.
- `JoltConstraints/Soundness/Layer6/TerminalNextPC.lean:15`: `terminal_last_setup` extracts the selected final slot and prepared registers; 0.169 s.
- `JoltConstraints/Soundness/Layer6/TerminalNextPC.lean:58`: `terminal_direct_execution` extracts direct Sail execution; 0.074 s.
- `JoltConstraints/Soundness/Layer6/TerminalNextPC.lean:79`: `terminal_noncontrol` is proved; 0.810 s.
- `JoltConstraints/Soundness/Layer6/TerminalNextPC.lean:153`: `terminal_jal` is proved; 0.367 s.
- `JoltConstraints/Soundness/Layer6/TerminalNextPC.lean:198`: `terminal_jalr` is proved; 0.321 s.
- `JoltConstraints/Soundness/Layer6/TerminalNextPC.lean:257`: `terminal_branch` is a named, staged obligation with one `sorry`; 0.001 s.
- `JoltConstraints/Soundness/Layer6/TerminalNextPC.lean:289`: `terminal_next_unexpanded_pc` retains its statement and now follows from the four cases; 0.261 s, conditional on `terminal_branch`.

In `JoltConstraints/Soundness/Layer7/StallSuffix.lean`, I made `stall_jal_next_target` at line 604, `stall_jal_exec_target` at line 656, `stall_branch_lookup_decision` at line 784, `stall_branch_runs` at line 1341, and `tape_jalr_target` at line 1752 public in place, without changing their statements or proofs.
No `stall_` lemma was renamed.
Agent 1 also made `nonterminal_virtual_row_pc_plus_one` and `nonterminal_at_last_cycle_impossible` public in `LastJump.lean`; those visibility edits were concurrent, not mine.
I left Agent 1's Layer 5, `DivisionBlock.lean`, `PlainRow.lean`, and other report changes untouched.

`lake build JoltConstraints` succeeded with 8808 jobs, and `git diff --check` passed for the four allowed Lean files.
`#print axioms JoltInstance.expansion_finish` still reports `sorryAx`, inherited through `terminal_next_unexpanded_pc` from the staged `terminal_branch` obligation.
No new `bv_decide`, `native_decide`, heartbeat increase, or proof over ten seconds was introduced.
I did not edit `JoltConstraints/model_review.md` or `methods/soundness.md`, and I made no commit.

## Stage 5c, branch case

I checked the branch item of `methods/layer6/stage-5c.md` against the Lean selector, branch lookup, row-validity, Sail execution, and next-PC lemmas before editing.
I also checked Jolt's pinned `5def437f` implementations in `crates/jolt-witness/src/witnesses/pc.rs` (`NextUnexpandedPc::extract`), `crates/jolt-witness/src/witnesses/flags.rs` (`ShouldBranch::extract`), `crates/jolt-program/src/expand/metadata.rs` (`stamp_sequence_metadata`), and `tracer/src/instruction/format/format_b.rs` (`FormatB::parse`).
The real successor supplies an accepted bytecode address, and the signed 13-bit branch offset is recorded by `JoltInstructionRow.Valid.branch`; I found no incorrect plan claim.

`JoltConstraints/Soundness/Layer6/TerminalNextPC.lean:641` now proves `terminal_branch` with its staged statement unchanged.
The common terminal fallthrough calculation was extracted as `terminal_fallthrough_witness` at `TerminalNextPC.lean:80`, and `terminal_noncontrol` at `:110` now uses it without changing its statement.
The new branch helpers are `terminal_real_successor_address` at `:279`, `terminal_branch_target_cast` at `:309`, `terminal_branch_real_target` at `:335`, `terminal_branch_decision` at `:392`, `terminal_taken_branch_field` at `:421`, `terminal_taken_branch_target_ram` at `:451`, `terminal_branch_untaken` at `:477`, `terminal_branch_taken` at `:519`, and `terminal_branch_prepared_decision` at `:590`.
Each helper is used by the staged theorem's proof path; the taken case uses the real successor's lower address bound to rule out 64-bit branch-target wrap before applying `branch_target_toNat`.
No existing theorem statement, definition, or hypothesis changed.

`JoltConstraints/Soundness/Layer7/StallSuffix.lean:467` adds `next_cycle_address` by extracting the general address relation from `next_cycle_of_target`, whose statement at `:506` is unchanged and whose proof now derives from it.
The former private `stall_real_slot_index` was made public and renamed `real_slot_index` at `StallSuffix.lean:534`, with its statement and proof unchanged; its existing caller was updated.
`represented_last_branch_registers` at `StallSuffix.lean:2787` generalizes the operand extraction previously embedded in `stall_suffix_initial_branch`; the latter retains its statement at `:2866` and now uses the new lemma.
No `LastJump.lean` edit was needed.

`lake build JoltConstraints` passed with 8,810 jobs, and `git diff --check` passed.
`#print axioms JoltInstance.expansion_finish` reports `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`, and `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5`; it does not reach `sorryAx`.
There is no new `bv_decide` tactic call, `native_decide`, raised proof limit, or `sorry` in the changed Lean files.
The existing `branch_target_toNat` proof's `bv_decide` axiom is newly reachable from `expansion_finish` through the taken-branch proof.
Per-declaration profiling found no proof over ten seconds; the slowest changed proof was `represented_last_branch_registers` at 5.168 seconds.
I did not edit Agent 1's division files or `PlainRow.lean`, and I made no commit.
