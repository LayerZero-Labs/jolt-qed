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
