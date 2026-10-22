# Layer 6, stage 5b: close a source expansion

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md` and `methods/layer6/reuse.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.
Another agent works in the same checkout on Layer 5 files, `DivisionBlock.lean`, `PlainRow.lean` and possibly `PrefixAgreement.lean`.
Edit only `Soundness/Layer6/ExpansionFinish.lean`, one new file `Soundness/Layer6/TerminalNextPC.lean`, `Soundness/Layer6/BytecodePC.lean`, `Soundness/Layer7/StallSuffix.lean` and `JoltConstraints.lean` (to import the new file).
In the last two Lean files, only make a private lemma public in place or extract a shared lemma from an existing proof; say which in the report.
Do not edit `JoltConstraints/model_review.md` or `methods/soundness.md`; Claude updates them after both agents report.

## Why

`expansion_finish` turns `ExpansionState` with all of a source's rows done into `BoundaryState`.
Most fields copy over.
The hard one is `ready`: when the next witness cycle is real and the last row is not a stable stall, the witness must select the first row of the source at the address in Sail's `nextPC` after the last row.
This is the step between two source instructions, and every program crosses it.

## The task

Follow the top-down rule in `AGENTS.md`: stage the hard lemma, prove its caller and the short lemmas, and stop.

1. Stage `terminal_next_unexpanded_pc` with `sorry` in the new file `TerminalNextPC.lean`.
   It says: at the witness cycle of a run's last row, when that row ends its source (its `virtual_sequence_remaining.getD 0` is 0), Sail's `nextPC` after the row holds some `address`, and the witness's `NextUnexpandedPC` at that cycle is `(address.toNat : F)`.
   It takes the run's execution certificate (`last ∈ run.rows.back?`), `RepresentsRows witness run.toTrace`, the context, the equations, `joltField` and `assumptions.pcNoWrap`; it needs no restriction and no honest advice.
   It also needs the next cycle `run.rows.size` to exist and be real (`IsNoop` not 1, as `nextReal` in `stall_jal_next_target`).
   Without it the statement is false: before padding, `ShouldJump = Jump * (1 - NextIsNoop)` is 0, so a terminal `JAL +0` has `NextUnexpandedPC` 0 while Sail's `nextPC` is its own address (stage 5b report).
   Its proof, in a later stage, splits the last row into four kinds:
   - not JAL, JALR or a branch: `noncontrol_next_pc` and `terminal_link_no_wrap` (`StallSuffix.lean`);
   - JAL: the lookup computes the wrapped target (`stall_jal_lookup_target`, `jal_step`);
   - JALR: the represented `rs1`, which is not a temporary (`expanded_control_read_not_temporary`);
   - a branch: the represented operands decide the branch, and the target does not wrap (`branch_target_toNat`).
   Check the statement against these four cases before staging it, as "Before staging a statement" in `AGENTS.md` asks.
   If you find a case where it is false, stop and report the exact case.
2. Prove `boundary_successor` in `ExpansionFinish.lean` from `terminal_next_unexpanded_pc`: under the same hypotheses, plus a real next cycle (`IsNoop` 0) at cycle `run.rows.size`, the witness selects at that cycle a slot `next + 1` with `run.bytecode[next].address = address` and `run.bytecode[next].starts_source`.
   - The next cycle selects padding or a row at `address`: `stall_next_cycle_of_target` (private in `StallSuffix.lean`; make it public, and rename it `next_cycle_of_target` if no other file uses the old name).
     The real next cycle excludes padding, and `stall_cycle_selected_row` gives the row's index.
   - That row starts its source.
     The last row is terminal, so its `DoNotUpdateUnexpandedPC` flag is 0, and `mustStartSequenceFromBeginning` then rules out an interior next row.
     `selected_interior_predecessor` (`BytecodePC.lean`) already contains this argument: extract the part that derives `remaining ≠ 0` for the current row from an interior next row as its own lemma, and have `selected_interior_predecessor` use it.
   - `selected_represented_row` (`StallSuffix.lean`) gives the last row's selected slot.
3. Prove, in `ExpansionFinish.lean`, the bytecode fact that the last row of a source's block ends it: in expanded bytecode, if `first` starts a source, the row at `first + remaining(first)` exists and has remaining 0.
   `BytecodeLayout.next` (`expand_program_layout`) counts down by one per row; check `program_facts.lean` (`expand_instruction_countdown`, `valid_run_countdown`) for an existing form first.
4. Prove `expansion_finish` from these, without changing its statement:
   - `represents`, `real`, `noEarlierStop` and `terminationWord` copy over, and `honestAdvice` is the hypothesis;
   - `atBoundary`: `ordered` at the last offset gives the last row's index `first + remaining(first)`, then step 3;
   - `registers`: with all rows done, `ExpansionLive` holds only for registers that are not temporaries (`RegisterAgreementOn.mono`);
   - `ready`: `boundary_successor`, then `NextStep` with `pre = advance_pc address (source_is_compressed run.bytecode next) last.postState`, and the hypothesis and `noEarlierStop` for its other two fields.

Keep each proof under about 60 lines; if one grows past that, a lemma is missing.
If a step needs a fact that is not a short proof and is not named here or in `reuse.md`, stage it as its own lemma with `sorry`, and stop and report.

## Before you stop

Build `JoltConstraints`.
Run `#print axioms JoltInstance.expansion_finish`; it should reach `sorryAx` only through `terminal_next_unexpanded_pc`.
Write `methods/layer6/stage-5b-report.md` with each new or changed declaration (file and line, staged or proved), each private lemma made public or renamed, any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.
