# Layer 6, stage 2: split one source instruction into rows

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md` and `methods/layer6/stage-1-report.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
This stage is top-down: state the pieces with `sorry`, prove `boundary_step` from them, build, and stop for review.
Prove nothing else.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.

## The target

`JoltInstance.boundary_step` (`JoltConstraints/Soundness/Layer6/PrefixAgreement.lean:82`) executes one whole source instruction from a `BoundaryState` (line 28).
Do not change its statement, `BoundaryState`, or `soundness_execution_prefix_agreement`.

Facts the design rests on, each checked in the code:

- Inside an expansion, the witness's rows are consecutive and real.
  A row that does not end its source instruction is never at the last witness cycle and never followed by padding (`nonterminal_at_last_cycle_impossible` and `nonterminal_before_padding_impossible`, `Soundness/Layer7/LastJump.lean:350,401`, private for now), and the next cycle selects the next bytecode slot (`selected_next_of_remaining`, `Soundness/Layer6/BytecodePC.lean:67`).
- `VirtualAdvice` rows occur only in the eight division expansions (`divProgramAuto`, `divuProgramAuto`, `divwProgramAuto`, `divuwProgramAuto`, `remProgramAuto`, `remuProgramAuto`, `remwProgramAuto`, `remuwProgramAuto`, `JoltBytecode/JoltISA/ExpansionsAutomated.lean`), one per expansion; guest programs have no source-level `VirtualAdvice` (`JoltCustomInstruction`, `JoltConstraints/expansion_helpers.lean:17`).
  With `rd = x0` a division expands to a single `ADDI` with no advice row.
- Those eight expansions contain no load, store, jump, branch, HostIO or tape read.
  So no row of theirs uses a restriction that concerns an execution step.
  Four restrictions do, and they are stated over `UntrustedAnswerRun.NextStep`, which needs honest advice: `TracerAddressChecks`, `HostCallsSucceed`, `TerminationThenStall` and `PanicStoresOne` (`Soundness/Layer5/MemoryAccessRestriction.lean`, `HostCallRestriction.lean`, `TerminationRestriction.lean`, `PanicRestriction.lean`); they concern LD, SD, HostIO, JAL and JALR rows.
  The other three, `NoStoreConditional`, `NoMaxLengthTrace` and `ClaimsNoPanic`, are about the program, completed traces or the claim, not about a step.
- The witness's division advice may differ from the honest one (for `rem a0, a1, zero` every quotient passes); they then differ only in instruction temporaries (see `methods/advice_fix_report.md`).
- Every expansion writes each temporary before reading it (`ExpansionTempLiveness.firstAccessIsWrite`, `JoltConstraints/expansion_temp_liveness.lean:71`, checked for every source by `ExpansionFacts.expand_temps_ok`, `JoltConstraints/expansion_facts.lean:916`).

So the step splits by expansion kind.
An expansion with no advice row runs row by row on the honest run, where every row's advice is honest, so `NextStep` holds before each row.
A division expansion with an advice row runs as one block.

## Step 1: the state inside an expansion

Define in `PrefixAgreement.lean` a structure `ExpansionState witness context run first done` for a run whose last `done` rows are the first `done` rows of the expansion that begins at bytecode row `first`.
Its fields:

- the `represents`, `real`, `noEarlierStop` and `terminationWord` fields of `BoundaryState`, unchanged;
- `first` starts a source instruction, `done` is at most the expansion's row count, and the run's last `done` rows have row indices `first`, `first + 1`, ... in order; the rows before them end at a source boundary (or there are none);
- `registers`: when the run's row count is below the trace length, `RegisterAgreementOn` at that cycle against `finalTraceState run.toTrace`, where a register is live if it is not an instruction temporary, or if `done` is below the expansion's row count and a row of the current expansion already in the run wrote it.
  Once the expansion is finished, only registers that are not temporaries must agree: after `rem a0, a1, zero` the witness's temporary 40 may hold 5 while the run's holds 0;
- `next`: when `done` is below the expansion's row count, the cycle after the run's rows exists, is real, selects slot `first + done + 1`, and the run is ready for bytecode row `first + done` in the sense of the `ready` clause of `NextStep`;
- `notStopped`: when `done` is below the expansion's row count, the run's last row, if any, is not a stable stall.
  For `done = 0` this comes from `boundary_step`'s hypothesis; for an interior row it holds because a stable stall ends its source instruction.
  It is needed to keep `noEarlierStop` when a row is added; the expansion's last row may itself be a stable stall.

Do not put honest advice in `ExpansionState`.
The division block needs the same state for a run that carries the witness's advice.
Where honest advice is needed, it is a separate hypothesis.

## Step 2: the staged pieces

Stage each with `sorry`, a docstring and an example:

- `expansion_start`: from `BoundaryState`, a real next cycle and no final stable stall, the `ExpansionState` with `done = 0` for the source instruction that `ready` supplies.
- `row_step`: from an `ExpansionState` with `done` below the expansion's row count, and honest advice for every row of the run, the run extended by one row satisfies `ExpansionState` with `done + 1` and still has honest advice for every row.
  Its hypotheses must include the soundness assumptions and the restrictions bundle, as `boundary_step` has them, and that the expansion has no advice row.
  Without that last hypothesis the statement is false: at a division's advice row the witness may write 5 where the honest run writes 0, and the written temporary is live until the expansion ends.
- `division_block`: from an `ExpansionState` with `done = 0` for an expansion that contains an advice row, and honest advice for every row of the run, the run extended by all the expansion's rows satisfies `ExpansionState` with `done` equal to the row count, with honest advice for every row.
  Its proof, in a later stage, runs the witness's rows on states with the witness's advice using the Layer 5 step lemmas, applies the matching `*Program_sound` (for example `divProgram_sound`, `JoltBytecode/InstructionEquivalence/Instructions/ALUAdviceFamily/Div.lean:104`), and builds the run's rows from `*Program_concrete` (for example `Div.lean:42`); state it so that this proof is possible, and say in the report how.
- `expansion_finish`: from an `ExpansionState` with `done` equal to the row count and honest advice for every row, `BoundaryState`.
  This includes `ready` for the next source instruction: the open source-boundary transition.
  It needs the soundness assumptions: the witness's next unexpanded PC is a field sum that does not wrap, while Sail's next PC is a 64-bit word, so comparing them uses `NextPCNoWrap` (`assumptions.pcNoWrap`), as `Soundness/Layer5/Jal.lean` does.

Then prove `boundary_step` from them: start the expansion; if it has an advice row, apply `division_block`; otherwise apply `row_step` once per row, by induction on the rows left; then finish.
Its body must contain no `sorry`.

## Before you stop

Check each staged statement against "Before staging a statement" in `AGENTS.md`, and say for each why it holds for an honest witness, with one example; for `division_block`, use the `rem a0, a1, zero` example with witness quotient 5.
Build `JoltConstraints`.
Run `#print axioms JoltInstance.soundness`: `sorryAx` must come only through `boundaryState_empty`, the four statements staged here, and helpers C and D.
Write `methods/layer6/stage-2-report.md` with each new declaration (file and line, staged or proved), any place where this plan did not fit and what you did instead, any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.
