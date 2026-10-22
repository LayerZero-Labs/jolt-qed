# Layer 6, stage 1: stage the induction over source instructions

Read `/Users/ari.biswas/Lean/jolt-qed-public/AGENTS.md` first.
Claude wrote this plan and has made mistakes in this proof before; check each claim against the code before relying on it, and stop and report if one is wrong.
This stage is top-down: state the pieces with `sorry`, prove `soundness_execution_prefix_agreement` from them, build, and stop for review.
Prove nothing else.
Work in `/Users/ari.biswas/Lean/jolt-qed-public` on `feat/soundness`; do not commit.

## The target

`JoltInstance.soundness_execution_prefix_agreement` (`JoltConstraints/Soundness/Layer6/ExecutionPrefix.lean:80`) says the witness is a run of the program up to its cut.
Its only caller is helper A (`Soundness/TopLevel.lean`).
Do not change its statement, or `IsInstructionTemporary`, `RepresentsRows`, `RepresentsPrefix` and `Represents` (same file, lines 17, 29, 50 and 69).

Two facts shape the design.

- The run uses the honest tracer's advice, but the witness may record different division advice: for `rem a0, a1, zero` every quotient passes the checks.
  The two then differ only in instruction temporaries (registers 40 to 47), which `RepresentsRows` does not compare.
  See `methods/advice_fix_plan.md`.
- The witness's real cycles split into whole source instructions.
  The last real cycle before padding, and the last witness cycle, end a source instruction (`last_row_terminal`, `Soundness/Layer7/LastJump.lean:455`, private for now), and a stable stall ends one by definition (`TraceRow.StableStall`, `JoltConstraints/honest_trace.lean:36`).

So the induction goes one source instruction at a time, and its invariant holds only between source instructions.
There, every expansion in the run is complete, so honest advice holds for every row, and every temporary is dead (`ExpansionFacts.expand_temps_ok`, `JoltConstraints/expansion_facts.lean`).

## Step 1: move the theorem

Move `soundness_execution_prefix_agreement`, unchanged, into a new file `Soundness/Layer6/PrefixAgreement.lean`, and make `TopLevel.lean` import it.
`ExecutionPrefix.lean` keeps the definitions and structures, which the Layer 7 files import.
`PrefixAgreement.lean` may import the Layer 5 files, `Layer6/BytecodePC.lean` and the Layer 7 files: no Layer 7 file imports it, so there is no cycle.
Move nothing else.

## Step 2: register agreement on a set of registers

Add to `Soundness/Layer5/Registers.lean` a structure `RegisterAgreementOn (live : Fin 128 → Prop) witness t state`: `AllRegistersPresent state.sail`, and, for every register in `live`, the same table/state equation as `RegisterAgreement.values` (`Registers.lean:21`).
Add only the definition, with a docstring and an example (between source instructions, `live` is every register that is not an instruction temporary).
Do not change `RegisterAgreement` or any step lemma.

## Step 3: the invariant between source instructions

Define in `PrefixAgreement.lean` a structure `BoundaryState witness context run` for a run whose rows are the witness's first `n = run.rows.size` cycles.
Its fields:

- `represents : RepresentsPrefix witness run.toTrace`: the row observations, and RAM agreement after the last row at every word except the termination word.
- `real`: every retained cycle has `IsNoop = 0`.
- `noEarlierStop`: no retained row before the last is a stable stall, as in the theorem.
- `honestAdvice`: every row's `someTracerAdvice?` is `honestTracerAdviceAtStepN joltInstance.program run.rows` at that row, as in the theorem.
- `atBoundary`: the last row, if any, ends its source instruction (`virtual_sequence_remaining.getD 0 = 0`).
- `registers`: when `n` is below the trace length, `RegisterAgreementOn` at cycle `n` against `finalTraceState run.toTrace` (`JoltConstraints/witness_helpers/ram_state.lean:9`), with `live` the registers that are not instruction temporaries.
- `terminationWord`: when `n` is below the trace length and no row of the run stores to the termination region (`UntrustedAnswerRun.StoresTerminationAt`, `Soundness/Layer5/TerminationRestriction.lean:35`), the witness's RAM column `n` holds 0 at the termination word (its index is written out in `RepresentsPrefix.cutRam`).
  The RAM field leaves this word out, but a load of the termination word before any store must read 0 in both: Jolt's tracer loads 0 there, and the witness's initial RAM holds 0 there.
- `ready`: when `n` is below the trace length, cycle `n` is real and the last row is not a stable stall, there are a bytecode row `next`, a state `pre` and a slot such that the witness selects that slot at cycle `n`, the slot is `next + 1` (slot `k + 1` holds bytecode row `k`; see `slotPosition` in `host_call_selected_step`, `Soundness/Layer5/HostCallRegisterFrame.lean`), and `run.NextStep next pre` holds (`Soundness/Layer5/MemoryAccessRestriction.lean:29`).
  `NextStep` holds in full here, honest advice included, because every expansion in the run is complete.
  Do not change `NextStep`.

Give the structure a docstring defining each field, with an example.
If a field cannot be stated this way, stop and report.
Add no other field: if a later stage needs another fact carried between source instructions, it will be added then, with review.

## Step 4: the staged pieces

Stage these with `sorry`, each with a docstring and an example:

- `boundaryState_empty`: the run with no rows on the instance's initial state satisfies `BoundaryState`.
  The initial state comes from `context.initialized`.
- `boundary_step`: from `BoundaryState` for `run`, a cycle `n` below the trace length that is real, and a last row that is not a stable stall, there is a run `run'` with more rows than `run` that satisfies `BoundaryState`.
  It stands for executing the next source instruction, every one of its rows, and is the only statement later stages split.
  Its proof will extend `run` by that instruction's rows; the statement need not say so.

Then prove `soundness_execution_prefix_agreement` from them, by strong induction on the number of cycles left.
At each run, stop if `n` is the trace length, cycle `n` is padding, or the last row is a stable stall; the theorem's conclusion then follows from the `BoundaryState` fields and `run.expands` with `context.expands` for the bytecode equation.
Otherwise apply `boundary_step`.
`represents.rowsBound` bounds the row count, so the induction terminates.
The body of the theorem must contain no `sorry`.

## Before you stop

Check each staged statement against "Before staging a statement" in `AGENTS.md`, and say for each field and each staged statement why it holds for an honest witness, with one example.
Build `JoltConstraints`.
Run `#print axioms JoltInstance.soundness`: `sorryAx` must come only through `boundaryState_empty`, `boundary_step`, and helpers C and D.
Write `methods/layer6/stage-1-report.md` with each new declaration (file and line, staged or proved), any place where this plan did not fit and what you did instead, any proof slower than about ten seconds, and the build and axiom results.
Do not commit.
Then stop.
