import JoltConstraints.Soundness.Layer6.DivisionDefs
import JoltConstraints.Soundness.Layer7.TerminationStore

/-! Reconstruction of an honest division expansion's trace rows. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

/-- A replay of `count` consecutive division rows after `run`.
`ordered` identifies each bytecode row, `firstPre` records the prepared starting
state, and `adviceAtOffset` records the one patched advice word.
For example, a nine-row REM replay with quotient zero starts at the original
prefix's end and records zero on its VirtualAdvice row. -/
structure DivisionReplayRows
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run replay : UntrustedAnswerRun joltInstance privateInputs)
    {bytecode : Array JoltInstructionRow} (first : Fin bytecode.size)
    (count : Nat) (pre honestPost : SailJoltState) (advice : BitVec 64) : Prop where
  extendsRun : RunExtends run replay
  size : replay.rows.size = run.rows.size + count
  ordered : ∀ offset < count, ∃ row ∈ replay.rows[run.rows.size + offset]?,
    row.rowIndex.val = first.val + offset
  firstPre : ∀ row ∈ replay.rows[run.rows.size]?, row.preState = pre
  finalPost : TraceWitness.finalTraceState replay.toTrace = honestPost
  adviceAtOffset : ∀ offset < count, ∀ row ∈ replay.rows[run.rows.size + offset]?,
    row.someTracerAdvice? =
      if replay.bytecode[row.rowIndex].instruction.adviceValue?.isSome then some advice else none

/-- Appending rows preserves honest advice on the retained prefix.
For example, replaying a REM block after a JAL leaves the JAL's earlier advice
observation unchanged. -/
theorem RunExtends.honestAdvice_before
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (run replay : UntrustedAnswerRun joltInstance privateInputs)
    (extendsRun : RunExtends run replay)
    (honest : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n)
    (n : Fin replay.rows.size) (before : n.val < run.rows.size) :
    replay.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program replay.rows n := by
  obtain ⟨bytecodeEq, rowsEq⟩ := extendsRun
  rcases run with ⟨⟨runBytecode, runRows, _⟩, _⟩
  rcases replay with ⟨⟨replayBytecode, replayRows, _⟩, _⟩
  dsimp only at bytecodeEq rowsEq honest n before ⊢
  subst bytecodeEq
  dsimp only at rowsEq honest before ⊢
  have sizes := congrArg Array.size rowsEq
  simp only [Array.size_extract, Nat.sub_zero] at sizes
  have within : runRows.size ≤ replayRows.size := by omega
  have rowEq : replayRows[n].someTracerAdvice? =
      (runRows[n.val]'before).someTracerAdvice? := by
    have h := congrArg (fun rows : Array (TraceRow replayBytecode) => rows[n.val]?) rowsEq
    simp only [Array.getElem?_extract, Nat.min_eq_left within, Nat.zero_add, Nat.sub_zero,
      if_pos before, Array.getElem?_eq_getElem n.isLt,
      Array.getElem?_eq_getElem before] at h
    exact congrArg TraceRow.someTracerAdvice? (Option.some.inj h)
  rw [rowEq]
  have adviceEq := honestTracerAdviceAtStepN_extract joltInstance.program
    replayRows runRows.size n.val within before
  rw [rowsEq] at adviceEq
  exact (honest ⟨n.val, before⟩).trans adviceEq

/-- Split an honest division program run and append each execution to the
original prefix, preserving its exact rows and recording the patched advice.
For example, the nine REM instructions become nine consecutive trace rows. -/
theorem division_replay_rows
    {F : Type} [Field F] {joltInstance : JoltInstance SourceInstruction}
    {params : WitnessParams} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (state : ExpansionState witness context run first 0)
    (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (count : (expansionInstructions context.bytecode first).length =
      expansionRowCount context.bytecode first)
    (shape : ArithmeticAdviceSequence (expansionInstructions context.bytecode first)
      (kind.program rd rs1 rs2))
    (pre honestPost : SailJoltState)
    (entry : ∃ next : Fin run.bytecode.size, next.val = first.val ∧ run.NextStep next pre)
    (honestRun : Program.Run
      (kind.program rd rs1 rs2 (kind.honestAdvice rd rs1 rs2 pre)) pre honestPost) :
    ∃ replay : UntrustedAnswerRun joltInstance privateInputs,
      DivisionReplayRows run replay first (expansionRowCount context.bytecode first)
        pre honestPost (kind.honestAdvice rd rs1 rs2 pre) := by
  sorry

/-- Transfer a completed witness division block's observation, RAM, register,
and stopping invariants to its honest replay, using their equal final states
outside instruction temporaries.
For example, REM quotient five and quotient zero still agree on architectural
registers and RAM after the last row. -/
theorem division_replay_complete
    {F : Type} [Field F] {joltInstance : JoltInstance SourceInstruction}
    {params : WitnessParams} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run candidate replay : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (state : ExpansionState witness context run first 0)
    (kind : DivisionKind) (rd rs1 rs2 : regidx)
    (count : (expansionInstructions context.bytecode first).length =
      expansionRowCount context.bytecode first)
    (shape : ArithmeticAdviceSequence (expansionInstructions context.bytecode first)
      (kind.program rd rs1 rs2))
    (pre honestPost : SailJoltState)
    (entry : ∃ next : Fin run.bytecode.size, next.val = first.val ∧ run.NextStep next pre)
    (candidateExtends : RunExtends run candidate)
    (candidateSize : candidate.rows.size = run.rows.size + expansionRowCount context.bytecode first)
    (complete : ExpansionState witness context candidate first
      (expansionRowCount context.bytecode first))
    (same : DivisionFinalAgreement (TraceWitness.finalTraceState candidate.toTrace) honestPost)
    (replayed : DivisionReplayRows run replay first (expansionRowCount context.bytecode first)
      pre honestPost (kind.honestAdvice rd rs1 rs2 pre)) :
    ExpansionState witness context replay first
      (expansionRowCount context.bytecode first) := by
  sorry

/-- On the appended block, the honest tracer recomputes the single advice word
from the source instruction and the prepared state at the block's first row.
For example, a REM by zero records quotient magnitude zero on its advice row. -/
theorem division_replay_honest_new
    {F : Type} [Field F] {joltInstance : JoltInstance SourceInstruction}
    {params : WitnessParams} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run replay : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (starts : context.bytecode[first].starts_source = true)
    (kind : DivisionKind) (rd rs1 rs2 : regidx) (placeholder : BitVec 64)
    (source : joltInstance.program.instructionAt context.bytecode[first].address =
      some (kind.source rd rs1 rs2 placeholder))
    (count : (expansionInstructions context.bytecode first).length =
      expansionRowCount context.bytecode first)
    (shape : ArithmeticAdviceSequence (expansionInstructions context.bytecode first)
      (kind.program rd rs1 rs2))
    (pre honestPost : SailJoltState)
    (replayed : DivisionReplayRows run replay first (expansionRowCount context.bytecode first)
      pre honestPost (kind.honestAdvice rd rs1 rs2 pre))
    (n : Fin replay.rows.size) (new : run.rows.size ≤ n.val) :
    replay.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program replay.rows n := by
  sorry

end JoltInstance
