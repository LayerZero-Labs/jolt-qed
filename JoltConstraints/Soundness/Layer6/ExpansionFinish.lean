import JoltConstraints.Soundness.Layer6.PrefixState

/-! Staged transition from a completed source expansion to the next boundary. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness

/-- Close a completed source expansion with honest advice, restoring the boundary
invariant including readiness for the next source when execution continues.
The assumptions retain `pcNoWrap` for the field/word PC comparison.
For example, a completed ADDI at address 0x1000 selects a successor at 0x1004
when uncompressed and when the next witness cycle is real. -/
theorem expansion_finish {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (state : ExpansionState witness context run first (expansionRowCount context.bytecode first))
    (honestAdvice : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n) :
    BoundaryState witness context run := by
  sorry

end JoltInstance
