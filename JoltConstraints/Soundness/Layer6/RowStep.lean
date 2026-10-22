import JoltConstraints.Soundness.Layer6.PrefixState

/-! Staged execution of one row in a source expansion without internal advice. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness

/-- Append one row of an unfinished source with no VirtualAdvice, preserving
the expansion invariant and honest advice throughout the extended run.
For example, SLL's first row writes temporary 40, which becomes live for its
second row; no hypothesis equates that temporary before its first write. -/
theorem row_step {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (honestAdvice : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n)
    (noAdvice : ¬ ExpansionHasAdvice context.bytecode first) :
    ∃ run' : UntrustedAnswerRun joltInstance privateInputs,
      RunExtends run run' ∧ run'.rows.size = run.rows.size + 1 ∧
      ExpansionState witness context run' first (done + 1) ∧
      (∀ n : Fin run'.rows.size, run'.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run'.rows n) := by
  sorry

end JoltInstance
