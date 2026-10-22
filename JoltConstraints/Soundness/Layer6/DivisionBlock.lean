import JoltConstraints.Soundness.Layer6.PrefixState

/-! Staged reconstruction of a whole division expansion with honest advice. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness

/-- Append an entire advice-bearing division expansion, using honest advice in
the returned run and restoring agreement outside instruction temporaries.
The input is before the expansion, so a later proof may separately execute
witness advice, apply the matching division soundness theorem, and construct
honest rows using its concrete-execution theorem.
For example, REM with divisor zero may use witness quotient 5 while the returned
nine rows use quotient 0 and still produce the same architectural result.
See jolt/crates/jolt-program/src/expand/division/rem.rs (`expand_rem`) at 5def437f. -/
theorem division_block {F : Type} [Field F] (joltField : JoltField F)
    {joltInstance : JoltInstance SourceInstruction} {params : WitnessParams}
    {privateInputs : JoltPrivateInputs} (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (first : Fin context.bytecode.size)
    (state : ExpansionState witness context run first 0)
    (honestAdvice : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n)
    (hasAdvice : ExpansionHasAdvice context.bytecode first) :
    ∃ run' : UntrustedAnswerRun joltInstance privateInputs,
      RunExtends run run' ∧
      run'.rows.size = run.rows.size + expansionRowCount context.bytecode first ∧
      ExpansionState witness context run' first (expansionRowCount context.bytecode first) ∧
      (∀ n : Fin run'.rows.size, run'.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run'.rows n) := by
  sorry

end JoltInstance
