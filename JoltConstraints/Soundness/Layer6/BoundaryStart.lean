import JoltConstraints.Soundness.Layer6.PrefixState

/-! Staged initialization of the empty run and the next source expansion. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness

/-- The instance's initialized state admits an empty run satisfying the boundary
invariant at witness cycle zero. The run's `initialized` certificate identifies
its state with the state supplied by `context.initialized`.
For example, before an entry ADDI, registers and nontermination RAM agree with
their initial tables, and the selected entry row supplies `ready` if it is real. -/
theorem boundaryState_empty {F : Type} [Field F] (joltField : JoltField F)
    {joltInstance : JoltInstance SourceInstruction} {params : WitnessParams}
    {privateInputs : JoltPrivateInputs} (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness) :
    ∃ run : UntrustedAnswerRun joltInstance privateInputs,
      run.rows = #[] ∧ BoundaryState witness context run := by
  sorry

/-- Open the source selected by a boundary's real next cycle without adding a
row. `done = 0` leaves all instruction temporaries dead and preserves the run.
For example, before a two-row SLL, the selected first row is VirtualPow2 and
the next clause prepares that row's pre-state using the source compression flag. -/
theorem expansion_start {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (boundary : BoundaryState witness context run)
    (bound : run.rows.size < params.traceLength)
    (real : witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 0)
    (notStopped : ∀ last ∈ run.rows.back?, ¬ last.StableStall) :
    ∃ first : Fin context.bytecode.size, ExpansionState witness context run first 0 := by
  sorry

end JoltInstance
