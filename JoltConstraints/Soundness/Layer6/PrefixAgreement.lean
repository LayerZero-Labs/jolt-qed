import JoltConstraints.Soundness.Layer6.BoundaryStart
import JoltConstraints.Soundness.Layer6.DivisionBlock
import JoltConstraints.Soundness.Layer6.RowStep
import JoltConstraints.Soundness.Layer6.ExpansionFinish
import JoltConstraints.Soundness.Layer6.BytecodePC

/-! Execution-prefix reconstruction from the staged boundary and expansion lemmas. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness

/-- From a boundary with a real next witness cycle and no final stable stall,
execute a whole source instruction to obtain a larger run satisfying the same
boundary invariant. The conclusion requires progress, without specifying the
array extension used to construct that run.
For example, a REM step retains all nine expanded rows with honest quotient
advice, even when the witness's quotient differs in instruction temporaries. -/
theorem boundary_step {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (boundary : BoundaryState witness context run)
    (bound : run.rows.size < params.traceLength)
    (real : witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 0)
    (notStopped : ∀ last ∈ run.rows.back?, ¬ last.StableStall) :
    ∃ run' : UntrustedAnswerRun joltInstance privateInputs,
      run.rows.size < run'.rows.size ∧ BoundaryState witness context run' := by
  classical
  obtain ⟨first, initial⟩ := expansion_start witness context run boundary bound real notStopped
  let count := expansionRowCount context.bytecode first
  have complete : ∃ run' : UntrustedAnswerRun joltInstance privateInputs,
      run'.rows.size = run.rows.size + count ∧
      ExpansionState witness context run' first count ∧
      (∀ n : Fin run'.rows.size, run'.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run'.rows n) := by
    by_cases hasAdvice : ExpansionHasAdvice context.bytecode first
    · obtain ⟨run', _, size, state, advice⟩ := division_block joltField witness context
        equations run first initial boundary.honestAdvice hasAdvice
      exact ⟨run', size, state, advice⟩
    have finish : ∀ remaining done (current : UntrustedAnswerRun joltInstance privateInputs),
        count - done = remaining → ExpansionState witness context current first done →
        (∀ n : Fin current.rows.size, current.rows[n].someTracerAdvice? =
          honestTracerAdviceAtStepN joltInstance.program current.rows n) →
        ∃ result : UntrustedAnswerRun joltInstance privateInputs,
          result.rows.size = current.rows.size + (count - done) ∧
          ExpansionState witness context result first count ∧
          (∀ n : Fin result.rows.size, result.rows[n].someTracerAdvice? =
            honestTracerAdviceAtStepN joltInstance.program result.rows n) := by
      intro remaining
      induction remaining with
      | zero =>
        intro done current left state advice
        have done_le : done ≤ count := state.done_le
        have doneEq : done = count := by omega
        subst done
        exact ⟨current, by omega, state, advice⟩
      | succ remaining ih =>
        intro done current left state advice
        have unfinished : done < count := by omega
        obtain ⟨next, _, size, state', advice'⟩ := row_step joltField joltInstance
          assumptions restrictions privateInputs witness context equations current first
          done state unfinished advice hasAdvice
        obtain ⟨result, total, completed, honest⟩ := ih (done + 1) next
          (by omega) state' advice'
        exact ⟨result, by omega, completed, honest⟩
    simpa only [Nat.sub_zero] using finish count 0 run rfl initial boundary.honestAdvice
  obtain ⟨run', size, state, advice⟩ := complete
  have positive : 0 < count := Nat.zero_lt_succ _
  exact ⟨run', by omega, expansion_finish joltField joltInstance assumptions
    privateInputs witness context equations run' first state advice⟩

/-- Reconstruct witness rows through the first stable stall, or through padding
or the last cycle when no stall occurs. Every retained row is real, no retained
row stops before the last, and its observations and internal advice agree. -/
theorem soundness_execution_prefix_agreement {F : Type} [Field F]
    (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness) :
    ∃ run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs,
      run.bytecode = context.bytecode ∧
      RepresentsPrefix witness run.toTrace ∧
      (∀ t : Fin params.traceLength,
        t.val < run.rows.size → witness.InstructionFlags .IsNoop t = 0) ∧
      (∀ (i : Nat) (current next : TraceRow run.bytecode),
        run.rows[i]? = some current → run.rows[i + 1]? = some next →
        ¬ current.StableStall) ∧
      (run.rows.size = params.traceLength ∨
        ∃ bound : run.rows.size < params.traceLength,
          witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 1 ∨
          ∃ last ∈ run.rows.back?, last.StableStall) ∧
      (∀ n : Fin run.rows.size,
        run.rows[n].someTracerAdvice? =
          honestTracerAdviceAtStepN joltInstance.program run.rows n) := by
  classical
  obtain ⟨run, empty, boundary⟩ := boundaryState_empty joltField witness context equations
  clear empty
  generalize remainingEq : params.traceLength - run.rows.size = remaining
  induction remaining using Nat.strong_induction_on generalizing run with
  | h remaining ih =>
    have rowsBound := boundary.represents.rowsBound
    by_cases cut : run.rows.size = params.traceLength ∨
        ∃ bound : run.rows.size < params.traceLength,
          witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 1 ∨
          ∃ last ∈ run.rows.back?, last.StableStall
    · exact ⟨run, Option.some.inj (run.expands.symm.trans context.expands),
        boundary.represents, boundary.real, boundary.noEarlierStop, cut,
        boundary.honestAdvice⟩
    have notFull : run.rows.size ≠ params.traceLength := fun full => cut (Or.inl full)
    have bound : run.rows.size < params.traceLength := by omega
    have notPadding : witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ ≠ 1 :=
      fun padding => cut (Or.inr ⟨bound, Or.inl padding⟩)
    have real : witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 0 := by
      obtain ⟨slot, selected, _⟩ := bytecodeRa_unique
        (two_pow_127_lt_char joltField) context equations ⟨run.rows.size, bound⟩
      have flag := instructionFlag_of_selected_bytecode
        (two_pow_127_lt_char joltField) context equations .IsNoop
        ⟨run.rows.size, bound⟩ slot selected
      unfold JoltConstraints.bytecodeInstructionFlag at flag
      split at flag
      · simpa only [JoltMetadata.instructionFlag, Bool.false_eq_true, ↓reduceIte] using flag
      · exact False.elim (notPadding (by simpa only [↓reduceIte] using flag))
    have notStopped : ∀ last ∈ run.rows.back?, ¬ last.StableStall := by
      intro last atEnd stalled
      exact cut (Or.inr ⟨bound, Or.inr ⟨last, atEnd, stalled⟩⟩)
    obtain ⟨run', grows, boundary'⟩ := boundary_step joltField joltInstance
      assumptions restrictions privateInputs witness context equations run boundary
      bound real notStopped
    have nextBound := boundary'.represents.rowsBound
    exact ih (params.traceLength - run'.rows.size) (by omega) run' boundary' rfl

end JoltInstance
