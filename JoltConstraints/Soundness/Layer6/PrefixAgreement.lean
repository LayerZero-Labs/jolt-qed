import JoltConstraints.Soundness.Layer6.ExecutionPrefix
import JoltConstraints.Soundness.Layer6.BytecodePC
import JoltConstraints.Soundness.Layer5.Registers

/-! Execution-prefix reconstruction by induction over complete source instructions.
The boundary obligations are staged for review before their proofs are attempted. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness

/-- Agreement after `run.rows.size` witness cycles, at a source-instruction boundary.
`represents` compares retained row observations and RAM outside the termination word;
`real` excludes retained padding and `noEarlierStop` excludes a stall before the last row.
`honestAdvice` records the honest tracer's advice at every retained row, while
`atBoundary` says the last row, if present, completes its source instruction.
`registers` compares all non-instruction-temporary registers at the next witness cycle
with the run's final state and retains the presence of every Sail register.
`terminationWord` keeps the termination RAM word zero until a store touches it.
`ready` supplies the next selected bytecode row and its prepared execution state when
the witness has another real cycle and the run has not reached a stable stall.
For example, after `rem a0, a1, zero`, witness quotient 5 and honest quotient 0 may
differ in temporary 40, while `a0`, other persistent registers and RAM still agree.
See jolt/crates/jolt-program/src/expand/division/rem.rs:15-24 and
jolt/tracer/src/instruction/rem.rs:44-58 at 5def437f. -/
structure BoundaryState {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (run : UntrustedAnswerRun joltInstance privateInputs) : Prop where
  represents : RepresentsPrefix witness run.toTrace
  real : ∀ t : Fin params.traceLength,
    t.val < run.rows.size → witness.InstructionFlags .IsNoop t = 0
  noEarlierStop : ∀ (i : Nat) (current next : TraceRow run.bytecode),
    run.rows[i]? = some current → run.rows[i + 1]? = some next →
    ¬ current.StableStall
  honestAdvice : ∀ n : Fin run.rows.size,
    run.rows[n].someTracerAdvice? =
      honestTracerAdviceAtStepN joltInstance.program run.rows n
  atBoundary : ∀ last ∈ run.rows.back?,
    run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0
  registers : ∀ bound : run.rows.size < params.traceLength,
    RegisterAgreementOn (fun register => ¬ IsInstructionTemporary register)
      witness ⟨run.rows.size, bound⟩ (TraceWitness.finalTraceState run.toTrace)
  terminationWord : ∀ bound : run.rows.size < params.traceLength,
    (¬ ∃ i : Fin run.rows.size, run.StoresTerminationAt i) →
    ∀ address : Fin params.ramSize,
      address.val = (run.initialState.jolt_device.memory_layout.termination.toNat -
        JoltConstraints.ramLowestAddress run.initialState.jolt_device.memory_layout) / 8 →
      witness.RamVal address ⟨run.rows.size, bound⟩ = 0
  ready : ∀ bound : run.rows.size < params.traceLength,
    witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 0 →
    (∀ last ∈ run.rows.back?, ¬ last.StableStall) →
    ∃ (next : Fin run.bytecode.size) (pre : SailJoltState)
      (slot : Fin (2 ^ params.logBytecodeK)),
      JoltConstraints.bytecodeRa witness slot ⟨run.rows.size, bound⟩ = 1 ∧
      slot.val = next.val + 1 ∧ run.NextStep next pre

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
  sorry

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
