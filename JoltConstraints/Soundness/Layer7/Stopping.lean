import JoltConstraints.Soundness.Layer7.StallSuffix
import JoltConstraints.Soundness.Layer7.LastJump
import JoltConstraints.Soundness.Layer7.TerminationStore
import JoltConstraints.Soundness.Layer3.History

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions JoltISA

namespace JoltInstance

/-- The retained run ends in a stable stall and has at least one row, and
its final RAM agrees with the witness outside the synthetic termination word.
For example, an SDK exit stores 1 to termination and finishes with `j .`.
See jolt/jolt-sdk/macros/src/lib.rs:880-887 at 5def437f and
PR #2109 merge commit 0249591a, jolt/tracer/src/emulator/cpu.rs:553-576. -/
theorem soundness_stopping {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsPrefix witness run.toTrace)
    (realRows : ∀ t : Fin params.traceLength,
      t.val < run.rows.size → witness.InstructionFlags .IsNoop t = 0)
    (noEarlierStop : ∀ (i : Nat) (current next : TraceRow run.bytecode),
      run.rows[i]? = some current → run.rows[i + 1]? = some next →
      ¬ current.StableStall)
    (cut : run.rows.size = params.traceLength ∨
      ∃ bound : run.rows.size < params.traceLength,
        witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 1 ∨
        ∃ last ∈ run.rows.back?, last.StableStall)
    (advice : ∀ n : Fin run.rows.size,
      run.rows[n].someTracerAdvice? =
        honestTracerAdviceAtStepN joltInstance.program run.rows n) :
    (∀ last ∈ run.rows.back?, last.StableStall) ∧
    0 < run.rows.size ∧
    (∀ address : Fin params.ramSize,
      address.val ≠ (run.initialState.jolt_device.memory_layout.termination.toNat -
        JoltConstraints.ramLowestAddress run.initialState.jolt_device.memory_layout) / 8 →
      witness.RamValFinal address =
        ((TraceWitness.finalRamWord run.toTrace address.val).toNat : F)) := by
  obtain ⟨storeIndex, stored⟩ :=
    soundness_termination_store_exists joltField joltInstance assumptions restrictions
      privateInputs witness context equations run bytecodeEq represented realRows cut
  have nonempty : 0 < run.rows.size := by
    have inBounds := storeIndex.isLt
    omega
  have stops : ∀ last ∈ run.rows.back?, last.StableStall := by
    rcases cut with full | ⟨bound, padding | ⟨last, lastMem, stable⟩⟩
    · have lastJump := soundness_last_row_is_jump joltField joltInstance privateInputs
        witness context equations run bytecodeEq represented.toRepresentsRows
        realRows nonempty (Or.inl full)
      exact soundness_termination_last_stall joltInstance restrictions.terminationThenStall
        privateInputs run ⟨storeIndex, stored⟩ noEarlierStop advice lastJump
    · have lastJump := soundness_last_row_is_jump joltField joltInstance privateInputs
        witness context equations run bytecodeEq represented.toRepresentsRows
        realRows nonempty (Or.inr ⟨bound, padding⟩)
      exact soundness_termination_last_stall joltInstance restrictions.terminationThenStall
        privateInputs run ⟨storeIndex, stored⟩ noEarlierStop advice lastJump
    · intro other otherMem
      have someLast : run.rows.back? = some last := by simpa using lastMem
      have someOther : run.rows.back? = some other := by simpa using otherMem
      have equal : other = last := Option.some.inj (someOther.symm.trans someLast)
      subst other
      exact stable
  have suffixZero :
      ∀ t : Fin params.traceLength, run.rows.size ≤ t.val →
        ∀ address : Fin params.ramSize,
          witness.RamRa address t * witness.RamInc t = 0 :=
    soundness_stall_suffix_zero_ram_effects joltField joltInstance assumptions.pcNoWrap privateInputs
      witness context equations run bytecodeEq represented.toRepresentsRows nonempty stops
  have finalFromCut :
      ∀ address : Fin params.ramSize,
        address.val ≠ (run.initialState.jolt_device.memory_layout.termination.toNat -
          JoltConstraints.ramLowestAddress run.initialState.jolt_device.memory_layout) / 8 →
        witness.RamValFinal address =
          ((TraceWitness.finalRamWord run.toTrace address.val).toNat : F) := by
    intro address nonTermination
    by_cases below : run.rows.size < params.traceLength
    · have atCut := represented.cutRam.1 below address nonTermination
      have sameFinal := JoltConstraints.Soundness.ramVal_eq_final_of_suffix_zero
        equations.ramValEqInitialPlusPrefixRamInc
        equations.ramValFinalEqInitialPlusRamInc address ⟨run.rows.size, below⟩
        (fun cycle later => suffixZero cycle later address)
      exact sameFinal.symm.trans atCut
    · have equal : run.rows.size = params.traceLength := by
        exact Nat.le_antisymm represented.rowsBound (Nat.le_of_not_gt below)
      exact represented.cutRam.2 equal address nonTermination
  exact ⟨stops, nonempty, finalFromCut⟩

end JoltInstance
