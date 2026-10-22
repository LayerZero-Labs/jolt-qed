import JoltConstraints.Constraints.All
import JoltConstraints.Soundness.Assumptions
import JoltConstraints.Soundness.Layer5.TapeTrace
import JoltConstraints.witness_helpers.pc
import JoltConstraints.witness_helpers.rs1_value
import JoltConstraints.witness_helpers.rs2_value
import JoltConstraints.witness_helpers.ram_address

set_option autoImplicit false

namespace JoltInstance

/-- The witness observations for every row up to and including the first stable
stall, or up to padding or the last witness cycle when there is no stall. -/
structure RepresentsRows {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (trace : Trace) : Prop where
  rowsBound : trace.rows.size ≤ params.traceLength
  pc : ∀ t : Fin params.traceLength, t.val < trace.rows.size →
    witness.PC t = TraceWitness.PC params trace t
  rs1 : ∀ t : Fin params.traceLength, t.val < trace.rows.size →
    witness.Rs1Value t = TraceWitness.Rs1Value params trace t
  rs2 : ∀ t : Fin params.traceLength, t.val < trace.rows.size →
    witness.Rs2Value t = TraceWitness.Rs2Value params trace t
  ramAddress : ∀ t : Fin params.traceLength, t.val < trace.rows.size →
    witness.RamAddress t = TraceWitness.RamAddress params trace t

/-- Row observations and RAM agreement immediately after the retained prefix.
At the last witness cycle the boundary is `RamValFinal`; otherwise it is
`RamVal` at the cut. -/
structure RepresentsPrefix {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (trace : Trace) : Prop
    extends RepresentsRows witness trace where
  cutRam :
    (∀ bound : trace.rows.size < params.traceLength,
      ∀ address : Fin params.ramSize,
        address.val ≠ (trace.initialState.jolt_device.memory_layout.termination.toNat -
          JoltConstraints.ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 →
        witness.RamVal address ⟨trace.rows.size, bound⟩ =
          ((TraceWitness.finalRamWord trace address.val).toNat : F)) ∧
    (trace.rows.size = params.traceLength →
      ∀ address : Fin params.ramSize,
        address.val ≠ (trace.initialState.jolt_device.memory_layout.termination.toNat -
          JoltConstraints.ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 →
        witness.RamValFinal address =
          ((TraceWitness.finalRamWord trace address.val).toNat : F))

/-- Row agreement together with final RAM agreement outside the synthetic
termination word. The stopping proof owns the final RAM comparison. -/
structure Represents {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (trace : Trace) : Prop
    extends RepresentsRows witness trace where
  finalRam : ∀ address : Fin params.ramSize,
    address.val ≠ (trace.initialState.jolt_device.memory_layout.termination.toNat -
      JoltConstraints.ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 →
    witness.RamValFinal address = ((TraceWitness.finalRamWord trace address.val).toNat : F)

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
  sorry

end JoltInstance
