import JoltConstraints.Constraints.LookupOperandData

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (40) in `constraints.md`:
The left lookup operand is zero for identity RAF and the deinterleaved left value otherwise.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs#L181-L201 -/
def leftLookupOperandEqInstructionRaf {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.LeftLookupOperand t =
      ∑ address : Fin (2 ^ 128), instructionLookupRa witness address t *
        (1 - witness.InstructionRafFlag t) * lookupAddressLeft address

/-- Completeness target for the honest witness; proof pending.
Requires the address-chunk selection and operand-encoding correspondence.
This equation does not require any lookup-table output to be implemented. -/
theorem honestWitness_leftLookupOperandEqInstructionRaf
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    : leftLookupOperandEqInstructionRaf
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  sorry

end JoltConstraints
