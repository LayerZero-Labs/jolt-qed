import JoltConstraints.Constraints.LookupOperandData

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (41) in `constraints.md`:
The right lookup operand is the full address for identity RAF and the deinterleaved right value otherwise.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs#L181-L201 -/
def rightLookupOperandEqInstructionRaf {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.RightLookupOperand t =
      ∑ address : Fin (2 ^ 128), instructionLookupRa witness address t *
        ((1 - witness.InstructionRafFlag t) * lookupAddressRight address +
          witness.InstructionRafFlag t * (address.val : F))

/-- Completeness target for the honest witness; proof pending.
Requires the address-chunk selection and operand-encoding correspondence.
The entire 128-bit address is cast into F, preserving arithmetic carry. -/
theorem honestWitness_rightLookupOperandEqInstructionRaf
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : trace.rows.size ≤ params.traceLength)
    : rightLookupOperandEqInstructionRaf
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  sorry

end JoltConstraints
