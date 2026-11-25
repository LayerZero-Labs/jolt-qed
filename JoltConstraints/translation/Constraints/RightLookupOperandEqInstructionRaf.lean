import JoltConstraints.translation.Constraints.LookupOperandData
import JoltConstraints.translation.Constraints.InstructionLookupRa

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (41) in `constraints.md`:
The right lookup operand is the full address for identity RAF and the deinterleaved right value otherwise.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs -/
def rightLookupOperandEqInstructionRaf {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.RightLookupOperand t =
      ∑ address : Fin (2 ^ 128), instructionLookupRa witness address t *
        ((1 - witness.InstructionRafFlag t) * lookupAddressRight address +
          witness.InstructionRafFlag t * (address.val : F))

end JoltConstraints
