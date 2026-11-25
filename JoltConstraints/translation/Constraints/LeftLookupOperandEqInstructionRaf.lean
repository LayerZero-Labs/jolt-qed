import JoltConstraints.translation.Constraints.LookupOperandData
import JoltConstraints.translation.Constraints.InstructionLookupRa

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (40) in `constraints.md`:
The left lookup operand is zero for identity RAF and the deinterleaved left value otherwise.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs -/
def leftLookupOperandEqInstructionRaf {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.LeftLookupOperand t =
      ∑ address : Fin (2 ^ 128), instructionLookupRa witness address t *
        (1 - witness.InstructionRafFlag t) * lookupAddressLeft address

end JoltConstraints
