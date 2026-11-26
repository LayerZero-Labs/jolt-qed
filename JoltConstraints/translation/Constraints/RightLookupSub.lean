import JoltConstraints.translation.witness
import JoltBytecode.MathlibTactics
import LeanRV64D.Defs

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (09) in `constraints.md` (stage 1):
subtraction places the biased difference of the inputs in the right lookup operand.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs -/
def rightLookupSub {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .SubtractOperands t *
      (witness.RightLookupOperand t - witness.LeftInstructionInput t +
        witness.RightInstructionInput t - (2 : F) ^ 64) = 0

end JoltConstraints
