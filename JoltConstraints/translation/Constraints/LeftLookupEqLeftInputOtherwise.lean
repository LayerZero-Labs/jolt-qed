import JoltConstraints.translation.witness
import JoltBytecode.MathlibTactics
import LeanRV64D.Defs

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (07) in `constraints.md` (stage 1):
the other operand modes preserve the left instruction input.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs -/
def leftLookupEqLeftInputOtherwise {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (1 - witness.OpFlags .AddOperands t - witness.OpFlags .SubtractOperands t -
      witness.OpFlags .MultiplyOperands t) *
      (witness.LeftLookupOperand t - witness.LeftInstructionInput t) = 0

end JoltConstraints
