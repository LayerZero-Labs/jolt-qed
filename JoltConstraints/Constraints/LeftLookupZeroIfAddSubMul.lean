import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (06) in `constraints.md` (stage 1):
addition, subtraction and multiplication use zero as their left lookup operand.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def leftLookupZeroIfAddSubMul {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (witness.OpFlags .AddOperands t + witness.OpFlags .SubtractOperands t +
      witness.OpFlags .MultiplyOperands t) * witness.LeftLookupOperand t = 0

end JoltConstraints
