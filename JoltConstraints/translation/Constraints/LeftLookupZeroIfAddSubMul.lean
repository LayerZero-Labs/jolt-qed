import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.witness_helpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (06) in `constraints.md` (stage 1):
addition, subtraction and multiplication use zero as their left lookup operand.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs -/
def leftLookupZeroIfAddSubMul {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (witness.OpFlags .AddOperands t + witness.OpFlags .SubtractOperands t +
      witness.OpFlags .MultiplyOperands t) * witness.LeftLookupOperand t = 0

end JoltConstraints
