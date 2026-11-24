import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.witness_helpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (08) in `constraints.md` (stage 1):
addition places the sum of the instruction inputs in the right lookup operand.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs -/
def rightLookupAdd {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .AddOperands t *
      (witness.RightLookupOperand t - witness.LeftInstructionInput t -
        witness.RightInstructionInput t) = 0

end JoltConstraints
