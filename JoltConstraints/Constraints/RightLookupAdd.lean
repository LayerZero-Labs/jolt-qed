import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (08) in `constraints.md` (stage 1):
addition places the sum of the instruction inputs in the right lookup operand.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def rightLookupAdd {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .AddOperands t *
      (witness.RightLookupOperand t - witness.LeftInstructionInput t -
        witness.RightInstructionInput t) = 0

end JoltConstraints
