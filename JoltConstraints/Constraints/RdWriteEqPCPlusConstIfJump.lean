import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions
import JoltConstraints.Constraints.JumpReturnProofHelpers

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (14) in `constraints.md` (stage 1):
jumps write the return address, accounting for compressed instructions.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def rdWriteEqPCPlusConstIfJump {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .Jump t *
      (witness.RdWriteValue t - witness.UnexpandedPC t - 4 +
        2 * witness.OpFlags .IsCompressed t) = 0

end JoltConstraints
