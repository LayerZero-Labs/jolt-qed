import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (22) in `constraints.md` (stage 2):
ShouldJump is the jump flag multiplied by one minus the next no-op flag.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def shouldJumpEqJumpMulNotNextIsNoop {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.ShouldJump t = witness.OpFlags .Jump t * (1 - witness.NextIsNoop t)

end JoltConstraints
