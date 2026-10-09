import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (16) in `constraints.md` (stage 1):
a taken branch advances the unexpanded PC by its immediate.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def nextUnexpandedPCEqPCPlusImmIfShouldBranch {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.ShouldBranch t *
      (witness.NextUnexpandedPC t - witness.UnexpandedPC t - witness.Imm t) = 0

end JoltConstraints
