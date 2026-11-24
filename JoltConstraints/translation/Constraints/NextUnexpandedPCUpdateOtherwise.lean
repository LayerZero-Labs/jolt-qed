import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.witness_helpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (17) in `constraints.md` (stage 1):
the remaining rows advance or preserve the unexpanded PC according to their flags.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs -/
def nextUnexpandedPCUpdateOtherwise {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (1 - witness.ShouldBranch t - witness.OpFlags .Jump t) *
      (witness.NextUnexpandedPC t - witness.UnexpandedPC t - 4 +
        4 * witness.OpFlags .DoNotUpdateUnexpandedPC t +
        2 * witness.OpFlags .IsCompressed t) = 0

end JoltConstraints
