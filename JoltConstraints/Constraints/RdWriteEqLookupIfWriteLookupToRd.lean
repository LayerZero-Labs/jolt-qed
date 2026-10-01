import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.Constraints.TracePCProofHelpers

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (13) in `constraints.md` (stage 1):
rows with WriteLookupOutputToRD copy the lookup output to the destination.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def rdWriteEqLookupIfWriteLookupToRd {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .WriteLookupOutputToRD t *
      (witness.RdWriteValue t - witness.LookupOutput t) = 0

end JoltConstraints
