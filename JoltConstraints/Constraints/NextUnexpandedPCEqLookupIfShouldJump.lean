import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

namespace JoltConstraints

/-- Constraint (15) in `constraints.md` (stage 1):
a taken jump selects the lookup output as the next unexpanded PC.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def nextUnexpandedPCEqLookupIfShouldJump {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.ShouldJump t * (witness.NextUnexpandedPC t - witness.LookupOutput t) = 0

end JoltConstraints
