import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.witness_helpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (12) in `constraints.md` (stage 1):
assertion rows require lookup output one.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs -/
def assertLookupOne {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength, witness.OpFlags .Assert t * (witness.LookupOutput t - 1) = 0

end JoltConstraints
