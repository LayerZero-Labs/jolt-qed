import JoltConstraints.translation.witness
import JoltBytecode.MathlibTactics
import LeanRV64D.Defs

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (13) in `constraints.md` (stage 1):
rows with WriteLookupOutputToRD copy the lookup output to the destination.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs -/
def rdWriteEqLookupIfWriteLookupToRd {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .WriteLookupOutputToRD t *
      (witness.RdWriteValue t - witness.LookupOutput t) = 0

end JoltConstraints
