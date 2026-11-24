import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.witness_helpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (34) in `constraints.md` (stage 4):
the destination selector reads the register value plus its write increment.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/relations/registers/read_write_checking.rs#L97-L121 -/
def rdWriteValueEqRegistersReadWrite {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.RdWriteValue t =
      ∑ register : Fin 128,
        witness.RdWa register t * (witness.RegistersVal register t + witness.RdInc t)

end JoltConstraints
