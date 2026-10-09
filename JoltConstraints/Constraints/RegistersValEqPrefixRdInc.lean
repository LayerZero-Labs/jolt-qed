import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (42) in `constraints.md` (stage 5):
each register value is the sum of its write increments at strictly earlier cycles.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/registers/val_evaluation.rs#L69-L79 -/
def registersValEqPrefixRdInc {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (register : Fin 128) (t : Fin params.traceLength),
    witness.RegistersVal register t =
      ∑ cycle : Fin params.traceLength,
        if cycle.val < t.val then witness.RdWa register cycle * witness.RdInc cycle else 0

end JoltConstraints
