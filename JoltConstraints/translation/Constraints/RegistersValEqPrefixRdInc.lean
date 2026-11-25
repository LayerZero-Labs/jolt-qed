import JoltConstraints.translation.witness
import JoltBytecode.MathlibTactics
import LeanRV64D.Defs

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (42) in `constraints.md` (stage 5):
each register value is the sum of its write increments at strictly earlier cycles.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/relations/registers/val_evaluation.rs -/
def registersValEqPrefixRdInc {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (register : Fin 128) (t : Fin params.traceLength),
    witness.RegistersVal register t =
      ∑ cycle : Fin params.traceLength,
        if cycle.val < t.val then witness.RdWa register cycle * witness.RdInc cycle else 0

end JoltConstraints
