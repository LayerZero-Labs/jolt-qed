import JoltConstraints.translation.Constraints.RamReadData

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (37) in `constraints.md`:
Before cycle t, each word equals its initial value plus strictly earlier write increments.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs -/
def ramValEqInitialPlusPrefixRamInc {F : Type} [Field F] {params : WitnessParams}
    (initialRam : Nat → BitVec 64) (witness : WitnessType F params) : Prop :=
  ∀ (address : Fin params.ramSize) (t : Fin params.traceLength),
    witness.RamVal address t = ramInitialValue initialRam address.val +
      ∑ cycle : Fin params.traceLength,
        if cycle.val < t.val then witness.RamRa address cycle * witness.RamInc cycle else 0

end JoltConstraints
