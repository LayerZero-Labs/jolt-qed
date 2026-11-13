import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.Constraints.RamReadData

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (37) in `constraints.md`:
Before cycle t, each word equals its initial value plus strictly earlier write increments.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs#L135-L154 -/
def ramValEqInitialPlusPrefixRamInc {F : Type} [Field F] {params : WitnessParams}
    (initialValue : Nat → F) (witness : WitnessType F params) : Prop :=
  ∀ (address : Fin params.ramSize) (t : Fin params.traceLength),
    witness.RamVal address t = initialValue address.val +
      ∑ cycle : Fin params.traceLength,
        if cycle.val < t.val then witness.RamRa address cycle * witness.RamInc cycle else 0

end JoltConstraints
