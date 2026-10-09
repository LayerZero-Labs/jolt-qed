import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.Constraints.RamReadData

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (38) in `constraints.md`:
Each final RAM word equals its initial value plus all write increments.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs#L135-L154 -/
def ramValFinalEqInitialPlusRamInc {F : Type} [Field F] {params : WitnessParams}
    (initialRam : Nat → BitVec 64) (witness : WitnessType F params) : Prop :=
  ∀ address : Fin params.ramSize,
    witness.RamValFinal address = ramInitialValue initialRam address.val +
      ∑ cycle : Fin params.traceLength, witness.RamRa address cycle * witness.RamInc cycle

end JoltConstraints
