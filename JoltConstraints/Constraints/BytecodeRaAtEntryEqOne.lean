import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (53) in `constraints.md`:
At cycle zero, the full bytecode selector selects the supplied public entry slot.
The entry slot comes from preprocessing; it need not be slot 1.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L358-L378 -/
def bytecodeRaAtEntryEqOne {F : Type} [Field F] {params : WitnessParams}
    (entry : Fin (2 ^ params.logBytecodeK)) (witness : WitnessType F params) : Prop :=
  bytecodeRa witness entry ⟨0, pow_pos (by decide : 0 < (2 : Nat)) _⟩ = 1

end JoltConstraints
