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
Rust: https://github.com/a16z/jolt/blob/5def437f21a0006e13c063a03f0b5a7c9b93cd6f/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L360-L380 -/
def bytecodeRaAtEntryEqOne {F : Type} [Field F] {params : WitnessParams}
    (entry : Fin (2 ^ params.logBytecodeK)) (witness : WitnessType F params) : Prop :=
  bytecodeRa witness entry ⟨0, pow_pos (by decide : 0 < (2 : Nat)) _⟩ = 1

end JoltConstraints
