import JoltConstraints.translation.Constraints.BytecodeReadData

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (53) in `constraints.md`:
At cycle zero, the full bytecode selector selects the supplied public entry slot.
The entry slot comes from preprocessing; it need not be slot 1.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L401-L421 -/
def bytecodeRaAtEntryEqOne {F : Type} [Field F] {params : WitnessParams}
    (entry : Fin (2 ^ params.logBytecodeK)) (witness : WitnessType F params) : Prop :=
  bytecodeRa witness entry ⟨0, pow_pos (by decide : 0 < (2 : Nat)) _⟩ = 1

end JoltConstraints
