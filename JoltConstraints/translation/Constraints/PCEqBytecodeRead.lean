import JoltConstraints.translation.Constraints.BytecodeReadData

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (43) in `constraints.md` (stages 6a–6b):
the expanded PC is the selected bytecode slot.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L401-L421 -/
def pcEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (t : Fin params.traceLength),
    witness.PC t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        (address.val : F) * bytecodeRa witness address t

end JoltConstraints
