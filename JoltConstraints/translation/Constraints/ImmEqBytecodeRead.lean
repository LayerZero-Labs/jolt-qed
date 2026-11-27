import JoltConstraints.translation.Constraints.BytecodeReadData

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (45) in `constraints.md` (stages 6a–6b):
the immediate is the selected row's normalized immediate.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L721-L845 -/
def immEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow) (witness : WitnessType F params) : Prop :=
  ∀ (t : Fin params.traceLength),
    witness.Imm t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeImmediate bytecode address.val * bytecodeRa witness address t

end JoltConstraints
