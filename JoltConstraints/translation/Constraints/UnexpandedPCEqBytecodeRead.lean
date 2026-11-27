import JoltConstraints.translation.Constraints.BytecodeReadData

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (44) in `constraints.md` (stages 6a–6b):
the unexpanded PC is the selected row's raw instruction address.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L606-L618 -/
def unexpandedPCEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow) (witness : WitnessType F params) : Prop :=
  ∀ (t : Fin params.traceLength),
    witness.UnexpandedPC t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeAddress bytecode address.val * bytecodeRa witness address t

end JoltConstraints
