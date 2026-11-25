import JoltConstraints.translation.Constraints.BytecodeReadData

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (46) in `constraints.md` (stages 6a–6b):
each circuit flag is selected from the fixed bytecode table.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L606-L618 -/
def opFlagsEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow) (witness : WitnessType F params) : Prop :=
  ∀ (flag : CircuitFlags) (t : Fin params.traceLength),
    witness.OpFlags flag t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeCircuitFlag bytecode flag address.val * bytecodeRa witness address t

end JoltConstraints
