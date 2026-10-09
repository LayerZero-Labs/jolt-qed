import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.Constraints.BytecodeReadData
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (46) in `constraints.md` (stages 6a–6b):
each circuit flag is selected from the fixed bytecode table.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L545-L557 -/
def opFlagsEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow) (witness : WitnessType F params) : Prop :=
  ∀ (flag : CircuitFlags) (t : Fin params.traceLength),
    witness.OpFlags flag t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeCircuitFlag bytecode flag address.val * bytecodeRa witness address t

end JoltConstraints
