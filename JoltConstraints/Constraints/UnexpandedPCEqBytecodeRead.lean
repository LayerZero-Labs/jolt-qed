import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.Constraints.BytecodeReadData
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (44) in `constraints.md` (stages 6a–6b):
the unexpanded PC is the selected row's raw instruction address.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L545-L557 -/
def unexpandedPCEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow) (witness : WitnessType F params) : Prop :=
  ∀ (t : Fin params.traceLength),
    witness.UnexpandedPC t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeAddress bytecode address.val * bytecodeRa witness address t

end JoltConstraints
