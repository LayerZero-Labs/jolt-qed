import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.Constraints.BytecodeReadData
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (43) in `constraints.md` (stages 6a–6b):
the expanded PC is the selected bytecode slot.
Rust: https://github.com/a16z/jolt/blob/5def437f21a0006e13c063a03f0b5a7c9b93cd6f/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L360-L380 -/
def pcEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ (t : Fin params.traceLength),
    witness.PC t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        (address.val : F) * bytecodeRa witness address t

end JoltConstraints
