import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (50) in `constraints.md`:
The register selector agrees with the selected fixed bytecode row.
Rust: https://github.com/a16z/jolt/blob/5def437f21a0006e13c063a03f0b5a7c9b93cd6f/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L657-L689 -/
def rdWaEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow) (witness : WitnessType F params) : Prop :=
  ∀ (register : Fin 128) (t : Fin params.traceLength),
    witness.RdWa register t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeRegisterSelector bytecode bytecodeRdRegister register address.val *
          bytecodeRa witness address t

end JoltConstraints
