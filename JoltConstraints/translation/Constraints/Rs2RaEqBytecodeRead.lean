import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.Constraints.BytecodeReadSelectors
import JoltConstraints.translation.witness_helpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (49) in `constraints.md`:
The register selector agrees with the selected fixed bytecode row.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L655-L682 -/
def rs2RaEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow) (witness : WitnessType F params) : Prop :=
  ∀ (register : Fin 128) (t : Fin params.traceLength),
    witness.Rs2Ra register t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeRegisterSelector bytecode bytecodeRs2Register register address.val *
          bytecodeRa witness address t

end JoltConstraints
