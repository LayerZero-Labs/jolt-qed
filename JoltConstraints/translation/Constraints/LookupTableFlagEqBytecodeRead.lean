import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.Constraints.BytecodeReadSelectors
import JoltConstraints.translation.witness_helpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (51) in `constraints.md`:
The flag agrees with the selected fixed bytecode row.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs -/
def lookupTableFlagEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow) (witness : WitnessType F params) : Prop :=
  ∀ (table : LookupTableKind) (t : Fin params.traceLength),
    witness.LookupTableFlag table t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeLookupTableFlag bytecode table address.val * bytecodeRa witness address t

end JoltConstraints
