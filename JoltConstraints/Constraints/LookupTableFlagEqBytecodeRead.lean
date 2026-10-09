import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (51) in `constraints.md`:
The flag agrees with the selected fixed bytecode row.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L603-L609 -/
def lookupTableFlagEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow) (witness : WitnessType F params) : Prop :=
  ∀ (table : LookupTableKind) (t : Fin params.traceLength),
    witness.LookupTableFlag table t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeLookupTableFlag bytecode table address.val * bytecodeRa witness address t

end JoltConstraints
