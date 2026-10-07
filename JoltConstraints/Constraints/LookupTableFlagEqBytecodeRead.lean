import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (51) in `constraints.md`:
The flag agrees with the selected fixed bytecode row.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L603-L609 -/
def lookupTableFlagEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (witness : WitnessType F params) : Prop :=
  ∀ (table : LookupTableKind) (t : Fin params.traceLength),
    witness.LookupTableFlag table t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeLookupTableFlag trace table address.val * bytecodeRa witness address t

end JoltConstraints
