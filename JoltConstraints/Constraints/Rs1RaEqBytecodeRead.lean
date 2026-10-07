import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (48) in `constraints.md`:
The register selector agrees with the selected fixed bytecode row.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L598-L630 -/
def rs1RaEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (witness : WitnessType F params) : Prop :=
  ∀ (register : Fin 128) (t : Fin params.traceLength),
    witness.Rs1Ra register t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeRegisterSelector trace bytecodeRs1Register register address.val *
          bytecodeRa witness address t

end JoltConstraints
