import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (50) in `constraints.md`:
The register selector agrees with the selected fixed bytecode row.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L598-L630 -/
def rdWaEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (program : JoltProgram) (witness : WitnessType F params) : Prop :=
  ∀ (register : Fin 128) (t : Fin params.traceLength),
    witness.RdWa register t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeRegisterSelector program bytecodeRdRegister register address.val *
          bytecodeRa witness address t

end JoltConstraints
