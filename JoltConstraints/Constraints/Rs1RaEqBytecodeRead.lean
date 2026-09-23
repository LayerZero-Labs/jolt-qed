import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (48) in `constraints.md`:
The register selector agrees with the selected fixed bytecode row.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L598-L630 -/
def rs1RaEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (program : JoltProgram) (witness : WitnessType F params) : Prop :=
  ∀ (register : Fin 128) (t : Fin params.traceLength),
    witness.Rs1Ra register t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeRegisterSelector program bytecodeRs1Register register address.val *
          bytecodeRa witness address t

/-- Completeness target for the honest witness; proof pending.
The domain contains every expanded row and the leading no-op slot. -/
theorem honestWitness_rs1RaEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : trace.rows.size ≤ params.traceLength)
    (bytecodeFits : program.expandedBytecode.size + 1 ≤ 2 ^ params.logBytecodeK)
    : rs1RaEqBytecodeRead program
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  sorry

end JoltConstraints
