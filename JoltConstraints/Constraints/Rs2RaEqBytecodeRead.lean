import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (49) in `constraints.md`:
The register selector agrees with the selected fixed bytecode row.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L598-L630 -/
def rs2RaEqBytecodeRead {F : Type} [Field F] {params : WitnessParams}
    (program : JoltProgram) (witness : WitnessType F params) : Prop :=
  ∀ (register : Fin 128) (t : Fin params.traceLength),
    witness.Rs2Ra register t =
      ∑ address : Fin (2 ^ params.logBytecodeK),
        bytecodeRegisterSelector program bytecodeRs2Register register address.val *
          bytecodeRa witness address t

/-- Completeness target for the honest witness.
The domain contains every expanded row and the leading no-op slot. -/
theorem honestWitness_rs2RaEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    : rs2RaEqBytecodeRead program
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro register t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeRegisterSelector program bytecodeRs2Register register) t]
  by_cases h : t.val < trace.rows.size
  · simp [JoltProgram.honestWitness, HonestWitness.Rs2Ra,
      HonestWitness.bytecodePc, bytecodeRegisterSelector, bytecodeRow, h] <;>
      cases hinst :
        program.expandedBytecode[↑(trace.rows[↑t].rowIndex)].instruction <;>
      simp [bytecodeRs2Register, hinst, eq_comm]
  · simp [JoltProgram.honestWitness, HonestWitness.Rs2Ra,
      HonestWitness.bytecodePc, bytecodeRegisterSelector, bytecodeRow, h]

end JoltConstraints
