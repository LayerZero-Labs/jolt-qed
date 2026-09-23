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

/-- Completeness target. Both selectors read the destination
recorded in the expanded row, including x0, without a second source rewrite.
The bytecode domain contains every expanded row and its leading padding slot. -/
theorem honestWitness_rdWaEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    : rdWaEqBytecodeRead program
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro register t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeRegisterSelector program bytecodeRdRegister register) t]
  by_cases h : t.val < trace.rows.size
  · simp [JoltProgram.honestWitness, HonestWitness.RdWa,
      HonestWitness.bytecodePc, bytecodeRegisterSelector, bytecodeRow, h]
    cases hinst :
      program.expandedBytecode[↑(trace.rows[↑t].rowIndex)].instruction <;>
      simp [bytecodeRdRegister, eq_comm]
  · simp [JoltProgram.honestWitness, HonestWitness.RdWa,
      HonestWitness.bytecodePc, bytecodeRegisterSelector, bytecodeRow, h]

end JoltConstraints
