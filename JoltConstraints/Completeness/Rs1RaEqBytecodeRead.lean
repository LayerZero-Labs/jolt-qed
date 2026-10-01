import JoltConstraints.Constraints.Rs1RaEqBytecodeRead
import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
The domain contains every expanded row and the leading no-op slot. -/
theorem honestWitness_rs1RaEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    : rs1RaEqBytecodeRead program
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro register t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeRegisterSelector program bytecodeRs1Register register) t]
  by_cases h : t.val < trace.rows.size
  · simp [JoltProgram.honestWitness, HonestWitness.Rs1Ra,
      HonestWitness.bytecodePc, bytecodeRegisterSelector, bytecodeRow, h]
    cases hinst :
      program.expandedBytecode[↑(trace.rows[↑t].rowIndex)].expandedInstruction <;>
      simp [bytecodeRs1Register, eq_comm]
  · simp [JoltProgram.honestWitness, HonestWitness.Rs1Ra,
      HonestWitness.bytecodePc, bytecodeRegisterSelector, bytecodeRow, h]

end JoltConstraints
