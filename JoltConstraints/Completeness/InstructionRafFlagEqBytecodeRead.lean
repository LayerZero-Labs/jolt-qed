import JoltConstraints.Constraints.InstructionRafFlagEqBytecodeRead
import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
The domain contains every expanded row and the leading no-op slot. -/
theorem honestWitness_instructionRafFlagEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    : instructionRafFlagEqBytecodeRead program
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeRafFlag program) t]
  by_cases h : t.val < trace.rows.size
  · simp [JoltProgram.honestWitness, HonestWitness.InstructionRafFlag,
      HonestWitness.bytecodePc, bytecodeRafFlag, bytecodeRow, h]
  · simp [JoltProgram.honestWitness, HonestWitness.InstructionRafFlag,
      HonestWitness.bytecodePc, bytecodeRafFlag, bytecodeRow, h]

end JoltConstraints
