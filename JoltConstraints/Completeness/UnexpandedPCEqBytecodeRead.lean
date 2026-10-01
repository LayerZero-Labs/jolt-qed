import JoltConstraints.Constraints.UnexpandedPCEqBytecodeRead
import JoltConstraints.Constraints.BytecodeReadData
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The honest witness satisfies constraint (44).
The bytecode domain must contain every program row and the leading no-op slot.
This bound prevents the address chunks from truncating an executed bytecode PC. -/
theorem honestWitness_unexpandedPCEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    unexpandedPCEqBytecodeRead program
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeAddress program) t]
  by_cases h : t.val < trace.rows.size
  · simp [JoltProgram.honestWitness, HonestWitness.UnexpandedPC,
      HonestWitness.bytecodePc, bytecodeAddress, bytecodeRow, h]
  · simp [JoltProgram.honestWitness, HonestWitness.UnexpandedPC,
      HonestWitness.bytecodePc, bytecodeAddress, bytecodeRow, h]

end JoltConstraints
