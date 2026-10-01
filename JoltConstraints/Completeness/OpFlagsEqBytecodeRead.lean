import JoltConstraints.Constraints.OpFlagsEqBytecodeRead
import JoltConstraints.Constraints.BytecodeReadData
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The honest witness satisfies constraint (46).
The bytecode domain must contain every program row and the leading no-op slot.
This bound prevents the address chunks from truncating an executed bytecode PC. -/
theorem honestWitness_opFlagsEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    opFlagsEqBytecodeRead program
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro flag t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeCircuitFlag program flag) t]
  by_cases h : t.val < trace.rows.size
  · simp [JoltProgram.honestWitness, HonestWitness.OpFlags,
      HonestWitness.bytecodePc, bytecodeCircuitFlag, bytecodeRow, h]
  · cases flag <;>
      simp [JoltProgram.honestWitness, HonestWitness.OpFlags,
        HonestWitness.bytecodePc, bytecodeCircuitFlag, bytecodeRow, h]

end JoltConstraints
