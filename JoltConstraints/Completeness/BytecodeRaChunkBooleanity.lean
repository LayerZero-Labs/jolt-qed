import JoltConstraints.Constraints.BytecodeRaChunkBooleanity
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies constraint (55). -/
theorem honestWitness_bytecodeRaChunkBooleanity
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    bytecodeRaChunkBooleanity
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro chunk entry t
  dsimp [JoltProgram.honestWitness, HonestWitness.BytecodeRaChunk,
    HonestWitness.addressChunkEntry]
  split_ifs <;> simp_all

end JoltConstraints
