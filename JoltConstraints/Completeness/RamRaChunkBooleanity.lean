import JoltConstraints.Constraints.RamRaChunkBooleanity
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies constraint (56). -/
theorem honestWitness_ramRaChunkBooleanity
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    ramRaChunkBooleanity
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro chunk entry t
  dsimp [JoltProgram.honestWitness, HonestWitness.RamRaChunk,
    HonestWitness.addressChunkEntry]
  cases h : HonestWitness.remappedRamAddress trace t.val <;> simp_all

end JoltConstraints
