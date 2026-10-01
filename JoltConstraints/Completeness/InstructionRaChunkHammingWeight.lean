import JoltConstraints.Constraints.InstructionRaChunkHammingWeight
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The honest witness satisfies constraint (60). -/
theorem honestWitness_instructionRaChunkHammingWeight
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    instructionRaChunkHammingWeight
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro chunk t
  dsimp [instructionRaChunkHammingWeight, JoltProgram.honestWitness,
    HonestWitness.InstructionRaChunk]
  exact HonestWitness.sum_addressChunkEntry_some params.chunkBits chunk
    (HonestWitness.lookupIndex trace t.val).toNat

end JoltConstraints
