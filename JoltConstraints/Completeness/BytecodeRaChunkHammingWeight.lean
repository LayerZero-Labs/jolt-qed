import JoltConstraints.Constraints.BytecodeRaChunkHammingWeight
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The honest witness satisfies constraint (61). -/
theorem honestWitness_bytecodeRaChunkHammingWeight
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    bytecodeRaChunkHammingWeight
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro chunk t
  dsimp [bytecodeRaChunkHammingWeight, JoltProgram.honestWitness,
    HonestWitness.BytecodeRaChunk]
  exact HonestWitness.sum_addressChunkEntry_some params.chunkBits chunk
    (HonestWitness.bytecodePc trace t.val)

end JoltConstraints
