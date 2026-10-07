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
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    instructionRaChunkHammingWeight
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro chunk t
  dsimp [instructionRaChunkHammingWeight, HonestTrace.honestWitness,
    HonestWitness.InstructionRaChunk]
  exact HonestWitness.sum_addressChunkEntry_some params.chunkBits chunk
    (HonestWitness.lookupIndex trace t.val).toNat

end JoltConstraints
