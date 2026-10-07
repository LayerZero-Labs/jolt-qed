import JoltConstraints.Constraints.InstructionRaChunkBooleanity
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies constraint (54). -/
theorem honestWitness_instructionRaChunkBooleanity
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    instructionRaChunkBooleanity
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro chunk entry t
  dsimp [HonestTrace.honestWitness, HonestWitness.InstructionRaChunk,
    HonestWitness.addressChunkEntry]
  split_ifs <;> simp_all

end JoltConstraints
