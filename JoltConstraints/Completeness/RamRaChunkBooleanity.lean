import JoltConstraints.Constraints.RamRaChunkBooleanity
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies constraint (56). -/
theorem honestWitness_ramRaChunkBooleanity
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    ramRaChunkBooleanity
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro chunk entry t
  dsimp [HonestTrace.honestWitness, HonestWitness.RamRaChunk,
    HonestWitness.addressChunkEntry]
  cases h : HonestWitness.remappedRamAddress trace t.val <;> simp_all

end JoltConstraints
