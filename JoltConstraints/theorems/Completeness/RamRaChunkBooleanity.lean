import JoltConstraints.translation.Constraints.RamRaChunkBooleanity
import JoltConstraints.translation.witness
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.witness_domain

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies constraint (56). -/
theorem honestWitness_ramRaChunkBooleanity
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    ramRaChunkBooleanity
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro chunk entry t
  dsimp [HonestTrace.honestWitness, TraceWitness.RamRaChunk,
    TraceWitness.addressChunkEntry]
  cases h : TraceWitness.remappedRamAddress trace t.val <;> simp_all

end JoltConstraints
