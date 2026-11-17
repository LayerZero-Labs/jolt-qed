import JoltConstraints.translation.Constraints.InstructionRaChunkBooleanity
import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.witness_domain

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies constraint (54). -/
theorem honestWitness_instructionRaChunkBooleanity
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    instructionRaChunkBooleanity
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro chunk entry t
  dsimp [HonestTrace.honestWitness, TraceWitness.InstructionRaChunk,
    TraceWitness.addressChunkEntry]
  split_ifs <;> simp_all

end JoltConstraints
