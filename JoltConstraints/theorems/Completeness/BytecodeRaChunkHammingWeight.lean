import JoltConstraints.translation.Constraints.BytecodeRaChunkHammingWeight
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.witness_domain

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The honest witness satisfies constraint (61). -/
theorem honestWitness_bytecodeRaChunkHammingWeight
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    bytecodeRaChunkHammingWeight
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro chunk t
  dsimp [bytecodeRaChunkHammingWeight, HonestTrace.honestWitness,
    TraceWitness.BytecodeRaChunk]
  exact TraceWitness.sum_addressChunkEntry_some params.chunkBits chunk
    (TraceWitness.bytecodePc trace t.val)

end JoltConstraints
