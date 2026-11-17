import JoltConstraints.translation.Constraints.RamHammingWeightBooleanity
import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.witness_domain

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies constraint (57). -/
theorem honestWitness_ramHammingWeightBooleanity
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    ramHammingWeightBooleanity
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  dsimp [HonestTrace.honestWitness, TraceWitness.RamHammingWeight]
  split_ifs
  · split <;> (try split_ifs) <;> simp_all
  · simp

end JoltConstraints
