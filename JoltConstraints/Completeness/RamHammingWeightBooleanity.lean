import JoltConstraints.Constraints.RamHammingWeightBooleanity
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies constraint (57). -/
theorem honestWitness_ramHammingWeightBooleanity
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    ramHammingWeightBooleanity
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  dsimp [HonestTrace.honestWitness, TraceWitness.RamHammingWeight]
  split_ifs
  · split <;> (try split_ifs) <;> simp_all
  · simp

end JoltConstraints
