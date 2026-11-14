import JoltConstraints.translation.Constraints.NextIsFirstInSequenceEqShift
import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.witness_domain

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies the NextIsFirstInSequence shift constraint at every padded cycle. -/
theorem honestWitness_nextIsFirstInSequenceEqShift
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    nextIsFirstInSequenceEqShift
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  rfl

end JoltConstraints
