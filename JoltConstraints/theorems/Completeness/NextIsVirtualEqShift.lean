import JoltConstraints.translation.Constraints.NextIsVirtualEqShift
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.witness_domain

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies the NextIsVirtual shift constraint at every padded cycle. -/
theorem honestWitness_nextIsVirtualEqShift
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    nextIsVirtualEqShift
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  rfl

end JoltConstraints
