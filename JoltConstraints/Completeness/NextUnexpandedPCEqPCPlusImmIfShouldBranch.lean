import JoltConstraints.Constraints.NextUnexpandedPCEqPCPlusImmIfShouldBranch
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions

set_option autoImplicit false

namespace JoltConstraints

/-- Completeness for the taken-branch next-PC constraint.
The proof is pending alignment of the Lean trace and witness model with the
reported Rust fix for the historical taken self-branch counterexample. -/
theorem honestWitness_nextUnexpandedPCEqPCPlusImmIfShouldBranch
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (_terminated : trace.Terminated)
    (tracePadded : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    nextUnexpandedPCEqPCPlusImmIfShouldBranch
      (HonestTrace.honestWitness (F := F) params trace) := by
  sorry

end JoltConstraints
