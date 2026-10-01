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
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (_terminated : trace.Terminated)
    (tracePadded : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    nextUnexpandedPCEqPCPlusImmIfShouldBranch
      (JoltProgram.honestWitness (F := F) params trace ramFits tracePadded bytecodeDomain) := by
  sorry

end JoltConstraints
