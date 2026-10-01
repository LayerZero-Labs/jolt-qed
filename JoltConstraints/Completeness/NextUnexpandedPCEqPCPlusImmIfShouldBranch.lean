import JoltConstraints.Constraints.NextUnexpandedPCEqPCPlusImmIfShouldBranch
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions

set_option autoImplicit false

namespace JoltConstraints

/-- Unrestricted completeness statement to investigate, not an admitted theorem.
Rust can terminate on a taken self-branch, leaving a zero padding successor.
The original constraint is retained, with no assumption excluding the example. -/
def honestWitness_nextUnexpandedPCEqPCPlusImmIfShouldBranchStatement
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (_terminated : trace.Terminated)
    (tracePadded : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) : Prop :=
    nextUnexpandedPCEqPCPlusImmIfShouldBranch
      (JoltProgram.honestWitness (F := F) params trace ramFits tracePadded bytecodeDomain)

end JoltConstraints
