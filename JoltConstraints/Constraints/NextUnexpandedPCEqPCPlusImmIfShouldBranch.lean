import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (16) in `constraints.md` (stage 1):
a taken branch advances the unexpanded PC by its immediate.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def nextUnexpandedPCEqPCPlusImmIfShouldBranch {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.ShouldBranch t *
      (witness.NextUnexpandedPC t - witness.UnexpandedPC t - witness.Imm t) = 0

/-- Unrestricted completeness statement to investigate, not an admitted theorem.
Rust can terminate on a taken self-branch, leaving a zero padding successor.
The original constraint is retained, with no assumption excluding the example. -/
def honestWitness_nextUnexpandedPCEqPCPlusImmIfShouldBranchStatement
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (terminated : trace.Terminated)
    (tracePadded : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) : Prop :=
    nextUnexpandedPCEqPCPlusImmIfShouldBranch
      (JoltProgram.honestWitness (F := F) params trace ramFits tracePadded bytecodeDomain)

end JoltConstraints
