import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (21) in `constraints.md` (stage 2):
ShouldBranch is the lookup output multiplied by the branch flag.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def shouldBranchEqLookupOutputMulBranch {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.ShouldBranch t = witness.LookupOutput t * witness.InstructionFlags .Branch t

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_shouldBranchEqLookupOutputMulBranch
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size) :
    shouldBranchEqLookupOutputMulBranch
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  sorry

end JoltConstraints
