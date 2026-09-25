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

/-- Completeness target for the honest witness. -/
theorem honestWitness_shouldBranchEqLookupOutputMulBranch
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    shouldBranchEqLookupOutputMulBranch
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · let row := getElem trace.rows t.val h
    let bytecodeRow := getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt
    dsimp [shouldBranchEqLookupOutputMulBranch, JoltProgram.honestWitness,
      HonestWitness.ShouldBranch, HonestWitness.LookupOutput,
      HonestWitness.InstructionFlags]
    simp only [dif_pos h]
    cases hi : bytecodeRow.instruction
    all_goals simp only [bytecodeRow, row] at hi
    all_goals simp [JoltMetadata.instructionFlag]
    all_goals
      simp [HonestWitness.rowLookupOutput, hi]
    all_goals split_ifs <;> simp
  · simp [JoltProgram.honestWitness, HonestWitness.ShouldBranch,
      HonestWitness.LookupOutput, HonestWitness.InstructionFlags, h]

end JoltConstraints
