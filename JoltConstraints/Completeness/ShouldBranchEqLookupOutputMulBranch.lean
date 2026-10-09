import JoltConstraints.Constraints.ShouldBranchEqLookupOutputMulBranch
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Completeness target for the honest witness. -/
theorem honestWitness_shouldBranchEqLookupOutputMulBranch
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    shouldBranchEqLookupOutputMulBranch
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · let row := getElem trace.rows t.val h
    let bytecodeRow := getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt
    dsimp [shouldBranchEqLookupOutputMulBranch, HonestTrace.honestWitness,
      TraceWitness.ShouldBranch, TraceWitness.LookupOutput,
      TraceWitness.InstructionFlags]
    simp only [dif_pos h]
    cases hi : bytecodeRow.instruction
    all_goals simp only [bytecodeRow, row] at hi
    all_goals simp [JoltMetadata.instructionFlag]
    all_goals
      simp [TraceWitness.rowLookupOutput, hi]
    all_goals split_ifs <;> simp
  · simp [HonestTrace.honestWitness, TraceWitness.ShouldBranch,
      TraceWitness.LookupOutput, TraceWitness.InstructionFlags, h]

end JoltConstraints
