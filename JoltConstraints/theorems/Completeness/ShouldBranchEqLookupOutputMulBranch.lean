import JoltConstraints.translation.Constraints.ShouldBranchEqLookupOutputMulBranch
import JoltConstraints.translation.witness
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.witness_domain

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Completeness target for the honest witness. -/
theorem honestWitness_shouldBranchEqLookupOutputMulBranch
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    shouldBranchEqLookupOutputMulBranch
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · let row := getElem trace.rows t.val h
    let bytecodeRow := getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt
    dsimp [shouldBranchEqLookupOutputMulBranch, HonestTrace.honestWitness,
      TraceWitness.ShouldBranch, TraceWitness.LookupOutput,
      TraceWitness.InstructionFlags]
    simp only [dite_eq_left h]
    cases hi : bytecodeRow.instruction
    all_goals simp only [bytecodeRow, row] at hi
    all_goals simp [JoltMetadata.instructionFlag]
    all_goals
      simp [TraceWitness.rowLookupOutput, hi]
    all_goals split_ifs <;> simp
  · simp [HonestTrace.honestWitness, TraceWitness.ShouldBranch,
      TraceWitness.LookupOutput, TraceWitness.InstructionFlags, h]

end JoltConstraints
