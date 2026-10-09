import JoltConstraints.Constraints.RightInstructionInputEqSelection
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

private theorem rightOperandFlagsExclusive (instruction : JoltISA.Instr) :
    ¬ (JoltMetadata.instructionFlag instruction .RightOperandIsImm = true ∧
      JoltMetadata.instructionFlag instruction .RightOperandIsRs2Value = true) := by
  cases instruction <;> simp [JoltMetadata.instructionFlag]

/-- The honest witness satisfies constraint (33). -/
theorem honestWitness_rightInstructionInputEqSelection
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    rightInstructionInputEqSelection
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · let instruction :=
      (getElem trace.bytecode
        (getElem trace.rows t.val h).rowIndex.val
        (getElem trace.rows t.val h).rowIndex.isLt).instruction
    have hex := rightOperandFlagsExclusive instruction
    dsimp [rightInstructionInputEqSelection, HonestTrace.honestWitness,
      TraceWitness.RightInstructionInput, TraceWitness.InstructionFlags]
    simp only [dif_pos h]
    by_cases himm : JoltMetadata.instructionFlag instruction .RightOperandIsImm = true
    · have hrs : JoltMetadata.instructionFlag instruction .RightOperandIsRs2Value = false := by
        cases hf : JoltMetadata.instructionFlag instruction .RightOperandIsRs2Value with
        | false => rfl
        | true => exact False.elim (hex ⟨himm, hf⟩)
      simp [instruction, himm, hrs]
    · cases himm' : JoltMetadata.instructionFlag instruction .RightOperandIsImm with
      | true => exact False.elim (himm himm')
      | false =>
        by_cases hrs : JoltMetadata.instructionFlag instruction .RightOperandIsRs2Value = true
        · simp [instruction, hrs]
        · cases hrs' : JoltMetadata.instructionFlag instruction .RightOperandIsRs2Value with
          | true => exact False.elim (hrs hrs')
          | false => simp
  · dsimp [rightInstructionInputEqSelection, HonestTrace.honestWitness,
      TraceWitness.RightInstructionInput, TraceWitness.InstructionFlags]
    simp [h]

end JoltConstraints
