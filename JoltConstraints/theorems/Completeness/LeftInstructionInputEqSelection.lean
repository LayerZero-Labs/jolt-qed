import JoltConstraints.translation.Constraints.LeftInstructionInputEqSelection
import JoltConstraints.translation.witness
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.witness_domain

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

private theorem leftOperandFlagsExclusive (instruction : JoltISA.Instr) :
    ¬ (JoltMetadata.instructionFlag instruction .LeftOperandIsPC = true ∧
      JoltMetadata.instructionFlag instruction .LeftOperandIsRs1Value = true) := by
  cases instruction <;> simp [JoltMetadata.instructionFlag]

/-- The honest witness satisfies constraint (32). -/
theorem honestWitness_leftInstructionInputEqSelection
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    leftInstructionInputEqSelection
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · let instruction :=
      (getElem trace.bytecode
        (getElem trace.rows t.val h).rowIndex.val
        (getElem trace.rows t.val h).rowIndex.isLt).instruction
    have hex := leftOperandFlagsExclusive instruction
    dsimp [leftInstructionInputEqSelection, HonestTrace.honestWitness,
      TraceWitness.LeftInstructionInput, TraceWitness.InstructionFlags]
    simp only [dite_eq_left h]
    by_cases hpc : JoltMetadata.instructionFlag instruction .LeftOperandIsPC = true
    · have hrs : JoltMetadata.instructionFlag instruction .LeftOperandIsRs1Value = false := by
        cases hf : JoltMetadata.instructionFlag instruction .LeftOperandIsRs1Value with
        | false => rfl
        | true => exact False.elim (hex ⟨hpc, hf⟩)
      simp [instruction, hpc, hrs]
    · cases hpc' : JoltMetadata.instructionFlag instruction .LeftOperandIsPC with
      | true => exact False.elim (hpc hpc')
      | false =>
        by_cases hrs : JoltMetadata.instructionFlag instruction .LeftOperandIsRs1Value = true
        · simp [instruction, hrs]
        · cases hrs' : JoltMetadata.instructionFlag instruction .LeftOperandIsRs1Value with
          | true => exact False.elim (hrs hrs')
          | false => simp
  · dsimp [leftInstructionInputEqSelection, HonestTrace.honestWitness,
      TraceWitness.LeftInstructionInput, TraceWitness.InstructionFlags]
    simp [h]

end JoltConstraints
