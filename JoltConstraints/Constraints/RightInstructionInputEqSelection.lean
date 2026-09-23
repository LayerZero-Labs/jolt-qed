import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (33) in `constraints.md` (stage 3):
the right instruction input is selected from Rs2Value and Imm by the instruction flags.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs#L108-L127 -/
def rightInstructionInputEqSelection {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.RightInstructionInput t =
      witness.InstructionFlags .RightOperandIsRs2Value t * witness.Rs2Value t +
      witness.InstructionFlags .RightOperandIsImm t * witness.Imm t

private theorem rightOperandFlagsExclusive (instruction : JoltISA.Instr) :
    ¬ (JoltMetadata.instructionFlag instruction .RightOperandIsImm = true ∧
      JoltMetadata.instructionFlag instruction .RightOperandIsRs2Value = true) := by
  cases instruction <;> simp [JoltMetadata.instructionFlag]

/-- The honest witness satisfies constraint (33). -/
theorem honestWitness_rightInstructionInputEqSelection
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    rightInstructionInputEqSelection
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · let instruction :=
      (getElem program.expandedBytecode
        (getElem trace.rows t.val h).rowIndex.val
        (getElem trace.rows t.val h).rowIndex.isLt).instruction
    have hex := rightOperandFlagsExclusive instruction
    dsimp [rightInstructionInputEqSelection, JoltProgram.honestWitness,
      HonestWitness.RightInstructionInput, HonestWitness.InstructionFlags]
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
  · dsimp [rightInstructionInputEqSelection, JoltProgram.honestWitness,
      HonestWitness.RightInstructionInput, HonestWitness.InstructionFlags]
    simp [h]

end JoltConstraints
