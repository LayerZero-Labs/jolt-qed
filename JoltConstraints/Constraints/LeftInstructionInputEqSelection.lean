import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (32) in `constraints.md` (stage 3):
the left instruction input is selected from Rs1Value and UnexpandedPC by the instruction flags.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs#L108-L127 -/
def leftInstructionInputEqSelection {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.LeftInstructionInput t =
      witness.InstructionFlags .LeftOperandIsRs1Value t * witness.Rs1Value t +
      witness.InstructionFlags .LeftOperandIsPC t * witness.UnexpandedPC t

private theorem leftOperandFlagsExclusive (instruction : JoltISA.Instr) :
    ¬ (JoltMetadata.instructionFlag instruction .LeftOperandIsPC = true ∧
      JoltMetadata.instructionFlag instruction .LeftOperandIsRs1Value = true) := by
  cases instruction <;> simp [JoltMetadata.instructionFlag]

/-- The honest witness satisfies constraint (32). -/
theorem honestWitness_leftInstructionInputEqSelection
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    leftInstructionInputEqSelection
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  by_cases h : t.val < trace.rows.size
  · let instruction :=
      (getElem program.expandedBytecode
        (getElem trace.rows t.val h).rowIndex.val
        (getElem trace.rows t.val h).rowIndex.isLt).instruction
    have hex := leftOperandFlagsExclusive instruction
    dsimp [leftInstructionInputEqSelection, JoltProgram.honestWitness,
      HonestWitness.LeftInstructionInput, HonestWitness.InstructionFlags]
    simp only [dif_pos h]
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
  · dsimp [leftInstructionInputEqSelection, JoltProgram.honestWitness,
      HonestWitness.LeftInstructionInput, HonestWitness.InstructionFlags]
    simp [h]

end JoltConstraints
