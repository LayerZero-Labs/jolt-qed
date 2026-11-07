import JoltConstraints.Soundness.Layer4.Table

open LeanRV64D

/-! Connect instruction inputs to their selected bytecode sources and show that
interleaved lookup operands preserve those inputs. Agreement of the source
columns with the run's state is the later Layer 5b obligation. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

/-- An instruction selecting rs1 as its left input cannot select the destination
value as its right input: only LD selects that destination value, and LD does
not select rs1 as an instruction input.
For example, ADD and ADDI both have the destination-value flag false. -/
theorem rdWriteInput_false_of_rs1Input (instruction : JoltISA.Instr)
    (source : JoltMetadata.instructionFlag instruction .LeftOperandIsRs1Value = true) :
    JoltMetadata.instructionFlag instruction .RightOperandIsRdWriteValue = false := by
  simp only [JoltMetadata.instructionFlag]
  split
  · simp [JoltMetadata.instructionFlag] at source
  · rfl

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include charAbove2pow127 context equations

/-- The selected instruction determines each input as a sum of its flagged
source columns, which are still field values.
For example, LD selects RdWriteValue, while VirtualShiftDataB selects Rs2Value
plus the signed immediate.
See Jolt's verifier at c6703570, `crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs`
(`InputVirtualization::unbatched_relation`). -/
theorem instructionInputs_of_selected_bytecode
    (t : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1) (row : JoltInstructionRow)
    (present : bytecodeRow context.bytecode slot.val = some row) :
    witness.LeftInstructionInput t =
      (if JoltMetadata.instructionFlag row.instruction .LeftOperandIsRs1Value then
        witness.Rs1Value t else 0) +
      (if JoltMetadata.instructionFlag row.instruction .LeftOperandIsPC then
        witness.UnexpandedPC t else 0) ∧
    witness.RightInstructionInput t =
      (if JoltMetadata.instructionFlag row.instruction .RightOperandIsRs2Value then
        witness.Rs2Value t else 0) +
      (if JoltMetadata.instructionFlag row.instruction .RightOperandIsImm then
        witness.Imm t else 0) +
      (if JoltMetadata.instructionFlag row.instruction .RightOperandIsRdWriteValue then
        witness.RdWriteValue t else 0) := by
  rw [equations.leftInstructionInputEqSelection t, equations.rightInstructionInputEqSelection t]
  simp_rw [instructionFlag_of_selected_bytecode charAbove2pow127 context equations
    _ t slot selected]
  simp [bytecodeInstructionFlag, present, ite_mul]

private theorem arithmeticAdviceFlags_zero_of_raf_zero (t : Fin params.traceLength)
    (raf : witness.InstructionRafFlag t = 0) :
    witness.OpFlags .AddOperands t = 0 ∧ witness.OpFlags .SubtractOperands t = 0 ∧
    witness.OpFlags .MultiplyOperands t = 0 ∧ witness.OpFlags .Advice t = 0 := by
  obtain ⟨slot, selected, _⟩ := bytecodeRa_unique charAbove2pow127 context equations t
  rw [instructionRafFlag_of_selected_bytecode charAbove2pow127 context equations
    t slot selected] at raf
  simp_rw [opFlag_of_selected_bytecode charAbove2pow127 context equations _ t slot selected]
  cases present : bytecodeRow context.bytecode slot.val with
  | none => simp [bytecodeCircuitFlag, present]
  | some row =>
    have flags : JoltMetadata.instructionRafFlag row.instruction = false := by
      simpa [bytecodeRafFlag, present] using raf
    simp only [JoltMetadata.instructionRafFlag, Bool.or_eq_false_iff] at flags
    simp [bytecodeCircuitFlag, present, JoltMetadata.circuitFlag,
      flags.1.1.1, flags.1.1.2, flags.1.2, flags.2]

/-- With RAF zero, neither arithmetic nor advice changes the operands: both
lookup operands equal their corresponding instruction inputs. -/
theorem lookupOperands_eq_inputs_of_raf_zero (t : Fin params.traceLength)
    (raf : witness.InstructionRafFlag t = 0) :
    witness.LeftLookupOperand t = witness.LeftInstructionInput t ∧
    witness.RightLookupOperand t = witness.RightInstructionInput t := by
  obtain ⟨add, sub, mul, advice⟩ :=
    arithmeticAdviceFlags_zero_of_raf_zero charAbove2pow127 context equations t raf
  have left := equations.leftLookupEqLeftInputOtherwise t
  have right := equations.rightLookupEqRightInputOtherwise t
  simp only [add, sub, mul, advice, sub_zero, one_mul, sub_eq_zero] at left right
  exact ⟨left, right⟩

end JoltConstraints.Soundness
