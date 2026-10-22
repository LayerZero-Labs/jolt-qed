import JoltConstraints.Soundness.Layer4.Table

/-! Connect instruction inputs to their selected bytecode sources and show that
interleaved lookup operands preserve those inputs. Agreement of the source
columns with the run's state is the later Layer 5b obligation. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include charAbove2pow127 context equations

/-- The selected instruction determines whether each input comes from a source
register, the PC, an immediate, or zero. The source columns are still field values. -/
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
        witness.Imm t else 0) := by
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
