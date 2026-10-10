import JoltConstraints.Soundness.Layer1.Bytecode

/-! Each lemma reads a witness column at the slot selected by the bytecode
selector. `bytecodeRa_unique` supplies such a slot at every cycle, including
padding. Register results retain the fixed table's distinction between x0
and an absent operand. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F]
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  {params : WitnessParams} {witness : WitnessType F params}

/-- The expanded PC is the selected bytecode slot. -/
theorem pc_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.PC t = (chosen.val : F) := by
  rw [equations.pcEqBytecodeRead t]
  exact bytecode_read_of_selected charAbove2pow127 context equations t _ chosen selected

/-- The unexpanded PC is the selected slot's instruction address. -/
theorem unexpandedPC_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.UnexpandedPC t = bytecodeAddress context.bytecode chosen.val := by
  rw [equations.unexpandedPCEqBytecodeRead t]
  exact bytecode_read_of_selected charAbove2pow127 context equations t _ chosen selected

/-- The immediate is the selected slot's normalized immediate. -/
theorem imm_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.Imm t = bytecodeImmediate context.bytecode chosen.val := by
  rw [equations.immEqBytecodeRead t]
  exact bytecode_read_of_selected charAbove2pow127 context equations t _ chosen selected

/-- Each circuit flag comes from the selected bytecode slot. -/
theorem opFlag_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (flag : CircuitFlags) (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.OpFlags flag t = bytecodeCircuitFlag context.bytecode flag chosen.val := by
  rw [equations.opFlagsEqBytecodeRead flag t]
  exact bytecode_read_of_selected charAbove2pow127 context equations t _ chosen selected

/-- Each instruction flag comes from the selected bytecode slot. -/
theorem instructionFlag_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (flag : InstructionFlags) (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.InstructionFlags flag t = bytecodeInstructionFlag context.bytecode flag chosen.val := by
  rw [equations.instructionFlagsEqBytecodeRead flag t]
  exact bytecode_read_of_selected charAbove2pow127 context equations t _ chosen selected

/-- The first source-register selector comes from the selected bytecode slot. -/
theorem rs1Ra_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (register : Fin 128) (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.Rs1Ra register t = bytecodeRegisterSelector context.bytecode bytecodeRs1Register register chosen.val := by
  rw [equations.rs1RaEqBytecodeRead register t]
  exact bytecode_read_of_selected charAbove2pow127 context equations t _ chosen selected

/-- The second source-register selector comes from the selected bytecode slot. -/
theorem rs2Ra_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (register : Fin 128) (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.Rs2Ra register t = bytecodeRegisterSelector context.bytecode bytecodeRs2Register register chosen.val := by
  rw [equations.rs2RaEqBytecodeRead register t]
  exact bytecode_read_of_selected charAbove2pow127 context equations t _ chosen selected

/-- The destination-register selector comes from the selected bytecode slot. -/
theorem rdWa_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (register : Fin 128) (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.RdWa register t = bytecodeRegisterSelector context.bytecode bytecodeRdRegister register chosen.val := by
  rw [equations.rdWaEqBytecodeRead register t]
  exact bytecode_read_of_selected charAbove2pow127 context equations t _ chosen selected

/-- Each lookup-table flag comes from the selected bytecode slot. -/
theorem lookupTableFlag_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (table : LookupTableKind) (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.LookupTableFlag table t = bytecodeLookupTableFlag context.bytecode table chosen.val := by
  rw [equations.lookupTableFlagEqBytecodeRead table t]
  exact bytecode_read_of_selected charAbove2pow127 context equations t _ chosen selected

/-- `InstructionRafFlag` comes from the selected bytecode slot. A value of 1
means the right lookup operand is the whole 128-bit address and the left is zero;
0 means the address interleaves the two operands' bits. -/
theorem instructionRafFlag_of_selected_bytecode (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1) :
    witness.InstructionRafFlag t = bytecodeRafFlag context.bytecode chosen.val := by
  rw [equations.instructionRafFlagEqBytecodeRead t]
  exact bytecode_read_of_selected charAbove2pow127 context equations t _ chosen selected

end JoltConstraints.Soundness
