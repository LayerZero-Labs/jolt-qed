import JoltConstraints.Soundness.Layer2.Registers
import JoltConstraints.Soundness.Layer2.RegisterMap
import JoltConstraints.Soundness.Layer2.ZeroLookup

/-! The x0 register-table entry remains zero in every satisfying witness.
Expansion permits only the canonical no-op to target x0. Its constraints force
a zero write when the old x0 value is zero; other rows cannot change that entry.
Induction discharges the old-value hypothesis, including padding cycles. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}

section NoOp

variable (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
  (selected : bytecodeRa witness chosen t = 1)
  {row : JoltInstructionRow} (present : bytecodeRow context.bytecode chosen.val = some row)
  (noOp : row.instruction = JoltISA.Instr.canonicalNoOp)

include charAbove2pow127 context equations selected present noOp

private theorem canonicalNoOp_inputs (zero : witness.RegistersVal 0 t = 0) :
    witness.LeftInstructionInput t = 0 ∧ witness.RightInstructionInput t = 0 := by
  have source := rs1Value_of_selected_bytecode charAbove2pow127 context equations t chosen selected
  have sourceZero : witness.Rs1Value t = 0 := by
    simpa [present, noOp, JoltISA.Instr.canonicalNoOp, bytecodeRs1Register,
      TraceWitness.sourceRegisterAddress, zero] using source
  have immediate := imm_of_selected_bytecode charAbove2pow127 context equations t chosen selected
  have immediateZero : witness.Imm t = 0 := by
    simpa [bytecodeImmediate, present, noOp, JoltISA.Instr.canonicalNoOp,
      JoltMetadata.immediate] using immediate
  have flags := instructionFlag_of_selected_bytecode charAbove2pow127 context equations
  constructor
  · rw [equations.leftInstructionInputEqSelection t, flags .LeftOperandIsRs1Value t chosen selected,
      flags .LeftOperandIsPC t chosen selected]
    simp [bytecodeInstructionFlag, present, noOp, JoltISA.Instr.canonicalNoOp,
      JoltMetadata.instructionFlag, sourceZero]
  · rw [equations.rightInstructionInputEqSelection t, flags .RightOperandIsRs2Value t chosen selected,
      flags .RightOperandIsImm t chosen selected]
    simp [bytecodeInstructionFlag, present, noOp, JoltISA.Instr.canonicalNoOp,
      JoltMetadata.instructionFlag, immediateZero]

private theorem canonicalNoOp_rightLookupOperand (zero : witness.RegistersVal 0 t = 0) :
    witness.RightLookupOperand t = 0 := by
  obtain ⟨left, right⟩ := canonicalNoOp_inputs charAbove2pow127 context equations t chosen
    selected present noOp zero
  have addFlag := opFlag_of_selected_bytecode charAbove2pow127 context equations
    .AddOperands t chosen selected
  have addOne : witness.OpFlags .AddOperands t = 1 := by
    simpa [bytecodeCircuitFlag, present, JoltMetadata.circuitFlag, noOp,
      JoltISA.Instr.canonicalNoOp, JoltMetadata.opcodeFlag] using addFlag
  simpa [addOne, left, right] using equations.rightLookupAdd t

private theorem canonicalNoOp_lookup_flags :
    witness.InstructionRafFlag t = 1 ∧
      ∀ table, witness.LookupTableFlag table t = if table = .RangeCheck then 1 else 0 := by
  constructor
  · have raf := instructionRafFlag_of_selected_bytecode charAbove2pow127 context equations t chosen selected
    simpa [bytecodeRafFlag, present, noOp, JoltISA.Instr.canonicalNoOp,
      JoltMetadata.instructionRafFlag, JoltMetadata.opcodeFlag] using raf
  · intro table
    rw [lookupTableFlag_of_selected_bytecode charAbove2pow127 context equations table t chosen selected]
    simp only [bytecodeLookupTableFlag, present, noOp]
    cases table <;> rfl

end NoOp

variable (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include charAbove2pow128 equations in
private theorem canonicalNoOp_rdInc
    (t : Fin params.traceLength) (chosen : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness chosen t = 1)
    {row : JoltInstructionRow} (present : bytecodeRow context.bytecode chosen.val = some row)
    (noOp : row.instruction = JoltISA.Instr.canonicalNoOp)
    (zero : witness.RegistersVal 0 t = 0) : witness.RdInc t = 0 := by
  have charAbove2pow127 : 2 ^ 127 < ringChar F := two_pow_127_lt_char charAbove2pow128
  have right := canonicalNoOp_rightLookupOperand charAbove2pow127 context equations t chosen selected present noOp zero
  obtain ⟨raf, tables⟩ := canonicalNoOp_lookup_flags charAbove2pow127 context equations t chosen selected present noOp
  have output := lookupOutput_rangeCheck_zero charAbove2pow128 context equations t raf right tables
  have writeFlag := opFlag_of_selected_bytecode charAbove2pow127 context equations
    .WriteLookupOutputToRD t chosen selected
  have writeOne : witness.OpFlags .WriteLookupOutputToRD t = 1 := by
    simpa [bytecodeCircuitFlag, present, JoltMetadata.circuitFlag, noOp,
      JoltISA.Instr.canonicalNoOp, JoltMetadata.opcodeFlag] using writeFlag
  have writeZero : witness.RdWriteValue t = 0 := by
    simpa [writeOne, output] using equations.rdWriteEqLookupIfWriteLookupToRd t
  have write := rdWriteValue_of_selected_bytecode charAbove2pow127 context equations t chosen selected
  simpa [present, noOp, JoltISA.Instr.canonicalNoOp, bytecodeRdRegister,
    TraceWitness.capturedDestination, TraceWitness.destinationRegisterAddress,
    zero, writeZero] using write.symm

private theorem canonicalNoOp_of_destination_zero
    {address : Nat} {row : JoltInstructionRow}
    (present : bytecodeRow context.bytecode address = some row)
    (destinationZero : bytecodeRdRegister row.instruction = some 0) :
    row.instruction = JoltISA.Instr.canonicalNoOp := by
  have rowOk := bytecodeRow_rowOk context present
  rw [bytecodeRdRegister_eq_destination] at destinationZero
  cases destinationIs : row.instruction.destination? with
  | none => simp [destinationIs] at destinationZero
  | some destination =>
    have addressZero : TraceWitness.destinationRegisterAddress destination = 0 := by
      simpa [destinationIs] using destinationZero
    have canonical := instruction_destination_canonical _ _ rowOk.canonical destinationIs
    have destinationEq : destination = .xreg (.Regidx 0) :=
      destinationRegisterAddress_injective canonical rfl addressZero
    subst destination
    exact rowOk.valid.x0DestinationIsNoOp _ destinationIs rfl

include charAbove2pow128 context equations

private theorem x0_increment_of_zero (t : Fin params.traceLength)
    (zero : witness.RegistersVal 0 t = 0) :
    witness.RdWa 0 t * witness.RdInc t = 0 := by
  have charAbove2pow127 : 2 ^ 127 < ringChar F := two_pow_127_lt_char charAbove2pow128
  obtain ⟨chosen, selected, _⟩ := bytecodeRa_unique charAbove2pow127 context equations t
  rw [rdWa_of_selected_bytecode charAbove2pow127 context equations 0 t chosen selected]
  cases present : bytecodeRow context.bytecode chosen.val with
  | none => simp [bytecodeRegisterSelector, present]
  | some row =>
    by_cases destinationZero : bytecodeRdRegister row.instruction = some 0
    · have noOp := canonicalNoOp_of_destination_zero context present destinationZero
      rw [canonicalNoOp_rdInc charAbove2pow128 context equations t chosen selected present noOp zero]
      simp
    · simp [bytecodeRegisterSelector, present, destinationZero]

/-- The x0 table entry is zero at every cycle, proved by induction from the
constraints and expanded bytecode alone. The old-value hypothesis used for the
no-op lookup is discharged by this induction. -/
theorem registersVal_x0 (t : Fin params.traceLength) : witness.RegistersVal 0 t = 0 := by
  obtain ⟨n, bound⟩ := t
  induction n with
  | zero => exact registersVal_zero equations.registersValEqPrefixRdInc 0
  | succ n ih =>
    have before : n < params.traceLength := by omega
    have zero := ih before
    rw [registersVal_succ equations.registersValEqPrefixRdInc 0 ⟨n, before⟩ bound,
      x0_increment_of_zero charAbove2pow128 context equations ⟨n, before⟩ zero,
      zero, add_zero]

/-- No cycle changes x0, including the final cycle, for which there is no next
register-table column. This is the write effect needed by the state induction. -/
theorem x0_write_effect_zero (t : Fin params.traceLength) :
    witness.RdWa 0 t * witness.RdInc t = 0 :=
  x0_increment_of_zero charAbove2pow128 context equations t
    (registersVal_x0 charAbove2pow128 context equations t)

end JoltConstraints.Soundness
