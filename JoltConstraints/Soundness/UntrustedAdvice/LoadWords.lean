import JoltConstraints.Soundness.Layer2.Registers
import JoltConstraints.Soundness.Layer4.Inputs
import JoltConstraints.Soundness.Layer4.Interleaved
import JoltConstraints.Soundness.Layer6.BytecodePC
import JoltConstraints.Soundness.Layer7.AdjacentRows

open LeanRV64D

/-! Every load row's RAM read value is a 64-bit word.
Jolt's verifier holds only a commitment to the untrusted-advice words, so the
initial RAM value at a first access can be any field element.
Each load range-checks the doubleword it reads, so a row with the Load flag
cannot read such a value.
LD feeds its destination value into the right lookup operand.
A narrow load (`VirtualLoadB/H/W`) writes a register that a later row of the
same expansion reads as its left lookup operand, after a mask row that leaves
the register unchanged.
See a16z/jolt#2190 (merge commit 4e55c9a5) and
`jolt/crates/jolt-program/src/expand/memory/` at a6b6dc717. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness.UntrustedAdvice

open AdjacentRows

/-- A load that does not range-check its own destination value: a row with the Load flag
whose destination value does not pass through a lookup operand of the same row
(`ExpansionFacts.loadSelfChecked`). For example, `VirtualLoadB` is narrow, while `LD`
checks its value through its right lookup operand and is not. -/
def NarrowLoad (instruction : JoltISA.Instr) : Prop :=
  JoltMetadata.opcodeFlag instruction .Load = true ∧
    ExpansionFacts.loadSelfChecked instruction = false

/-- A load, a mask row that leaves the load's destination unchanged, and a row that
reads that destination as its left lookup operand. For example, the `LB` expansion
starts with `VirtualLoadB` into `dw`, then `VirtualWindowMaskB` into a lane register
other than `dw`, then `VirtualPextSigned` reading `dw` as `rs1`: these three rows form a
load window for `dw`. -/
def LoadWindow (window : Fin 3 → JoltISA.Instr) : Prop :=
  ∃ register, bytecodeRdRegister (window 0) = some register ∧
    bytecodeRdRegister (window 1) ≠ some register ∧
    ExpansionFacts.leftOperandIsRegister register (window 2) = true

/-- The expansion checker places every narrow load at the start of a load window. -/
theorem loadWindowsOk_windows : ∀ instructions : List JoltISA.Instr,
    ExpansionFacts.loadWindowsOk instructions = true →
      Windows NarrowLoad LoadWindow 0 instructions
  | [], _ => by intro k inRange; simp at inRange
  | instruction :: rest, ok => by
    simp only [ExpansionFacts.loadWindowsOk, Bool.and_eq_true] at ok
    obtain ⟨head, tail⟩ := ok
    intro k inRange choose
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero] at choose
      obtain ⟨load, notSelf⟩ := choose
      simp only [load, notSelf, Bool.not_true, Bool.false_or] at head
      cases destination : bytecodeRdRegister instruction with
      | none => simp [destination] at head
      | some register =>
        rcases rest with _ | ⟨mask, _ | ⟨consumer, others⟩⟩
        · simp [destination] at head
        · simp [destination] at head
        · simp only [destination, Bool.and_eq_true, bne_iff_ne, ne_eq] at head
          refine ⟨0, by simp, by simp, register, ?_, ?_, ?_⟩
          · simpa using destination
          · simpa using head.1
          · simpa using head.2
    | succ k =>
      obtain ⟨j, fits, position, related⟩ := loadWindowsOk_windows rest tail k
        (by simp only [List.length_cons] at inRange; omega)
        (by simpa only [List.getElem_cons_succ] using choose)
      have bound : j + 1 + 3 ≤ (instruction :: rest).length := by
        simp only [List.length_cons]; omega
      refine ⟨j + 1, bound, by simp only [Fin.val_zero] at position ⊢; omega, ?_⟩
      have same : (fun i : Fin 3 =>
            (instruction :: rest)[j + 1 + i.val]'(window_bound bound i)) =
          fun i => rest[j + i.val]'(window_bound fits i) := by
        funext i
        have shift : j + 1 + i.val = (j + i.val) + 1 := by omega
        simp only [shift, List.getElem_cons_succ]
      rw [same]
      exact related

/-- Every narrow load in an expanded program starts a load window inside its own
source instruction. -/
theorem expand_program_loadWindows (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow) (expanded : expand_program image = some bytecode) :
    Windows (fun row => NarrowLoad row.instruction) (WithinSource LoadWindow) 0
      bytecode.toList :=
  expand_program_windows (fun instructions => ExpansionFacts.loadWindowsOk instructions = true)
    NarrowLoad LoadWindow 0 loadWindowsOk_windows
    (ExpansionFacts.expand_instruction_property _ ExpansionFacts.nativeRowOk_loadWindowsOk
      ExpansionFacts.sequenceOk_loadWindowsOk)
    image bytecode expanded

/-- A narrow load at bytecode slot `slot` is followed by its mask row and its
consumer row at the next two slots, and neither the load nor the mask row ends
its source instruction. -/
theorem narrowLoad_window {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} {params : WitnessParams}
    (context : ConstraintContext joltInstance privateInputs params)
    {slot : Nat} {row : JoltInstructionRow}
    (rowIs : bytecodeRow context.bytecode slot = some row)
    (narrow : NarrowLoad row.instruction) :
    ∃ register mask consumer,
      bytecodeRow context.bytecode (slot + 1) = some mask ∧
      bytecodeRow context.bytecode (slot + 2) = some consumer ∧
      bytecodeRdRegister row.instruction = some register ∧
      bytecodeRdRegister mask.instruction ≠ some register ∧
      ExpansionFacts.leftOperandIsRegister register consumer.instruction = true ∧
      row.virtual_sequence_remaining.getD 0 ≠ 0 ∧
      mask.virtual_sequence_remaining.getD 0 ≠ 0 := by
  cases slot with
  | zero => simp [bytecodeRow] at rowIs
  | succ index =>
    simp only [bytecodeRow] at rowIs
    obtain ⟨bound, rowEq⟩ := Array.getElem?_eq_some_iff.mp rowIs
    obtain ⟨j, fits, position, ⟨register, writes, keeps, reads⟩, continues, _⟩ :=
      expand_program_loadWindows _ _ context.expands index
        (by simpa only [Array.length_toList] using bound)
        (by simpa only [Array.getElem_toList, rowEq] using narrow)
    simp only [Fin.val_zero, Nat.add_zero] at position
    subst position
    simp only [Array.length_toList] at fits
    refine ⟨register, context.bytecode[index + 1], context.bytecode[index + 2],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [bytecodeRow]
      exact Array.getElem?_eq_getElem _
    · simp only [bytecodeRow]
      exact Array.getElem?_eq_getElem _
    · simpa [Array.getElem_toList, rowEq] using writes
    · simpa [Array.getElem_toList] using keeps
    · simpa [Array.getElem_toList] using reads
    · have first := continues 0 (by decide)
      simp only [JoltInstructionRow.continues, bne_iff_ne] at first
      simpa [Array.getElem_toList, rowEq] using first
    · have second := continues 1 (by decide)
      simp only [JoltInstructionRow.continues, bne_iff_ne] at second
      simpa [Array.getElem_toList] using second

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  {initialValue : Nat → F}
  (equations : FieldConstraintEquations context.bytecode initialValue context.io
    context.entry witness)

include charAbove2pow127 context equations

/-- A row that feeds its destination value into the right lookup operand writes a
64-bit word.
For example, LD's destination value is the right half of its range-check lookup. -/
theorem selfChecked_rdWriteValue_word (t : Fin params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK)) (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    (self : ExpansionFacts.loadSelfChecked row.instruction = true) :
    ∃ value : BitVec 64, witness.RdWriteValue t = (value.toNat : F) := by
  simp only [ExpansionFacts.loadSelfChecked, Bool.and_eq_true, Bool.not_eq_true'] at self
  obtain ⟨⟨⟨rdFlag, rs2Off⟩, immOff⟩, rafOff⟩ := self
  have inputs := (instructionInputs_of_selected_bytecode charAbove2pow127 context equations
    t slot selected row rowIs).2
  simp only [rdFlag, rs2Off, immOff, ite_true, Bool.false_eq_true, ite_false, zero_add] at inputs
  have raf : witness.InstructionRafFlag t = 0 := by
    rw [instructionRafFlag_of_selected_bytecode charAbove2pow127 context equations t slot selected]
    simp [bytecodeRafFlag, rowIs, rafOff]
  obtain ⟨address, lookupSelected, _⟩ :=
    instructionLookupRa_unique charAbove2pow127 context equations t
  have operand := rightLookupOperand_of_selected charAbove2pow127 context equations
    t address lookupSelected
  rw [(lookupOperands_eq_inputs_of_raf_zero charAbove2pow127 context equations t raf).2,
    inputs, raf, lookupAddressRight_eq_uninterleave] at operand
  exact ⟨(uninterleave address).2, by simpa using operand⟩

/-- A narrow load writes a 64-bit word.
Its destination register is unchanged by the mask row and is read two rows later as
the left lookup operand, which is the left half of a lookup address. -/
theorem narrowLoad_rdWriteValue_word (t : Fin params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK)) (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    (narrow : NarrowLoad row.instruction) :
    ∃ value : BitVec 64, witness.RdWriteValue t = (value.toNat : F) := by
  obtain ⟨register, mask, consumer, maskIs, consumerIs, writes, keeps, reads, continues,
    maskContinues⟩ := narrowLoad_window context rowIs narrow
  have next1 := next_of_remaining charAbove2pow127 context equations t slot selected rowIs
    continues
  obtain ⟨slot1, selected1, slot1Is⟩ := selected_next_of_remaining charAbove2pow127 context
    equations t next1 slot selected rowIs continues
  have maskIs1 : bytecodeRow context.bytecode slot1.val = some mask := by
    rw [slot1Is]; exact maskIs
  have next2 := next_of_remaining charAbove2pow127 context equations _ slot1 selected1 maskIs1
    maskContinues
  obtain ⟨slot2, selected2, slot2Is⟩ := selected_next_of_remaining charAbove2pow127 context
    equations _ next2 slot1 selected1 maskIs1 maskContinues
  have consumerIs2 : bytecodeRow context.bytecode slot2.val = some consumer := by
    rw [slot2Is, slot1Is]; exact consumerIs
  -- the narrow load writes the register, and the mask row leaves it unchanged
  have step1 : witness.RegistersVal register ⟨t.val + 1, next1⟩ = witness.RdWriteValue t := by
    rw [registersVal_succ_of_selected_bytecode charAbove2pow127 context equations register t
      next1 slot selected]
    simp [rowIs, writes]
  have step2 : witness.RegistersVal register ⟨t.val + 1 + 1, next2⟩ =
      witness.RegistersVal register ⟨t.val + 1, next1⟩ := by
    rw [registersVal_succ_of_selected_bytecode charAbove2pow127 context equations register _
      next2 slot1 selected1]
    simp only [maskIs1, Option.bind_some]
    cases destination : bytecodeRdRegister mask.instruction with
    | none => rfl
    | some other =>
      have differs : register ≠ other := fun same => keeps (by rw [destination, same])
      simp [differs]
  simp only [ExpansionFacts.leftOperandIsRegister, Bool.and_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at reads
  obtain ⟨⟨⟨rs1Is, leftRs1⟩, leftPCOff⟩, rafOff⟩ := reads
  have rs1 := rs1Value_of_selected_bytecode charAbove2pow127 context equations _ slot2
    selected2
  simp only [consumerIs2, Option.bind_some, rs1Is] at rs1
  have inputs := (instructionInputs_of_selected_bytecode charAbove2pow127 context equations
    _ slot2 selected2 consumer consumerIs2).1
  simp only [leftRs1, leftPCOff, ite_true, Bool.false_eq_true, ite_false, add_zero] at inputs
  have raf : witness.InstructionRafFlag ⟨t.val + 1 + 1, next2⟩ = 0 := by
    rw [instructionRafFlag_of_selected_bytecode charAbove2pow127 context equations _ slot2
      selected2]
    simp [bytecodeRafFlag, consumerIs2, rafOff]
  obtain ⟨address, lookupSelected, _⟩ :=
    instructionLookupRa_unique charAbove2pow127 context equations ⟨t.val + 1 + 1, next2⟩
  have operand := leftLookupOperand_of_selected charAbove2pow127 context equations
    _ address lookupSelected
  rw [(lookupOperands_eq_inputs_of_raf_zero charAbove2pow127 context equations _ raf).1,
    inputs, rs1, raf, lookupAddressLeft_eq_uninterleave, step2, step1] at operand
  exact ⟨(uninterleave address).1, by simpa using operand⟩

/-- Every row with the Load flag writes a 64-bit word to its destination. -/
theorem load_rdWriteValue_word (t : Fin params.traceLength)
    (load : witness.OpFlags .Load t = 1) :
    ∃ value : BitVec 64, witness.RdWriteValue t = (value.toNat : F) := by
  obtain ⟨slot, selected, _⟩ := bytecodeRa_unique charAbove2pow127 context equations t
  have flag := opFlag_of_selected_bytecode charAbove2pow127 context equations .Load t slot
    selected
  rw [load] at flag
  cases rowIs : bytecodeRow context.bytecode slot.val with
  | none => simp [bytecodeCircuitFlag, rowIs] at flag
  | some row =>
    have loadFlag : JoltMetadata.opcodeFlag row.instruction .Load = true := by
      by_contra off
      simp [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, off] at flag
    cases self : ExpansionFacts.loadSelfChecked row.instruction
    · exact narrowLoad_rdWriteValue_word charAbove2pow127 context equations t slot selected
        rowIs ⟨loadFlag, self⟩
    · exact selfChecked_rdWriteValue_word charAbove2pow127 context equations t slot selected
        rowIs self

/-- Every row with the Load flag reads a 64-bit word from RAM.
Constraint 04 equates the read value with the destination value. -/
theorem load_ramReadValue_word (t : Fin params.traceLength)
    (load : witness.OpFlags .Load t = 1) :
    ∃ value : BitVec 64, witness.RamReadValue t = (value.toNat : F) := by
  obtain ⟨value, written⟩ := load_rdWriteValue_word charAbove2pow127 context equations t load
  have relation := equations.ramReadEqRdWriteIfLoad t
  rw [load, one_mul, sub_eq_zero] at relation
  exact ⟨value, relation.trans written⟩

end JoltConstraints.Soundness.UntrustedAdvice
