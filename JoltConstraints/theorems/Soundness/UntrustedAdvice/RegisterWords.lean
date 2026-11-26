import JoltConstraints.theorems.Soundness.UntrustedAdvice.LoadWords
import JoltConstraints.theorems.Soundness.Layer4.BitwiseEntry
import JoltConstraints.theorems.Soundness.Layer4.RotateEntry
import JoltConstraints.theorems.Soundness.Layer4.Outputs
import JoltConstraints.theorems.Soundness.Layer4.Table
import JoltConstraints.theorems.Soundness.Layer5.Jal
import JoltConstraints.theorems.Soundness.Layer7.StallSuffix

open LeanRV64D

/-! Every register-table entry of a satisfying witness is a 64-bit word.
The proof does not use the initial RAM values, so it holds when Jolt's verifier
adds arbitrary field elements for the untrusted-advice words.
Registers start at zero, and every row that writes a register writes a 64-bit word:
a load writes the doubleword its lookup range-checks (`LoadWords.lean`), a jump writes
its return address, and every other writing row writes its lookup output, which is
a 64-bit word in every table.
A store therefore stores a 64-bit word. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness.UntrustedAdvice

/-- A field element is a 64-bit word: the cast of some `BitVec 64`.
For example, `(5 : F)` is a word, and `2 ^ 64` is not when the characteristic is
larger than `2 ^ 64`. -/
def IsWord {F : Type} [Field F] (value : F) : Prop :=
  ∃ word : BitVec 64, value = (word.toNat : F)

section Table

variable {F : Type} [Field F]

theorem isWord_cast (word : BitVec 64) : IsWord (word.toNat : F) := ⟨word, rfl⟩

theorem isWord_zero : IsWord (0 : F) := ⟨0, by simp⟩

theorem isWord_one : IsWord (1 : F) := ⟨1, by simp⟩

theorem isWord_of_lt (value : Nat) (small : value < 2 ^ 64) : IsWord (value : F) :=
  ⟨BitVec.ofNat 64 value, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]⟩

/-- Every lookup-table entry is a 64-bit word.
For example, the And table gives the conjunction of the two operand words, and every
comparison table gives zero or one. -/
theorem lookupTableEntry_word (table : LookupTableKind) (address : Fin (2 ^ 128)) :
    IsWord (lookupTableEntry (F := F) table address) := by
  cases table
  case And =>
    simp only [lookupTableEntry]
    rw [← interleave_uninterleave address, and_entry]
    exact isWord_cast _
  case Or =>
    simp only [lookupTableEntry]
    rw [← interleave_uninterleave address, or_entry]
    exact isWord_cast _
  case Xor =>
    simp only [lookupTableEntry]
    rw [← interleave_uninterleave address, xor_entry]
    exact isWord_cast _
  case VirtualXORROTL1 =>
    simp only [lookupTableEntry]
    rw [← interleave_uninterleave address, xorRotL1_entry]
    exact isWord_cast _
  case AddressOffsetB | AddressOffsetH | AddressOffsetW =>
    simp only [lookupTableEntry, addressOffsetTableEntry]
    apply isWord_of_lt
    rw [BitVec.toNat_and]
    exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
  all_goals
    simp only [lookupTableEntry, rangeCheckTableEntry, rangeCheckAlignedTableEntry,
      andnTableEntry, equalTableEntry, signedGreaterThanEqualTableEntry,
      unsignedGreaterThanEqualTableEntry, notEqualTableEntry, signedLessThanTableEntry,
      unsignedLessThanTableEntry, signMaskTableEntry, upperWordTableEntry,
      unsignedLessThanEqualTableEntry, validUnsignedRemainderTableEntry, validDiv0TableEntry,
      lowerHalfWordTableEntry, signExtendWordTableEntry, pow2TableEntry, pow2WTableEntry,
      shiftRightBitmaskTableEntry, virtualRev8WTableEntry, virtualSRLTableEntry,
      virtualSRATableEntry, virtualROTRTableEntry, virtualROTRWTableEntry,
      virtualNegateIfTableEntry, mulUNoOverflowTableEntry, virtualXorRotTableEntry,
      virtualXorRotWTableEntry, windowMaskWTableEntry, pextSignedTableEntry,
      shiftRightBitmaskWTableEntry, virtualSRLWTableEntry, virtualSRAWTableEntry,
      pextTableEntry, windowMaskBTableEntry, windowMaskHTableEntry, shiftDataBTableEntry,
      shiftDataHTableEntry, shiftDataWTableEntry]
    repeat' split
    all_goals first
      | exact isWord_cast _
      | exact isWord_zero
      | exact isWord_one

end Table

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}

/-- Every instruction that names a destination register writes it through one of
three equations: the load equation, the jump equation, or the lookup-output equation.
For example, ADDI writes its lookup output and JAL writes its return address. -/
theorem destination_flags (instruction : JoltISA.Instr) {register : Fin 128}
    (destination : bytecodeRdRegister instruction = some register) :
    JoltMetadata.opcodeFlag instruction .Load = true ∨
      JoltMetadata.opcodeFlag instruction .Jump = true ∨
      JoltMetadata.opcodeFlag instruction .WriteLookupOutputToRD = true := by
  cases instruction <;> simp_all [bytecodeRdRegister, JoltMetadata.opcodeFlag]

/-- A jump row writes a 64-bit word, its return address.
The jump ends its source instruction, so the program image's no-wrap field bounds
the return address. -/
theorem jump_rdWriteValue_word (charAbove : 2 ^ 128 - 2 ^ 64 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    {initialValue : Nat → F}
    (equations : FieldConstraintEquations context.bytecode initialValue context.io
      context.entry witness)
    (t : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    (jump : JoltMetadata.opcodeFlag row.instruction .Jump = true) :
    IsWord (witness.RdWriteValue t) := by
  have ends := (bytecodeRow_rowOk context rowIs).ends
    (by simp [ExpansionFacts.ordinary, jump])
  have last : row.virtual_sequence_remaining.getD 0 = 0 := by
    simpa [JoltInstructionRow.continues] using ends
  obtain ⟨index, slotIs⟩ : ∃ index, slot.val = index + 1 := by
    cases value : slot.val with
    | zero => simp [bytecodeRow, value] at rowIs
    | succ index => exact ⟨index, rfl⟩
  rw [slotIs] at rowIs
  simp only [bytecodeRow] at rowIs
  obtain ⟨bound, rowEq⟩ := Array.getElem?_eq_some_iff.mp rowIs
  have lastAt : (context.bytecode[(⟨index, bound⟩ : Fin context.bytecode.size)]).virtual_sequence_remaining.getD 0 = 0 := by
    simpa only [Fin.getElem_fin, rowEq] using last
  have noWrap := expand_program_next_pc_no_wrap joltInstance.program context.bytecode
    context.expands joltInstance.program.next_pc_no_wrap ⟨index, bound⟩
  rw [JoltInstance.source_compressed_of_last context.bytecode ⟨index, bound⟩ lastAt] at noWrap
  simp only [Fin.getElem_fin, rowEq] at noWrap
  have rowIs' : bytecodeRow context.bytecode slot.val = some row := by
    rw [slotIs]; simpa only [bytecodeRow] using rowIs
  rw [jump_write_value charAbove context equations selected rowIs' jump noWrap]
  exact isWord_cast _

/-- A lookup-writing row writes a 64-bit word, its lookup output. -/
theorem lookup_rdWriteValue_word (charAbove2pow127 : 2 ^ 127 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    {initialValue : Nat → F}
    (equations : FieldConstraintEquations context.bytecode initialValue context.io
      context.entry witness)
    (t : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    (writes : JoltMetadata.opcodeFlag row.instruction .WriteLookupOutputToRD = true) :
    IsWord (witness.RdWriteValue t) := by
  have active : witness.OpFlags .WriteLookupOutputToRD t = 1 := by
    simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, writes] using!
      opFlag_of_selected_bytecode charAbove2pow127 context equations
        .WriteLookupOutputToRD t slot selected
  rw [rdWriteValue_eq_lookupOutput equations.rdWriteEqLookupIfWriteLookupToRd t active]
  obtain ⟨address, lookupSelected, _⟩ :=
    instructionLookupRa_unique charAbove2pow127 context equations t
  rw [lookupOutput_of_selected_bytecode charAbove2pow127 context equations t slot selected
    address lookupSelected]
  split
  · exact lookupTableEntry_word _ _
  · exact isWord_zero

/-- Every row that names a destination register writes a 64-bit word to it. -/
theorem rdWriteValue_word (charAbove : 2 ^ 128 - 2 ^ 64 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    {initialValue : Nat → F}
    (equations : FieldConstraintEquations context.bytecode initialValue context.io
      context.entry witness)
    (t : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow} (rowIs : bytecodeRow context.bytecode slot.val = some row)
    {register : Fin 128} (destination : bytecodeRdRegister row.instruction = some register) :
    IsWord (witness.RdWriteValue t) := by
  have charAbove2pow127 := two_pow_127_lt_char charAbove
  rcases destination_flags row.instruction destination with load | jump | writes
  · have active : witness.OpFlags .Load t = 1 := by
      simpa only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag, load] using!
        opFlag_of_selected_bytecode charAbove2pow127 context equations .Load t slot selected
    exact load_rdWriteValue_word charAbove2pow127 context equations t active
  · exact jump_rdWriteValue_word charAbove context equations t slot selected rowIs jump
  · exact lookup_rdWriteValue_word charAbove2pow127 context equations t slot selected rowIs
      writes

/-- Every register-table entry is a 64-bit word at every cycle.
For example, a register that a load wrote at cycle 3 holds the loaded doubleword at
cycle 4. -/
theorem registersVal_word (charAbove : 2 ^ 128 - 2 ^ 64 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    {initialValue : Nat → F}
    (equations : FieldConstraintEquations context.bytecode initialValue context.io
      context.entry witness)
    (register : Fin 128) (t : Fin params.traceLength) :
    IsWord (witness.RegistersVal register t) := by
  have charAbove2pow127 := two_pow_127_lt_char charAbove
  obtain ⟨n, inRange⟩ := t
  induction n generalizing register with
  | zero =>
    rw [registersVal_zero equations.registersValEqPrefixRdInc register]
    exact isWord_zero
  | succ n previous =>
    have before : n < params.traceLength := by omega
    obtain ⟨slot, selected, _⟩ := bytecodeRa_unique charAbove2pow127 context equations
      ⟨n, before⟩
    rw [registersVal_succ_of_selected_bytecode charAbove2pow127 context equations register
      ⟨n, before⟩ inRange slot selected]
    cases rowIs : bytecodeRow context.bytecode slot.val with
    | none => exact previous register before
    | some row =>
      simp only [Option.bind_some]
      cases destination : bytecodeRdRegister row.instruction with
      | none => exact previous register before
      | some written =>
        simp only
        split
        · exact rdWriteValue_word charAbove context equations ⟨n, before⟩ slot selected rowIs
            destination
        · exact previous register before

/-- Every second-source value is a 64-bit word; for example, the value an SD row
stores. -/
theorem rs2Value_word (charAbove : 2 ^ 128 - 2 ^ 64 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    {initialValue : Nat → F}
    (equations : FieldConstraintEquations context.bytecode initialValue context.io
      context.entry witness)
    (t : Fin params.traceLength) :
    IsWord (witness.Rs2Value t) := by
  have charAbove2pow127 := two_pow_127_lt_char charAbove
  obtain ⟨slot, selected, _⟩ := bytecodeRa_unique charAbove2pow127 context equations t
  rw [rs2Value_of_selected_bytecode charAbove2pow127 context equations t slot selected]
  split
  · exact isWord_zero
  · exact registersVal_word charAbove context equations _ t

end JoltConstraints.Soundness.UntrustedAdvice
