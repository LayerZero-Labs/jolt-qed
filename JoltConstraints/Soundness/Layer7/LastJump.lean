import JoltConstraints.Soundness.Layer6.ExecutionPrefix
import JoltConstraints.Soundness.Layer6.BytecodePC

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions JoltISA

namespace JoltInstance

/-- At a represented real cycle, the selected bytecode slot is the executed
row's index plus one; for example, row zero occupies slot one. -/
private theorem selected_represented_row
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (cycle : Fin params.traceLength) (inRun : cycle.val < run.rows.size) :
    JoltConstraints.bytecodeRa witness
      ⟨run.rows[cycle.val].rowIndex.val + 1, by
        have domain : params.BytecodeDomainFor run.bytecode.size := by
          simpa only [bytecodeEq] using context.bytecodeDomain
        have fits := domain.rowsFit
        have rowBound := run.rows[cycle.val].rowIndex.isLt
        omega⟩ cycle = 1 := by
  obtain ⟨slot, selected, _⟩ := JoltConstraints.Soundness.bytecodeRa_unique
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField) context equations cycle
  have pcSelected := JoltConstraints.Soundness.pc_of_selected_bytecode
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    context equations cycle slot selected
  have pcRun := represented.pc cycle inRun
  have encoded : (slot.val : F) = ((run.rows[cycle.val].rowIndex.val + 1 : Nat) : F) := by
    rw [← pcSelected, pcRun]
    simp [TraceWitness.PC, TraceWitness.bytecodePc, inRun]
  have slotBound : slot.val < ringChar F := by
    have domain := params.logBytecodeK_lt_usizeBits
    have small : 2 ^ params.logBytecodeK ≤ 2 ^ 64 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have characteristic := JoltConstraints.Soundness.two_pow_64_lt_char
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    omega
  have rowBound : run.rows[cycle.val].rowIndex.val + 1 < ringChar F := by
    have domain : params.BytecodeDomainFor run.bytecode.size := by
      simpa only [bytecodeEq] using context.bytecodeDomain
    have fits := domain.rowsFit
    have small : 2 ^ params.logBytecodeK ≤ 2 ^ 64 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) params.logBytecodeK_lt_usizeBits.le
    have characteristic := JoltConstraints.Soundness.two_pow_64_lt_char
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    omega
  have same := JoltConstraints.Soundness.natCast_injective_below_char
    slotBound rowBound encoded
  have sameSlot : slot = ⟨run.rows[cycle.val].rowIndex.val + 1, by
      have domain : params.BytecodeDomainFor run.bytecode.size := by
        simpa only [bytecodeEq] using context.bytecodeDomain
      have fits := domain.rowsFit
      have rowBound := run.rows[cycle.val].rowIndex.isLt
      omega⟩ := Fin.ext same
  simpa only [sameSlot] using selected

/-- A selected padding cycle has unexpanded address zero, as the no-op slots
have no source address. -/
private theorem unexpanded_zero_of_padding
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength)
    (padding : witness.InstructionFlags .IsNoop cycle = 1) :
    witness.UnexpandedPC cycle = 0 := by
  obtain ⟨slot, selected, _⟩ := JoltConstraints.Soundness.bytecodeRa_unique
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField) context equations cycle
  have flag := JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    context equations .IsNoop cycle slot selected
  have noRow : JoltConstraints.bytecodeRow context.bytecode slot.val = none := by
    cases present : JoltConstraints.bytecodeRow context.bytecode slot.val with
    | none => rfl
    | some row =>
      simp [JoltConstraints.bytecodeInstructionFlag, present,
        JoltMetadata.instructionFlag, padding] at flag
  rw [JoltConstraints.Soundness.unexpandedPC_of_selected_bytecode
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    context equations cycle slot selected]
  simp [JoltConstraints.bytecodeAddress, noRow]

/-- A bytecode Jump flag identifies exactly a JAL or JALR row; for example,
the JAL generated from EBREAK has this flag. -/
private theorem jump_instruction_of_flag (instruction : JoltISA.Instr)
    (jump : JoltMetadata.opcodeFlag instruction .Jump = true) :
    (∃ dst imm, instruction = .JAL dst imm) ∨
      ∃ dst base imm, instruction = .JALR dst base imm := by
  cases instruction <;> simp_all [JoltMetadata.opcodeFlag]

/-- A bytecode Branch flag identifies one of the six conditional branches;
for example, BEQ carries this flag. -/
private theorem branch_instruction_of_flag (instruction : JoltISA.Instr)
    (branch : JoltMetadata.instructionFlag instruction .Branch = true) :
    ∃ lhs rhs imm,
      instruction = .BEQ lhs rhs imm ∨ instruction = .BNE lhs rhs imm ∨
      instruction = .BLT lhs rhs imm ∨ instruction = .BGE lhs rhs imm ∨
      instruction = .BLTU lhs rhs imm ∨ instruction = .BGEU lhs rhs imm := by
  cases instruction <;> simp_all [JoltMetadata.instructionFlag]

/-- A decoded branch at a valid bytecode address cannot target field address
zero: its signed 13-bit offset is smaller than the RAM start address. -/
private theorem branch_target_ne_zero
    {F : Type} [Field F] (joltField : JoltField F)
    (row : JoltInstructionRow) (valid : row.Valid)
    (addressOk : bytecode_address_ok row.address = true)
    (branch : JoltMetadata.instructionFlag row.instruction .Branch = true) :
    (row.address.toNat : F) + (JoltMetadata.immediate row.instruction : F) ≠ 0 := by
  obtain ⟨lhs, rhs, imm, isBranch⟩ := branch_instruction_of_flag row.instruction branch
  obtain ⟨_, offset, offsetEq⟩ := valid.branch isBranch
  have immediate : JoltMetadata.immediate row.instruction = offset.toInt := by
    have ext : (offset.signExtend 128).toInt = offset.toInt :=
      BitVec.toInt_signExtend_of_le (by decide)
    rcases isBranch with h | h | h | h | h | h
    all_goals simp [h, JoltMetadata.immediate, offsetEq, ext]
  have ram : JoltISA.RAM_START_ADDRESS ≤ row.address.toNat := by
    have h := addressOk
    simp only [bytecode_address_ok, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have low := BitVec.le_toInt offset
  have high := BitVec.toInt_lt (x := offset)
  have positive : 0 < (row.address.toNat : Int) + offset.toInt := by
    have ramStart : JoltISA.RAM_START_ADDRESS = 2147483648 := rfl
    rw [ramStart] at ram
    norm_num at low high
    omega
  let target : Nat := Int.toNat ((row.address.toNat : Int) + offset.toInt)
  have targetPositive : 0 < target := by
    dsimp [target]
    omega
  have targetBound : target < ringChar F := by
    have wordBound := row.address.isLt
    have charBound := JoltConstraints.Soundness.two_pow_64_lt_char
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    have stronger := JoltConstraints.Soundness.two_pow_127_lt_char joltField
    norm_num at high
    dsimp [target]
    omega
  intro zero
  have targetCast : (target : F) = 0 := by
    have targetInt : (target : Int) = (row.address.toNat : Int) + offset.toInt := by
      dsimp [target]
      omega
    calc
      (target : F) = ((target : Int) : F) := by norm_num
      _ = (((row.address.toNat : Int) + offset.toInt : Int) : F) := by rw [targetInt]
      _ = (row.address.toNat : F) + (JoltMetadata.immediate row.instruction : F) := by
        rw [immediate]
        norm_num
      _ = 0 := zero
  have targetZero : target = 0 :=
    JoltConstraints.Soundness.natCast_injective_below_char (b := 0) targetBound
      (by have h := JoltConstraints.Soundness.two_pow_127_lt_char joltField; omega)
      (by simpa using targetCast)
  omega

/-- An ordinary row with neither a jump nor a taken branch has a nonzero next
unexpanded PC when its current address is a real 64-bit address. For example,
an ADDI at `RAM_START_ADDRESS` advances by two or four bytes under constraint 17.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:347-353
at 8bbb2357. -/
private theorem ordinary_row_next_pc_nonzero
    {F : Type} [Field F] (joltField : JoltField F)
    {params : WitnessParams} (witness : WitnessType F params)
    (address : BitVec 64) (isCompressed : Bool)
    (update : JoltConstraints.nextUnexpandedPCUpdateOtherwise witness)
    (cycle : Fin params.traceLength)
    (currentPC : witness.UnexpandedPC cycle = (address.toNat : F))
    (jumpZero : witness.OpFlags .Jump cycle = 0)
    (branchZero : witness.ShouldBranch cycle = 0)
    (doNotZero : witness.OpFlags .DoNotUpdateUnexpandedPC cycle = 0)
    (compressed : witness.OpFlags .IsCompressed cycle =
      if isCompressed then (1 : F) else 0) :
    witness.NextUnexpandedPC cycle ≠ 0 := by
  intro zero
  have relation := update cycle
  rw [branchZero, jumpZero, zero, currentPC, doNotZero, compressed] at relation
  have successorCast :
      ((address.toNat + (if isCompressed then 2 else 4) : Nat) : F) = 0 := by
    cases h : isCompressed <;> simp [h] at relation ⊢ <;>
      linear_combination -relation
  have successorBound : address.toNat + (if isCompressed then 2 else 4) < ringChar F := by
    have wordBound := address.isLt
    have charBound := JoltConstraints.Soundness.two_pow_127_lt_char joltField
    split_ifs <;> omega
  have successorZero := JoltConstraints.Soundness.natCast_injective_below_char
    (b := 0) successorBound
    (by have h := JoltConstraints.Soundness.two_pow_127_lt_char joltField; omega)
    (by simpa using successorCast)
  split_ifs at successorZero

/-- A nonterminal virtual row advances the expanded bytecode PC by one slot.
For example, the first row of an ECALL expansion selects the next ECALL row.
Constraint 18 gives the step because the virtual flag is one and the last-row
flag is zero. See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:354-357
at 8bbb2357. -/
private theorem nonterminal_virtual_row_pc_plus_one
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (rowIs : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (nonterminal : row.virtual_sequence_remaining.getD 0 ≠ 0) :
    witness.NextPC cycle = witness.PC cycle + 1 := by
  have virtual : witness.OpFlags .VirtualInstruction cycle = 1 := by
    rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations .VirtualInstruction cycle slot selected]
    have some : row.virtual_sequence_remaining.isSome = true := by
      cases h : row.virtual_sequence_remaining with
      | none =>
        have zero : row.virtual_sequence_remaining.getD 0 = 0 := by rw [h]; rfl
        exact False.elim (nonterminal zero)
      | some n => rfl
    rw [JoltConstraints.bytecodeCircuitFlag, rowIs]
    change (if row.virtual_sequence_remaining.isSome = true then (1 : F) else 0) = 1
    rw [some]
    rfl
  have nonlast : witness.OpFlags .IsLastInSequence cycle = 0 := by
    rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations .IsLastInSequence cycle slot selected]
    have notLast : row.virtual_sequence_remaining ≠ some 0 := by
      intro h
      rw [h] at nonterminal
      exact nonterminal rfl
    rw [JoltConstraints.bytecodeCircuitFlag, rowIs]
    change (if row.virtual_sequence_remaining == some 0 then (1 : F) else 0) = 0
    split_ifs with equal
    · exact False.elim (notLast (beq_iff_eq.mp equal))
    · rfl
  have relation := equations.nextPCEqPCPlusOneIfInline cycle
  rw [virtual, nonlast] at relation
  linear_combination relation

/-- A taken branch at a valid bytecode address has a nonzero next unexpanded
PC. For example, a BEQ at `RAM_START_ADDRESS` has an offset within 4 KiB,
so constraint 16 cannot send it to address zero. -/
private theorem branch_row_next_pc_nonzero
    {F : Type} [Field F] (joltField : JoltField F)
    {params : WitnessParams} (witness : WitnessType F params)
    (row : JoltInstructionRow) (valid : row.Valid)
    (addressOk : bytecode_address_ok row.address = true)
    (branch : JoltMetadata.instructionFlag row.instruction .Branch = true)
    (branchEquation : JoltConstraints.nextUnexpandedPCEqPCPlusImmIfShouldBranch witness)
    (cycle : Fin params.traceLength)
    (currentPC : witness.UnexpandedPC cycle = (row.address.toNat : F))
    (immediate : witness.Imm cycle = (JoltMetadata.immediate row.instruction : F))
    (taken : witness.ShouldBranch cycle ≠ 0) :
    witness.NextUnexpandedPC cycle ≠ 0 := by
  intro zero
  have relation := branchEquation cycle
  have target : witness.NextUnexpandedPC cycle - witness.UnexpandedPC cycle -
      witness.Imm cycle = 0 := (mul_eq_zero.mp relation).resolve_left taken
  have targetZero : (row.address.toNat : F) +
      (JoltMetadata.immediate row.instruction : F) = 0 := by
    rw [zero, currentPC, immediate] at target
    linear_combination -target
  exact branch_target_ne_zero joltField row valid addressOk branch targetZero

/-- The final represented real row occupies a selected bytecode slot, and the
boundary after it has unexpanded PC zero. For example, the final ADDI before
padding has its own selected slot while the next no-op has address zero. -/
private theorem represented_last_boundary
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (nonempty : 0 < run.rows.size)
    (boundary : run.rows.size = params.traceLength ∨
      ∃ bound : run.rows.size < params.traceLength,
        witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 1)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?) :
    ∃ cycle : Fin params.traceLength, cycle.val + 1 = run.rows.size ∧
      ∃ slot : Fin (2 ^ params.logBytecodeK),
        slot.val = last.rowIndex.val + 1 ∧
        JoltConstraints.bytecodeRa witness slot cycle = 1 ∧
        witness.UnexpandedPC cycle = (run.bytecode[last.rowIndex].address.toNat : F) ∧
        witness.NextUnexpandedPC cycle = 0 := by
  have lastAt : run.rows[run.rows.size - 1]? = some last := by
    simpa only [Array.back?_eq_getElem?] using atEnd
  obtain ⟨lastIn, lastEq⟩ := Array.getElem?_eq_some_iff.mp lastAt
  let cycle : Fin params.traceLength :=
    ⟨run.rows.size - 1, by have := represented.rowsBound; omega⟩
  have cycleEnd : cycle.val + 1 = run.rows.size := by dsimp [cycle]; omega
  have cycleIn : cycle.val < run.rows.size := by omega
  have rowAt : run.rows[cycle.val] = last := by
    dsimp [cycle]
    exact lastEq
  have selected := selected_represented_row joltField joltInstance privateInputs
    witness context equations run bytecodeEq represented cycle cycleIn
  let slot : Fin (2 ^ params.logBytecodeK) :=
    ⟨last.rowIndex.val + 1, by
      have domain : params.BytecodeDomainFor run.bytecode.size := by
        simpa only [bytecodeEq] using context.bytecodeDomain
      have fits := domain.rowsFit
      have rowBound := last.rowIndex.isLt
      omega⟩
  have currentSelected : JoltConstraints.bytecodeRa witness slot cycle = 1 := by
    simpa only [rowAt] using selected
  have currentPC : witness.UnexpandedPC cycle =
      (run.bytecode[last.rowIndex].address.toNat : F) := by
    have read := JoltConstraints.Soundness.unexpandedPC_of_selected_bytecode
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations cycle slot currentSelected
    rw [read]
    simp [slot, ← bytecodeEq, JoltConstraints.bytecodeAddress,
      JoltConstraints.bytecodeRow]
  have nextPCZero : witness.NextUnexpandedPC cycle = 0 := by
    rcases boundary with lastCycle | ⟨cutBound, padding⟩
    · rw [equations.nextUnexpandedPCEqShift cycle]
      simp [show ¬ cycle.val + 1 < params.traceLength by omega]
    · rw [equations.nextUnexpandedPCEqShift cycle]
      have next : cycle.val + 1 < params.traceLength := by omega
      simp only [dif_pos next]
      have cutEq : (⟨cycle.val + 1, next⟩ : Fin params.traceLength) =
          ⟨run.rows.size, cutBound⟩ := Fin.ext (by omega)
      rw [cutEq]
      exact unexpanded_zero_of_padding joltField joltInstance privateInputs
        witness context equations _ padding
  exact ⟨cycle, cycleEnd, slot, rfl, currentSelected, currentPC, nextPCZero⟩

/-- A nonterminal virtual row cannot occupy the final witness cycle, because
constraint 18 advances its positive expanded slot while the final shift is
zero. For example, the first ECALL row cannot be the witness's last row. -/
private theorem nonterminal_at_last_cycle_impossible
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (last : TraceRow run.bytecode)
    (cycle : Fin params.traceLength) (lastCycle : cycle.val + 1 = params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (slotIndex : slot.val = last.rowIndex.val + 1)
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (inlineNext : witness.NextPC cycle = witness.PC cycle + 1) : False := by
  have pcZero : witness.NextPC cycle = 0 := by
    rw [equations.nextPCEqShift cycle]
    simp [show ¬ cycle.val + 1 < params.traceLength by omega]
  have expandedPC := JoltConstraints.Soundness.pc_of_selected_bytecode
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    context equations cycle slot selected
  have castZero : ((last.rowIndex.val + 2 : Nat) : F) = 0 := by
    have h : ((last.rowIndex.val + 1 : Nat) : F) + 1 = 0 := by
      calc
        ((last.rowIndex.val + 1 : Nat) : F) + 1 = witness.PC cycle + 1 := by
          rw [expandedPC, slotIndex]
        _ = witness.NextPC cycle := inlineNext.symm
        _ = 0 := pcZero
    have natEq : last.rowIndex.val + 2 = (last.rowIndex.val + 1) + 1 := by omega
    rw [natEq]
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have bound : last.rowIndex.val + 2 < ringChar F := by
    have fit := (show params.BytecodeDomainFor run.bytecode.size by
      simpa only [bytecodeEq] using context.bytecodeDomain).rowsFit
    have powBound : 2 ^ params.logBytecodeK ≤ 2 ^ 64 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) params.logBytecodeK_lt_usizeBits.le
    have charBound := JoltConstraints.Soundness.two_pow_64_lt_char
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    omega
  have zero : last.rowIndex.val + 2 = 0 :=
    JoltConstraints.Soundness.natCast_injective_below_char (b := 0) bound
      (by
        have charBound := JoltConstraints.Soundness.two_pow_64_lt_char
          (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
        omega) (by simpa using castZero)
  omega

/-- A nonterminal virtual row cannot precede padding: its next selected slot
is still an in-bounds row of the same source. For example, an interior MRET
row is followed by another MRET row instead of a no-op. -/
private theorem nonterminal_before_padding_impossible
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (last : TraceRow run.bytecode)
    (cycle : Fin params.traceLength) (cycleEnd : cycle.val + 1 = run.rows.size)
    (slot : Fin (2 ^ params.logBytecodeK))
    (slotIndex : slot.val = last.rowIndex.val + 1)
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (rowIs : JoltConstraints.bytecodeRow context.bytecode slot.val =
      some run.bytecode[last.rowIndex])
    (continues : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 ≠ 0)
    (cutBound : run.rows.size < params.traceLength)
    (padding : witness.InstructionFlags .IsNoop ⟨run.rows.size, cutBound⟩ = 1) : False := by
  have next : cycle.val + 1 < params.traceLength := by omega
  obtain ⟨nextSlot, nextSelected, nextIndex⟩ :=
    JoltConstraints.Soundness.selected_next_of_remaining
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations cycle next slot selected rowIs continues
  have layout := expand_program_layout joltInstance.program run.bytecode run.expands
  have endBound : last.rowIndex.val +
      (run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0).toNat <
      run.bytecode.size := by
    simpa only [Fin.getElem_fin] using layout.endInBounds last.rowIndex
  have positive : 0 < (run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0).toNat := by
    have nonzeroNat := BitVec.toNat_ne_iff_ne.mpr continues
    have zeroNat : (0 : BitVec 16).toNat = 0 := rfl
    rw [zeroNat] at nonzeroNat
    omega
  have nextRowBound : last.rowIndex.val + 1 < run.bytecode.size := by omega
  have nextSlotEq : nextSlot.val = last.rowIndex.val + 2 := by
    rw [slotIndex] at nextIndex
    simpa only [Fin.val_mk] using nextIndex
  have nextReal : witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ = 0 := by
    rw [JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations .IsNoop ⟨cycle.val + 1, next⟩ nextSlot nextSelected]
    rw [← bytecodeEq]
    simp [JoltConstraints.bytecodeInstructionFlag, JoltConstraints.bytecodeRow,
      nextSlotEq, nextRowBound, JoltMetadata.instructionFlag]
  have cutEq : (⟨cycle.val + 1, next⟩ : Fin params.traceLength) =
      ⟨run.rows.size, cutBound⟩ := Fin.ext (by omega)
  rw [cutEq] at nextReal
  exact zero_ne_one (nextReal.symm.trans padding)

/-- A retained row immediately before padding or the final witness cycle
cannot be inside a virtual expansion. For example, a nonterminal ECALL row
must select another real ECALL row on the next cycle. -/
private theorem last_row_terminal
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (boundary : run.rows.size = params.traceLength ∨
      ∃ bound : run.rows.size < params.traceLength,
        witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 1)
    (last : TraceRow run.bytecode)
    (cycle : Fin params.traceLength) (cycleEnd : cycle.val + 1 = run.rows.size)
    (slot : Fin (2 ^ params.logBytecodeK))
    (slotIndex : slot.val = last.rowIndex.val + 1)
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (rowIs : JoltConstraints.bytecodeRow context.bytecode slot.val =
      some run.bytecode[last.rowIndex]) :
    run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 := by
  by_contra continues
  have inlineNext := nonterminal_virtual_row_pc_plus_one joltField
    joltInstance privateInputs witness context equations cycle slot selected
    run.bytecode[last.rowIndex] rowIs continues
  rcases boundary with lastCycle | ⟨cutBound, padding⟩
  · exact nonterminal_at_last_cycle_impossible joltField joltInstance privateInputs
      witness context equations run bytecodeEq last cycle (by omega) slot
      slotIndex selected inlineNext
  · exact nonterminal_before_padding_impossible joltField joltInstance privateInputs
      witness context equations run bytecodeEq last cycle cycleEnd slot slotIndex
      selected rowIs continues cutBound padding

/-- A selected terminal non-jump row has the ordinary update flags: Jump and
DoNotUpdateUnexpandedPC are zero, while IsCompressed records that row's length.
For example, a terminal compressed ADDI uses a two-byte successor. -/
private theorem selected_terminal_nonjump_flags
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (rowIs : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (terminal : row.virtual_sequence_remaining.getD 0 = 0)
    (jumpFalse : JoltMetadata.opcodeFlag row.instruction .Jump = false) :
    witness.OpFlags .Jump cycle = 0 ∧
      witness.OpFlags .DoNotUpdateUnexpandedPC cycle = 0 ∧
      witness.OpFlags .IsCompressed cycle = (if row.is_compressed then (1 : F) else 0) := by
  have jumpZero : witness.OpFlags .Jump cycle = 0 := by
    rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations .Jump cycle slot selected]
    rw [JoltConstraints.bytecodeCircuitFlag, rowIs]
    change (if JoltMetadata.opcodeFlag row.instruction .Jump = true
      then (1 : F) else 0) = 0
    rw [jumpFalse]
    rfl
  have doNotZero : witness.OpFlags .DoNotUpdateUnexpandedPC cycle = 0 := by
    rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations .DoNotUpdateUnexpandedPC cycle slot selected]
    rw [JoltConstraints.bytecodeCircuitFlag, rowIs]
    change (if row.virtual_sequence_remaining.getD 0 != 0 then (1 : F) else 0) = 0
    simp
    exact terminal
  have compressed : witness.OpFlags .IsCompressed cycle =
      (if row.is_compressed then (1 : F) else 0) := by
    rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations .IsCompressed cycle slot selected]
    simp [JoltConstraints.bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag]
  exact ⟨jumpZero, doNotZero, compressed⟩

/-- A nonzero ShouldBranch value on a selected row implies the row has the
Branch flag. For example, a taken BEQ has this flag; an ADDI cannot be taken. -/
private theorem selected_branch_flag_of_taken
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (rowIs : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (taken : witness.ShouldBranch cycle ≠ 0) :
    JoltMetadata.instructionFlag row.instruction .Branch = true := by
  by_contra notBranch
  have branchFalse : JoltMetadata.instructionFlag row.instruction .Branch = false :=
    Bool.eq_false_iff.mpr notBranch
  have zero : witness.ShouldBranch cycle = 0 := by
    rw [equations.shouldBranchEqLookupOutputMulBranch cycle,
      JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
        (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
        context equations .Branch cycle slot selected]
    rw [JoltConstraints.bytecodeInstructionFlag, rowIs]
    change witness.LookupOutput cycle *
      (if JoltMetadata.instructionFlag row.instruction .Branch = true
        then (1 : F) else 0) = 0
    rw [branchFalse]
    simp
  exact taken zero

/-- A selected terminal row at a zero next-PC boundary must have the Jump
flag. An ordinary ADDI has a positive successor, while a BEQ target cannot
be zero; a JAL or JALR remains possible. -/
private theorem selected_boundary_jump_flag
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (row : JoltInstructionRow)
    (rowIs : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (valid : row.Valid) (addressOk : bytecode_address_ok row.address = true)
    (terminal : row.virtual_sequence_remaining.getD 0 = 0)
    (currentPC : witness.UnexpandedPC cycle = (row.address.toNat : F))
    (nextZero : witness.NextUnexpandedPC cycle = 0) :
    JoltMetadata.opcodeFlag row.instruction .Jump = true := by
  by_contra jump
  have jumpFalse : JoltMetadata.opcodeFlag row.instruction .Jump = false :=
    Bool.eq_false_iff.mpr jump
  obtain ⟨jumpZero, doNotZero, compressed⟩ :=
    selected_terminal_nonjump_flags joltField joltInstance privateInputs witness
      context equations cycle slot selected row rowIs terminal jumpFalse
  by_cases branchZero : witness.ShouldBranch cycle = 0
  · exact (ordinary_row_next_pc_nonzero joltField witness row.address
      row.is_compressed equations.nextUnexpandedPCUpdateOtherwise cycle
      currentPC jumpZero branchZero doNotZero compressed) nextZero
  · have branchFlag := selected_branch_flag_of_taken joltField joltInstance
      privateInputs witness context equations cycle slot selected row rowIs branchZero
    have immediate : witness.Imm cycle =
        (JoltMetadata.immediate row.instruction : F) := by
      rw [JoltConstraints.Soundness.imm_of_selected_bytecode
        (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
        context equations cycle slot selected]
      simp [JoltConstraints.bytecodeImmediate, rowIs]
    exact (branch_row_next_pc_nonzero joltField witness row valid addressOk branchFlag
      equations.nextUnexpandedPCEqPCPlusImmIfShouldBranch cycle currentPC
      immediate branchZero) nextZero

/-- If the retained run ends at padding or the last witness cycle, its final
real row ends a source instruction with JAL or JALR. For example, an ordinary
ADDI before padding would force the next unexpanded PC to its positive successor.
See jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:347-353
at 8bbb2357. -/
theorem soundness_last_row_is_jump
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (realRows : ∀ cycle : Fin params.traceLength,
      cycle.val < run.rows.size → witness.InstructionFlags .IsNoop cycle = 0)
    (nonempty : 0 < run.rows.size)
    (boundary : run.rows.size = params.traceLength ∨
      ∃ bound : run.rows.size < params.traceLength,
        witness.InstructionFlags .IsNoop ⟨run.rows.size, bound⟩ = 1) :
    ∀ last ∈ run.rows.back?,
      run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 ∧
      ((∃ dst imm, run.bytecode[last.rowIndex].instruction = .JAL dst imm) ∨
        ∃ dst base imm, run.bytecode[last.rowIndex].instruction = .JALR dst base imm) := by
  intro last atEnd
  obtain ⟨cycle, cycleEnd, slot, slotIndex, currentSelected, currentPC, nextPCZero⟩ :=
    represented_last_boundary joltField joltInstance privateInputs witness context equations
      run bytecodeEq represented nonempty boundary last atEnd
  have rowIs : JoltConstraints.bytecodeRow context.bytecode slot.val =
      some run.bytecode[last.rowIndex] := by
    rw [slotIndex]
    simp [← bytecodeEq, JoltConstraints.bytecodeRow]
  have lastCompletes := last_row_terminal joltField joltInstance privateInputs
    witness context equations run bytecodeEq boundary last cycle cycleEnd slot
    slotIndex currentSelected rowIs
  have accepted : pc_map_ok run.bytecode = true := by
    obtain ⟨slots, preprocessed, _⟩ := context.entryIsRust
    unfold preprocess at preprocessed
    split at preprocessed
    · simpa only [bytecodeEq] using (show pc_map_ok context.bytecode = true from ‹_›)
    · cases preprocessed
  have addressOk := pc_map_ok_addresses run.bytecode accepted
    last.rowIndex.val last.rowIndex.isLt
  have valid := (expand_program_rows_valid joltInstance.program run.bytecode
    run.expands).rowValid last.rowIndex
  have jump := selected_boundary_jump_flag joltField joltInstance privateInputs
    witness context equations cycle slot currentSelected run.bytecode[last.rowIndex]
    rowIs valid addressOk lastCompletes currentPC nextPCZero
  exact ⟨lastCompletes, jump_instruction_of_flag _ jump⟩

end JoltInstance
