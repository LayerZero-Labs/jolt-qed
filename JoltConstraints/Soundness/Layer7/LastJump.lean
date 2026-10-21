import JoltConstraints.Soundness.Layer7.StallSuffix

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions JoltISA

namespace JoltInstance

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
  have lastAt : run.rows[run.rows.size - 1]? = some last := by
    simpa only [Array.back?_eq_getElem?] using atEnd
  obtain ⟨lastIn, lastEq⟩ := Array.getElem?_eq_some_iff.mp lastAt
  let cycle : Fin params.traceLength :=
    ⟨run.rows.size - 1, by have := represented.rowsBound; omega⟩
  have cycleIn : cycle.val < run.rows.size := by dsimp [cycle]; omega
  have rowAt : run.rows[cycle.val] = last := by
    dsimp [cycle]
    exact lastEq
  have selected := selected_represented_row joltField joltInstance privateInputs
    witness context equations run bytecodeEq represented cycle cycleIn
  have currentPC : witness.UnexpandedPC cycle =
      ((run.bytecode[last.rowIndex].address.toNat : Nat) : F) := by
    have read := JoltConstraints.Soundness.unexpandedPC_of_selected_bytecode
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
      context equations cycle
      ⟨run.rows[cycle.val].rowIndex.val + 1, by
        have domain : params.BytecodeDomainFor run.bytecode.size := by
          simpa only [bytecodeEq] using context.bytecodeDomain
        have fits := domain.rowsFit
        have rowBound := run.rows[cycle.val].rowIndex.isLt
        omega⟩ selected
    rw [read]
    simp [← bytecodeEq, JoltConstraints.bytecodeAddress,
      JoltConstraints.bytecodeRow, rowAt]
  have nextPCZero : witness.NextUnexpandedPC cycle = 0 := by
    rcases boundary with lastCycle | ⟨cutBound, padding⟩
    · rw [equations.nextUnexpandedPCEqShift cycle]
      simp [show ¬ cycle.val + 1 < params.traceLength by
        dsimp [cycle]; omega]
    · rw [equations.nextUnexpandedPCEqShift cycle]
      have next : cycle.val + 1 < params.traceLength := by
        dsimp [cycle]; omega
      simp only [dif_pos next]
      have cutEq : (⟨cycle.val + 1, next⟩ : Fin params.traceLength) =
          ⟨run.rows.size, cutBound⟩ := Fin.ext (by dsimp [cycle]; omega)
      rw [cutEq]
      exact unexpanded_zero_of_padding joltField joltInstance privateInputs
        witness context equations _ padding
  have currentSelected : JoltConstraints.bytecodeRa witness
      ⟨last.rowIndex.val + 1, by
        have domain : params.BytecodeDomainFor run.bytecode.size := by
          simpa only [bytecodeEq] using context.bytecodeDomain
        have fits := domain.rowsFit
        have rowBound := last.rowIndex.isLt
        omega⟩ cycle = 1 := by
    simpa only [rowAt] using selected
  have rowIs : JoltConstraints.bytecodeRow context.bytecode (last.rowIndex.val + 1) =
      some run.bytecode[last.rowIndex] := by
    simp [← bytecodeEq, JoltConstraints.bytecodeRow]
  have lastCompletes : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 := by
    by_contra continues
    have virtual : witness.OpFlags .VirtualInstruction cycle = 1 := by
      rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
        (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
        context equations .VirtualInstruction cycle _ currentSelected]
      have some : run.bytecode[last.rowIndex].virtual_sequence_remaining.isSome = true := by
        cases h : run.bytecode[last.rowIndex].virtual_sequence_remaining with
        | none =>
          have zero : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 := by
            rw [h]
            rfl
          exact False.elim (continues zero)
        | some n => rfl
      rw [JoltConstraints.bytecodeCircuitFlag, rowIs]
      change (if run.bytecode[last.rowIndex].virtual_sequence_remaining.isSome = true
        then (1 : F) else 0) = 1
      rw [some]
      rfl
    have nonlast : witness.OpFlags .IsLastInSequence cycle = 0 := by
      rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
        (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
        context equations .IsLastInSequence cycle _ currentSelected]
      have notLast : run.bytecode[last.rowIndex].virtual_sequence_remaining ≠ some 0 := by
        intro h
        rw [h] at continues
        exact continues rfl
      rw [JoltConstraints.bytecodeCircuitFlag, rowIs]
      change (if run.bytecode[last.rowIndex].virtual_sequence_remaining == some 0
        then (1 : F) else 0) = 0
      split_ifs with equal
      · exact False.elim (notLast (beq_iff_eq.mp equal))
      · rfl
    have inlineNext : witness.NextPC cycle = witness.PC cycle + 1 := by
      have relation := equations.nextPCEqPCPlusOneIfInline cycle
      rw [virtual, nonlast] at relation
      linear_combination relation
    rcases boundary with lastCycle | ⟨cutBound, padding⟩
    · have pcZero : witness.NextPC cycle = 0 := by
        rw [equations.nextPCEqShift cycle]
        simp [show ¬ cycle.val + 1 < params.traceLength by
          dsimp [cycle]; omega]
      have expandedPC := JoltConstraints.Soundness.pc_of_selected_bytecode
        (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
        context equations cycle _ currentSelected
      have castZero : ((last.rowIndex.val + 2 : Nat) : F) = 0 := by
        have h : ((last.rowIndex.val + 1 : Nat) : F) + 1 = 0 := by
          calc
            ((last.rowIndex.val + 1 : Nat) : F) + 1 = witness.PC cycle + 1 := by
              rw [expandedPC]
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
    · have next : cycle.val + 1 < params.traceLength := by
        dsimp [cycle]; omega
      obtain ⟨nextSlot, nextSelected, nextIndex⟩ :=
        JoltConstraints.Soundness.selected_next_of_remaining
          (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
          context equations cycle next _ currentSelected rowIs continues
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
        simpa only [Fin.val_mk] using nextIndex
      have nextReal : witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ = 0 := by
        rw [JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
          (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
          context equations .IsNoop ⟨cycle.val + 1, next⟩ nextSlot nextSelected]
        rw [← bytecodeEq]
        simp [JoltConstraints.bytecodeInstructionFlag, JoltConstraints.bytecodeRow,
          nextSlotEq, nextRowBound, JoltMetadata.instructionFlag]
      have cutEq : (⟨cycle.val + 1, next⟩ : Fin params.traceLength) =
          ⟨run.rows.size, cutBound⟩ := Fin.ext (by dsimp [cycle]; omega)
      rw [cutEq] at nextReal
      exact zero_ne_one (nextReal.symm.trans padding)
  refine ⟨lastCompletes, ?_⟩
  by_cases jump : JoltMetadata.opcodeFlag
      run.bytecode[last.rowIndex].instruction .Jump = true
  · exact jump_instruction_of_flag _ jump
  · have jumpFalse : JoltMetadata.opcodeFlag
        run.bytecode[last.rowIndex].instruction .Jump = false :=
      Bool.eq_false_iff.mpr jump
    have jumpZero : witness.OpFlags .Jump cycle = 0 := by
      rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
        (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
        context equations .Jump cycle _ currentSelected]
      rw [JoltConstraints.bytecodeCircuitFlag, rowIs]
      change (if JoltMetadata.opcodeFlag run.bytecode[last.rowIndex].instruction .Jump = true
        then (1 : F) else 0) = 0
      rw [jumpFalse]
      rfl
    have ordinaryImpossible (branchZero : witness.ShouldBranch cycle = 0) : False := by
      have doNotZero : witness.OpFlags .DoNotUpdateUnexpandedPC cycle = 0 := by
        rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
          (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
          context equations .DoNotUpdateUnexpandedPC cycle _ currentSelected]
        rw [JoltConstraints.bytecodeCircuitFlag, rowIs]
        change (if run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 != 0
          then (1 : F) else 0) = 0
        have rest : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0 :=
          lastCompletes
        simp only [Fin.getElem_fin] at rest ⊢
        simp
        exact rest
      have compressed : witness.OpFlags .IsCompressed cycle =
          (if run.bytecode[last.rowIndex].is_compressed then (1 : F) else 0) := by
        rw [JoltConstraints.Soundness.opFlag_of_selected_bytecode
          (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
          context equations .IsCompressed cycle _ currentSelected]
        simp [JoltConstraints.bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag]
      have update := equations.nextUnexpandedPCUpdateOtherwise cycle
      rw [branchZero, jumpZero, nextPCZero, currentPC, doNotZero, compressed] at update
      have successorCast :
          ((run.bytecode[last.rowIndex].address.toNat +
            (if run.bytecode[last.rowIndex].is_compressed then 2 else 4) : Nat) : F) = 0 := by
        cases h : run.bytecode[last.rowIndex].is_compressed <;>
          simp only [Fin.getElem_fin] at h update ⊢
        all_goals
          simp [h] at update ⊢
          linear_combination -update
      have successorBound : run.bytecode[last.rowIndex].address.toNat +
          (if run.bytecode[last.rowIndex].is_compressed then 2 else 4) < ringChar F := by
        have wordBound := run.bytecode[last.rowIndex].address.isLt
        have charBound := JoltConstraints.Soundness.two_pow_127_lt_char joltField
        split_ifs <;> omega
      have successorZero := JoltConstraints.Soundness.natCast_injective_below_char
        (b := 0) successorBound
        (by have h := JoltConstraints.Soundness.two_pow_127_lt_char joltField; omega)
        (by simpa using successorCast)
      split_ifs at successorZero
    by_cases branchZero : witness.ShouldBranch cycle = 0
    · exact False.elim (ordinaryImpossible branchZero)
    · have branchFlag : JoltMetadata.instructionFlag
          run.bytecode[last.rowIndex].instruction .Branch = true := by
        by_contra notBranch
        have branchFalse : JoltMetadata.instructionFlag
            run.bytecode[last.rowIndex].instruction .Branch = false :=
          Bool.eq_false_iff.mpr notBranch
        have zero : witness.ShouldBranch cycle = 0 := by
          rw [equations.shouldBranchEqLookupOutputMulBranch cycle,
            JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
              (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
              context equations .Branch cycle _ currentSelected]
          rw [JoltConstraints.bytecodeInstructionFlag, rowIs]
          change witness.LookupOutput cycle *
            (if JoltMetadata.instructionFlag run.bytecode[last.rowIndex].instruction .Branch = true
              then (1 : F) else 0) = 0
          rw [branchFalse]
          simp
        exact branchZero zero
      have immediate : witness.Imm cycle =
          (JoltMetadata.immediate run.bytecode[last.rowIndex].instruction : F) := by
        rw [JoltConstraints.Soundness.imm_of_selected_bytecode
          (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
          context equations cycle _ currentSelected]
        simp [JoltConstraints.bytecodeImmediate, rowIs]
      have relation := equations.nextUnexpandedPCEqPCPlusImmIfShouldBranch cycle
      have target : witness.NextUnexpandedPC cycle - witness.UnexpandedPC cycle -
          witness.Imm cycle = 0 := (mul_eq_zero.mp relation).resolve_left branchZero
      have targetZero :
          (run.bytecode[last.rowIndex].address.toNat : F) +
            (JoltMetadata.immediate run.bytecode[last.rowIndex].instruction : F) = 0 := by
        rw [nextPCZero, currentPC, immediate] at target
        linear_combination -target
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
      exact False.elim (branch_target_ne_zero joltField _ valid addressOk branchFlag targetZero)

end JoltInstance
