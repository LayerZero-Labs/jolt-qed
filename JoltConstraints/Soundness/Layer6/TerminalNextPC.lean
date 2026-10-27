import JoltConstraints.Soundness.Layer7.StallSuffix
import JoltConstraints.Soundness.Layer7.LastJump

/-! The next source address at a terminal row with a real successor. -/

set_option autoImplicit false

namespace JoltInstance

open JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

/-- The final retained cycle selects the executed row and has its prepared PC
and link value. For example, a terminal ADDI row has its source address in PC. -/
private theorem terminal_last_setup
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (cycle : Fin params.traceLength) (atCycle : cycle.val + 1 = run.rows.size)
    (nextBound : run.rows.size < params.traceLength) :
    ∃ (index : Fin run.rows.size) (slot : Fin (2 ^ params.logBytecodeK)),
      index.val = cycle.val ∧ run.rows[index] = last ∧
      JoltConstraints.bytecodeRa witness slot cycle = 1 ∧
      JoltConstraints.bytecodeRow context.bytecode slot.val =
        some run.bytecode[last.rowIndex] ∧
      last.preState.sail.regs.get? Register.PC =
        some run.bytecode[last.rowIndex].address ∧
      last.preState.sail.regs.get? Register.nextPC =
        some (run.bytecode[last.rowIndex].address +
          if source_is_compressed run.bytecode last.rowIndex then 2 else 4) := by
  obtain ⟨before, slot, beforeIs, lastAt, selected, rowAtRun, _⟩ :=
    selected_last_represented_row joltField joltInstance privateInputs witness
      context equations run bytecodeEq represented last atEnd nextBound
  let index : Fin run.rows.size := ⟨before.val, by omega⟩
  have rowEq : run.rows[index] = last := by
    have atIndex : run.rows[index]? = some last := by simpa only [index] using lastAt
    exact (Array.getElem?_eq_some_iff.mp atIndex).2
  have beforeEq : before = cycle := Fin.ext (by omega)
  have selectedCycle : JoltConstraints.bytecodeRa witness slot cycle = 1 := by
    simpa only [beforeEq] using selected
  have rowAt : JoltConstraints.bytecodeRow context.bytecode slot.val =
      some run.bytecode[last.rowIndex] := by
    simpa only [← bytecodeEq] using rowAtRun
  refine ⟨index, slot, by dsimp [index]; omega, rowEq, selectedCycle, rowAt, ?_, ?_⟩
  · simpa only [rowEq] using untrusted_row_pc joltInstance privateInputs run index
  · simpa only [rowEq] using untrusted_row_next_pc joltInstance privateInputs run index

/-- A retained row without runtime advice or a tape load executes its bytecode
instruction directly. For example, a JAL row uses `execInstr` at its run index. -/
private theorem terminal_direct_execution
    (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (last : TraceRow run.bytecode) (index : Fin run.rows.size)
    (rowEq : run.rows[index] = last)
    (noAdvice : run.bytecode[last.rowIndex].instruction.adviceValue? = none)
    (noTape : ∀ answer, JoltConstraints.Soundness.execWithTapeAnswer
      run.bytecode[last.rowIndex].instruction answer =
        JoltISA.execInstr run.bytecode[last.rowIndex].instruction) :
    JoltISA.execInstr run.bytecode[last.rowIndex].instruction last.preState =
      .ok RETIRE_SUCCESS last.postState := by
  subst last
  have applied := JoltConstraints.Soundness.withRuntimeAdvice_eq_of_noAdvice
    run.bytecode[run.rows[index].rowIndex].instruction run.rows[index].runtimeAdvice noAdvice
  have executed := run.executes index
  rw [applied, noTape] at executed
  exact executed

/-- A selected terminal non-jump row with no taken branch advances the
witness by its source length. For example, an untaken BEQ at `a` advances to
`a + 4` when it is uncompressed. -/
private theorem terminal_fallthrough_witness
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
    (rowAt : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (terminal : row.virtual_sequence_remaining.getD 0 = 0)
    (jumpFalse : JoltMetadata.opcodeFlag row.instruction .Jump = false)
    (shouldBranchZero : witness.ShouldBranch cycle = 0) :
    witness.NextUnexpandedPC cycle =
      ((row.address.toNat + if row.is_compressed then 2 else 4 : Nat) : F) := by
  obtain ⟨jumpZero, doNotZero, compressed⟩ := selected_terminal_nonjump_flags
    joltField joltInstance privateInputs witness context equations cycle slot selected
      row rowAt terminal jumpFalse
  have currentPC : witness.UnexpandedPC cycle = (row.address.toNat : F) := by
    simpa [JoltConstraints.bytecodeAddress, rowAt] using
      JoltConstraints.Soundness.unexpandedPC_of_selected_bytecode
        (two_pow_127_lt_char joltField) context equations cycle slot selected
  exact ordinary_row_next_pc_value witness row.address row.is_compressed
    equations.nextUnexpandedPCUpdateOtherwise cycle currentPC jumpZero shouldBranchZero
    doNotZero compressed

/-- A terminal row outside control flow advances both Sail and the witness by
its source length. For example, ADDI at `0x80000000` advances to `0x80000004`. -/
private theorem terminal_noncontrol
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (noWrap : joltInstance.program.NextPCNoWrap)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (terminal : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0)
    (cycle : Fin params.traceLength) (atCycle : cycle.val + 1 = run.rows.size)
    (nextBound : run.rows.size < params.traceLength)
    (notJal : ¬ ∃ dst imm,
      run.bytecode[last.rowIndex].instruction = .JAL dst imm)
    (notJalr : ¬ ∃ dst base imm,
      run.bytecode[last.rowIndex].instruction = .JALR dst base imm)
    (notBranch : JoltMetadata.instructionFlag
      run.bytecode[last.rowIndex].instruction .Branch = false)
    (address : BitVec 64)
    (postNext : last.postState.sail.regs.get? Register.nextPC = some address) :
    witness.NextUnexpandedPC cycle = (address.toNat : F) := by
  obtain ⟨index, slot, _, rowEq, selected, rowAt, _, _⟩ :=
    terminal_last_setup joltField joltInstance privateInputs witness context equations
      run bytecodeEq represented last atEnd cycle atCycle nextBound
  have sail := noncontrol_next_pc joltInstance privateInputs run index
    (by simpa only [rowEq] using notJal)
    (by simpa only [rowEq] using notJalr)
    (by simpa only [rowEq] using notBranch)
  have addressEq : address = run.bytecode[last.rowIndex].address +
      (if source_is_compressed run.bytecode last.rowIndex then 2 else 4) := by
    exact Option.some.inj (postNext.symm.trans (by simpa only [rowEq] using sail))
  have jumpFalse : JoltMetadata.opcodeFlag
      run.bytecode[last.rowIndex].instruction .Jump = false := by
    change (match run.bytecode[last.rowIndex].instruction with
      | .JAL _ _ | .JALR _ _ _ => true | _ => false) = false
    split
    · rename_i dst imm jump
      exact False.elim (notJal ⟨dst, imm, jump⟩)
    · rename_i dst base imm jump
      exact False.elim (notJalr ⟨dst, base, imm, jump⟩)
    · rfl
  have branchFlag : witness.InstructionFlags .Branch cycle = 0 := by
    rw [JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
      (two_pow_127_lt_char joltField) context equations .Branch cycle slot selected]
    simp [JoltConstraints.bytecodeInstructionFlag, rowAt]
    exact notBranch
  have shouldBranch : witness.ShouldBranch cycle = 0 := by
    rw [equations.shouldBranchEqLookupOutputMulBranch cycle, branchFlag]
    ring
  have witnessNext := terminal_fallthrough_witness joltField joltInstance privateInputs
    witness context equations cycle slot selected run.bytecode[last.rowIndex] rowAt
    terminal jumpFalse shouldBranch
  have compressedEq := source_compressed_of_last run.bytecode last.rowIndex terminal
  have noWrapEq := terminal_link_no_wrap joltInstance.program run.bytecode run.expands
    noWrap last.rowIndex terminal
  rw [compressedEq] at addressEq
  rw [addressEq, noWrapEq]
  exact witnessNext

/-- A terminal JAL has the same wrapped target in Sail and the constrained
next source PC. For example, `JAL +0` keeps its source address. -/
private theorem terminal_jal
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (cycle : Fin params.traceLength) (atCycle : cycle.val + 1 = run.rows.size)
    (nextBound : run.rows.size < params.traceLength)
    (nextReal : witness.InstructionFlags .IsNoop ⟨run.rows.size, nextBound⟩ ≠ 1)
    (dst : JoltISA.Dst) (imm : BitVec 64)
    (jump : run.bytecode[last.rowIndex].instruction = .JAL dst imm)
    (address : BitVec 64)
    (postNext : last.postState.sail.regs.get? Register.nextPC = some address) :
    witness.NextUnexpandedPC cycle = (address.toNat : F) := by
  obtain ⟨index, slot, _, rowEq, selected, rowAt, pc, prepared⟩ :=
    terminal_last_setup joltField joltInstance privateInputs witness context equations
      run bytecodeEq represented last atEnd cycle atCycle nextBound
  have direct := terminal_direct_execution joltInstance privateInputs run last index rowEq
    (by rw [jump]; rfl) (by intro answer; rw [jump]; rfl)
  rw [jump] at direct
  have sail := stall_jal_exec_target dst imm run.bytecode[last.rowIndex].address
    (run.bytecode[last.rowIndex].address +
      if source_is_compressed run.bytecode last.rowIndex then 2 else 4)
    last.preState last.postState pc prepared direct
  have addressEq : address = run.bytecode[last.rowIndex].address + imm :=
    Option.some.inj (postNext.symm.trans sail)
  have next : cycle.val + 1 < params.traceLength := by omega
  have nextEq : (⟨cycle.val + 1, next⟩ : Fin params.traceLength) =
      ⟨run.rows.size, nextBound⟩ := Fin.ext atCycle
  have real : witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ ≠ 1 := by
    simpa only [nextEq] using nextReal
  have target := stall_jal_next_target joltField joltInstance privateInputs
    witness context equations cycle next slot selected run.bytecode[last.rowIndex]
    rowAt dst imm jump real
  rw [addressEq]
  exact target

/-- A terminal JALR uses the represented architectural base for the same
masked target as Sail. For example, `jalr x0, 0(x1)` selects `(x1 & ~1)`. -/
private theorem terminal_jalr
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (cycle : Fin params.traceLength) (atCycle : cycle.val + 1 = run.rows.size)
    (nextBound : run.rows.size < params.traceLength)
    (nextReal : witness.InstructionFlags .IsNoop ⟨run.rows.size, nextBound⟩ ≠ 1)
    (dst : JoltISA.Dst) (base : JoltISA.Src) (imm : BitVec 64)
    (jump : run.bytecode[last.rowIndex].instruction = .JALR dst base imm)
    (address : BitVec 64)
    (postNext : last.postState.sail.regs.get? Register.nextPC = some address) :
    witness.NextUnexpandedPC cycle = (address.toNat : F) := by
  obtain ⟨index, slot, cycleIndex, rowEq, selected, rowAt, _, prepared⟩ :=
    terminal_last_setup joltField joltInstance privateInputs witness context equations
      run bytecodeEq represented last atEnd cycle atCycle nextBound
  have direct := terminal_direct_execution joltInstance privateInputs run last index rowEq
    (by rw [jump]; rfl) (by intro answer; rw [jump]; rfl)
  rw [jump] at direct
  have tapeExec : JoltConstraints.Soundness.execWithTapeAnswer (.JALR dst base imm)
      (run.answers index) last.preState = .ok RETIRE_SUCCESS last.postState := by
    exact direct
  have sail := tape_jalr_target dst base imm
    (run.bytecode[last.rowIndex].address +
      if source_is_compressed run.bytecode last.rowIndex then 2 else 4)
    (run.answers index) last.preState last.postState prepared tapeExec
  have addressEq : address = jolt_jalr_target64
      (JoltISA.sourceValue base last.preState) imm :=
    Option.some.inj (postNext.symm.trans sail)
  have inRun : cycle.val < run.rows.size := by omega
  have rowAtRun : JoltConstraints.bytecodeRow run.bytecode slot.val =
      some run.bytecode[last.rowIndex] := by
    simpa only [bytecodeEq] using rowAt
  have atCycleRow : run.rows[cycle.val] = last := by
    simpa only [← cycleIndex] using rowEq
  have baseAt := represented_last_jalr_base joltField joltInstance privateInputs
    witness context equations run bytecodeEq represented last dst base imm jump
    cycle inRun atCycleRow slot selected rowAtRun
  have next : cycle.val + 1 < params.traceLength := by omega
  have nextEq : (⟨cycle.val + 1, next⟩ : Fin params.traceLength) =
      ⟨run.rows.size, nextBound⟩ := Fin.ext atCycle
  have real : witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ ≠ 1 := by
    simpa only [nextEq] using nextReal
  have target := selected_jalr_next_target joltField joltInstance privateInputs
    witness context equations cycle next slot selected run.bytecode[last.rowIndex]
    rowAt dst base imm (JoltISA.sourceValue base last.preState) jump baseAt real
  rw [addressEq]
  exact target

/-- A real successor is an accepted bytecode address and is the branch
cycle's constrained next source PC. For example, a BEQ targeting `0x80000008`
has a real successor at or above `RAM_START_ADDRESS` with an even address. -/
theorem terminal_real_successor_address
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (nextReal : witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ ≠ 1) :
    ∃ row : JoltInstructionRow,
      witness.NextUnexpandedPC cycle = (row.address.toNat : F) ∧
      JoltISA.RAM_START_ADDRESS ≤ row.address.toNat ∧ row.address.toNat % 2 = 0 := by
  rcases next_cycle_address joltField joltInstance privateInputs witness context
    equations cycle next with padding | ⟨slot, row, _, rowAt, nextAddress⟩
  · exact False.elim (nextReal padding)
  obtain ⟨index, _, rowEq⟩ := real_slot_index context.bytecode slot.val row rowAt
  have accepted : pc_map_ok context.bytecode = true := by
    obtain ⟨slots, preprocessed, _⟩ := context.entryIsRust
    unfold preprocess at preprocessed
    split at preprocessed
    · assumption
    · cases preprocessed
  have addressOk := pc_map_ok_addresses context.bytecode accepted index.val index.isLt
  simp only [bytecode_address_ok, Bool.and_eq_true, decide_eq_true_eq] at addressOk
  exact ⟨row, nextAddress, by rw [rowEq]; exact ⟨addressOk.1, beq_iff_eq.mp addressOk.2⟩⟩

/-- A valid branch whose source and wrapped target are accepted addresses
has the same target as the field sum of its source and signed offset.
For example, a BEQ with offset `-4` at `0x80000008` targets `0x80000004`. -/
private theorem terminal_branch_target_cast
    {F : Type} [Field F] (row : JoltInstructionRow) (valid : row.Valid)
    (lhs rhs : JoltISA.Src) (imm : BitVec 128)
    (shapes : row.instruction = .BEQ lhs rhs imm ∨
      row.instruction = .BNE lhs rhs imm ∨
      row.instruction = .BLT lhs rhs imm ∨
      row.instruction = .BGE lhs rhs imm ∨
      row.instruction = .BLTU lhs rhs imm ∨
      row.instruction = .BGEU lhs rhs imm)
    (fromRam : JoltISA.RAM_START_ADDRESS ≤ row.address.toNat)
    (toRam : JoltISA.RAM_START_ADDRESS ≤
      (row.address + imm.setWidth 64).toNat) :
    ((row.address + imm.setWidth 64).toNat : F) =
      (row.address.toNat : F) + (JoltMetadata.immediate row.instruction : F) := by
  obtain ⟨_, offset, offsetEq⟩ := valid.branch shapes
  have immediate : JoltMetadata.immediate row.instruction = imm.toInt := by
    rcases shapes with h | h | h | h | h | h
    all_goals rw [h]; rfl
  have target := JoltConstraints.branch_target_toNat row.address offset fromRam
    (by simpa only [← offsetEq] using toRam)
  have castEq := congrArg (fun value : Int => (value : F)) target
  push_cast at castEq
  simpa only [← offsetEq, immediate] using castEq

/-- A real successor satisfying the taken-branch field sum is the 64-bit
branch target. For example, offset `-4` from `0x80000008` selects `0x80000004`. -/
theorem terminal_branch_real_target
    {F : Type} [Field F] (joltField : JoltField F)
    (source successor : BitVec 64) (offset : BitVec 13)
    (sourceRam : JoltISA.RAM_START_ADDRESS ≤ source.toNat)
    (fieldTarget : (successor.toNat : F) =
      (source.toNat : F) + (offset.toInt : F)) :
    successor = source + (offset.signExtend 128).setWidth 64 := by
  have lower := BitVec.le_toInt offset
  have upper := BitVec.toInt_lt (x := offset)
  have sourceBound := source.isLt
  have successorBound := successor.isLt
  have charBound := JoltConstraints.Soundness.two_pow_127_lt_char joltField
  let sum : Int := (source.toNat : Int) + offset.toInt
  have sumNonneg : 0 ≤ sum := by
    have ramStart : JoltISA.RAM_START_ADDRESS = 2147483648 := rfl
    rw [ramStart] at sourceRam
    dsimp [sum]
    norm_num at lower upper
    omega
  have sumChar : sum.toNat < ringChar F := by
    dsimp [sum]
    norm_num at upper
    omega
  have castSum : (sum.toNat : F) =
      (source.toNat : F) + (offset.toInt : F) := by
    have sumEq : (sum.toNat : Int) = sum := Int.toNat_of_nonneg sumNonneg
    calc
      (sum.toNat : F) = ((sum.toNat : Int) : F) := (Int.cast_natCast _).symm
      _ = (sum : F) := by rw [sumEq]
      _ = (source.toNat : F) + (offset.toInt : F) := by dsimp [sum]; push_cast; ring
  have sameNat : sum.toNat = successor.toNat :=
    JoltConstraints.Soundness.natCast_injective_below_char sumChar
      (lt_trans successorBound (by omega : 2 ^ 64 < ringChar F))
      (castSum.trans fieldTarget.symm)
  have sumWord : sum < 2 ^ 64 := by omega
  have successorInt : successor = BitVec.ofInt 64 sum := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt]
    rw [Int.emod_eq_of_lt sumNonneg (by norm_num; omega)]
    simpa only [Int.toNat_natCast] using sameNat.symm
  have offsetWord : BitVec.ofInt 64 offset.toInt =
      (offset.signExtend 128).setWidth 64 := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_ofInt_eq_self (by decide)]
    · rw [← BitVec.signExtend_eq_setWidth_of_le (offset.signExtend 128)
        (by decide : 64 ≤ 128)]
      rw [BitVec.toInt_signExtend_eq_toInt_bmod_of_le _ (by decide : 64 ≤ 128)]
      rw [BitVec.toInt_signExtend_of_le (by decide : 13 ≤ 128)]
      exact (Int.bmod_eq_of_le (by norm_num at lower; omega)
        (by norm_num at upper; omega)).symm
    · norm_num at lower; omega
    · norm_num at upper; omega
  rw [successorInt, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, offsetWord]
  simp

/-- The selected branch's witness control equals the decision made from its
represented operands. For example, BEQ of equal words sets `ShouldBranch` to one. -/
theorem terminal_branch_decision
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
    (rowAt : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (branch : JoltMetadata.instructionFlag row.instruction .Branch = true)
    (lhs rhs : BitVec 64)
    (rs1 : witness.Rs1Value cycle = (lhs.toNat : F))
    (rs2 : witness.Rs2Value cycle = (rhs.toNat : F)) :
    witness.ShouldBranch cycle =
      if JoltISA.branchDecisionPure row.instruction lhs rhs then 1 else 0 := by
  have lookup := stall_branch_lookup_decision joltField joltInstance privateInputs
    witness context equations cycle slot selected row rowAt branch lhs rhs rs1 rs2
  have flag : witness.InstructionFlags .Branch cycle = 1 := by
    simpa [JoltConstraints.bytecodeInstructionFlag, rowAt, branch] using
      JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
        (two_pow_127_lt_char joltField) context equations .Branch cycle slot selected
  rw [equations.shouldBranchEqLookupOutputMulBranch cycle, lookup, flag]
  ring

/-- A selected taken branch makes the next unexpanded PC its address plus
its signed immediate in the field. For example, BEQ at `a` with `+8` yields `a + 8`. -/
theorem terminal_taken_branch_field
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
    (rowAt : JoltConstraints.bytecodeRow context.bytecode slot.val = some row)
    (taken : witness.ShouldBranch cycle = 1) :
    witness.NextUnexpandedPC cycle =
      (row.address.toNat : F) + (JoltMetadata.immediate row.instruction : F) := by
  have currentPC : witness.UnexpandedPC cycle = (row.address.toNat : F) := by
    simpa [JoltConstraints.bytecodeAddress, rowAt] using
      JoltConstraints.Soundness.unexpandedPC_of_selected_bytecode
        (two_pow_127_lt_char joltField) context equations cycle slot selected
  have immediate : witness.Imm cycle =
      (JoltMetadata.immediate row.instruction : F) := by
    simpa [JoltConstraints.bytecodeImmediate, rowAt] using
      JoltConstraints.Soundness.imm_of_selected_bytecode
        (two_pow_127_lt_char joltField) context equations cycle slot selected
  have relation := equations.nextUnexpandedPCEqPCPlusImmIfShouldBranch cycle
  rw [taken, one_mul, currentPC, immediate] at relation
  linear_combination relation

/-- A taken branch with a real successor has an accepted wrapped target.
For example, BEQ with offset `-4` can select `0x80000004`. -/
private theorem terminal_taken_branch_target_ram
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (cycle : Fin params.traceLength) (next : cycle.val + 1 < params.traceLength)
    (real : witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ ≠ 1)
    (source : BitVec 64) (offset : BitVec 13) (imm : BitVec 128)
    (offsetEq : imm = offset.signExtend 128)
    (sourceRam : JoltISA.RAM_START_ADDRESS ≤ source.toNat)
    (fieldTarget : witness.NextUnexpandedPC cycle =
      (source.toNat : F) + (offset.toInt : F)) :
    JoltISA.RAM_START_ADDRESS ≤ (source + imm.setWidth 64).toNat := by
  obtain ⟨successor, successorEq, successorRam⟩ :=
    terminal_real_successor_address joltField joltInstance privateInputs witness
      context equations cycle next real
  have successorWord := terminal_branch_real_target joltField source successor.address
    offset sourceRam (by rw [← successorEq, fieldTarget])
  rw [offsetEq, ← successorWord]
  exact successorRam.1

/-- An untaken terminal branch advances by its source length in Sail and
the witness. For example, an untaken BEQ at `0x80000000` reaches `0x80000004`. -/
private theorem terminal_branch_untaken
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (noWrap : joltInstance.program.NextPCNoWrap)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (last : TraceRow run.bytecode)
    (terminal : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0)
    (cycle : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (rowAt : JoltConstraints.bytecodeRow context.bytecode slot.val =
      some run.bytecode[last.rowIndex])
    (jumpFalse : JoltMetadata.opcodeFlag
      run.bytecode[last.rowIndex].instruction .Jump = false)
    (branchZero : witness.ShouldBranch cycle = 0)
    (prepared : last.preState.sail.regs.get? Register.nextPC =
      some (run.bytecode[last.rowIndex].address +
        if source_is_compressed run.bytecode last.rowIndex then 2 else 4))
    (same : last.postState = last.preState)
    (address : BitVec 64)
    (postNext : last.postState.sail.regs.get? Register.nextPC = some address) :
    witness.NextUnexpandedPC cycle = (address.toNat : F) := by
  have addressEq : address = run.bytecode[last.rowIndex].address +
      (if source_is_compressed run.bytecode last.rowIndex then 2 else 4) :=
    Option.some.inj (postNext.symm.trans (by rw [same]; exact prepared))
  have witnessNext := terminal_fallthrough_witness joltField joltInstance
    privateInputs witness context equations cycle slot selected
    run.bytecode[last.rowIndex] rowAt terminal jumpFalse branchZero
  have compressedEq := source_compressed_of_last run.bytecode last.rowIndex terminal
  have noWrapEq := terminal_link_no_wrap joltInstance.program run.bytecode run.expands
    noWrap last.rowIndex terminal
  rw [compressedEq] at addressEq
  rw [addressEq, noWrapEq]
  exact witnessNext

/-- A taken terminal branch has Sail's wrapped target as its constrained
next source address. For example, BEQ at `0x80000008` with `-4` advances to
`0x80000004`. -/
private theorem terminal_branch_taken
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (last : TraceRow run.bytecode)
    (cycle : Fin params.traceLength) (atCycle : cycle.val + 1 = run.rows.size)
    (nextBound : run.rows.size < params.traceLength)
    (nextReal : witness.InstructionFlags .IsNoop ⟨run.rows.size, nextBound⟩ ≠ 1)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (rowAt : JoltConstraints.bytecodeRow context.bytecode slot.val =
      some run.bytecode[last.rowIndex])
    (lhs rhs : JoltISA.Src) (imm : BitVec 128)
    (shapes : run.bytecode[last.rowIndex].instruction = .BEQ lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BNE lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BLT lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BGE lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BLTU lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BGEU lhs rhs imm)
    (valid : run.bytecode[last.rowIndex].Valid)
    (sourceRam : JoltISA.RAM_START_ADDRESS ≤
      run.bytecode[last.rowIndex].address.toNat)
    (taken : JoltNextPCFrame.BranchTaken
      run.bytecode[last.rowIndex].instruction last.preState = true)
    (branchOne : witness.ShouldBranch cycle = 1)
    (pc : last.preState.sail.regs.get? Register.PC =
      some run.bytecode[last.rowIndex].address)
    (runs : JoltISA.execInstr run.bytecode[last.rowIndex].instruction last.preState =
      .ok RETIRE_SUCCESS last.postState)
    (address : BitVec 64)
    (postNext : last.postState.sail.regs.get? Register.nextPC = some address) :
    witness.NextUnexpandedPC cycle = (address.toNat : F) := by
  have nextField := terminal_taken_branch_field joltField joltInstance privateInputs
    witness context equations cycle slot selected run.bytecode[last.rowIndex] rowAt branchOne
  obtain ⟨_, offset, offsetEq⟩ := valid.branch shapes
  have offsetImmediate : JoltMetadata.immediate
      run.bytecode[last.rowIndex].instruction = offset.toInt := by
    have ext := BitVec.toInt_signExtend_of_le (x := offset) (v := 128)
      (by decide : 13 ≤ 128)
    rcases shapes with h | h | h | h | h | h
    all_goals
      rw [h]
      change imm.toInt = offset.toInt
      rw [offsetEq]
      exact ext
  have next : cycle.val + 1 < params.traceLength := by omega
  have nextCycle : (⟨cycle.val + 1, next⟩ : Fin params.traceLength) =
      ⟨run.rows.size, nextBound⟩ := Fin.ext atCycle
  have real : witness.InstructionFlags .IsNoop ⟨cycle.val + 1, next⟩ ≠ 1 := by
    simpa only [nextCycle] using nextReal
  have targetRam : JoltISA.RAM_START_ADDRESS ≤
      (run.bytecode[last.rowIndex].address + imm.setWidth 64).toNat :=
    terminal_taken_branch_target_ram joltField joltInstance privateInputs witness
      context equations cycle next real run.bytecode[last.rowIndex].address
      offset imm offsetEq sourceRam (by rw [nextField, offsetImmediate])
  have targetCast := terminal_branch_target_cast (F := F) run.bytecode[last.rowIndex]
    valid lhs rhs imm shapes sourceRam targetRam
  have sail := JoltConstraints.execInstr_branch_target _ lhs rhs imm shapes
    last.preState last.postState run.bytecode[last.rowIndex].address taken pc runs
  have addressEq : address = run.bytecode[last.rowIndex].address + imm.setWidth 64 :=
    Option.some.inj (postNext.symm.trans sail)
  rw [addressEq, targetCast]
  exact nextField

/-- A represented terminal branch decides from its recorded pre-state
operands. For example, BEQ of equal pre-state words sets `ShouldBranch` to one. -/
private theorem terminal_branch_prepared_decision
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode)
    (cycle : Fin params.traceLength) (inRun : cycle.val < run.rows.size)
    (atCycleRow : run.rows[cycle.val] = last)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : JoltConstraints.bytecodeRa witness slot cycle = 1)
    (rowAt : JoltConstraints.bytecodeRow context.bytecode slot.val =
      some run.bytecode[last.rowIndex])
    (branch : JoltMetadata.instructionFlag
      run.bytecode[last.rowIndex].instruction .Branch = true)
    (lhs rhs : JoltISA.Src) (imm : BitVec 128)
    (shapes : run.bytecode[last.rowIndex].instruction = .BEQ lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BNE lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BLT lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BGE lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BLTU lhs rhs imm ∨
      run.bytecode[last.rowIndex].instruction = .BGEU lhs rhs imm) :
    witness.ShouldBranch cycle =
      if JoltNextPCFrame.BranchTaken run.bytecode[last.rowIndex].instruction
        last.preState then 1 else 0 := by
  have rowAtRun : JoltConstraints.bytecodeRow run.bytecode slot.val =
      some run.bytecode[last.rowIndex] := by simpa only [bytecodeEq] using rowAt
  have values := represented_last_branch_registers joltField joltInstance privateInputs
    witness context equations run bytecodeEq represented last cycle inRun atCycleRow
    slot selected rowAtRun branch lhs rhs imm shapes
  have decision := terminal_branch_decision joltField joltInstance privateInputs
    witness context equations cycle slot selected run.bytecode[last.rowIndex] rowAt
    branch (JoltISA.sourceValue lhs last.preState)
    (JoltISA.sourceValue rhs last.preState) values.2.1 values.2.2
  have modelEq : JoltISA.branchDecisionPure run.bytecode[last.rowIndex].instruction
      (JoltISA.sourceValue lhs last.preState) (JoltISA.sourceValue rhs last.preState) =
      JoltNextPCFrame.BranchTaken run.bytecode[last.rowIndex].instruction
        last.preState := by
    rcases shapes with h | h | h | h | h | h
    all_goals simp only [h, JoltNextPCFrame.BranchTaken]
  rw [modelEq] at decision
  exact decision

/-- A terminal branch's constrained next source address agrees with Sail's
post-state next PC, including a taken branch's signed target.
For example, a taken BEQ with offset `+8` advances to its source address plus eight. -/
private theorem terminal_branch
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (noWrap : joltInstance.program.NextPCNoWrap)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (terminal : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0)
    (cycle : Fin params.traceLength) (atCycle : cycle.val + 1 = run.rows.size)
    (nextBound : run.rows.size < params.traceLength)
    (nextReal : witness.InstructionFlags .IsNoop ⟨run.rows.size, nextBound⟩ ≠ 1)
    (branch : JoltMetadata.instructionFlag
      run.bytecode[last.rowIndex].instruction .Branch = true)
    (address : BitVec 64)
    (postNext : last.postState.sail.regs.get? Register.nextPC = some address) :
    witness.NextUnexpandedPC cycle = (address.toNat : F) := by
  obtain ⟨index, slot, cycleIndex, rowEq, selected, rowAt, pc, prepared⟩ :=
    terminal_last_setup joltField joltInstance privateInputs witness context equations
      run bytecodeEq represented last atEnd cycle atCycle nextBound
  have inRun : cycle.val < run.rows.size := by omega
  have atCycleRow : run.rows[cycle.val] = last := by
    simpa only [← cycleIndex] using rowEq
  obtain ⟨lhs, rhs, imm, shapes⟩ :=
    branch_instruction_of_flag run.bytecode[last.rowIndex].instruction branch
  have decision := terminal_branch_prepared_decision joltField joltInstance
    privateInputs witness context equations run bytecodeEq represented last cycle
    inRun atCycleRow slot selected rowAt branch lhs rhs imm shapes
  have runs := stall_branch_runs joltInstance privateInputs run last atEnd branch
  have jumpFalse : JoltMetadata.opcodeFlag
      run.bytecode[last.rowIndex].instruction .Jump = false := by
    rcases shapes with h | h | h | h | h | h
    all_goals rw [h]; rfl
  cases taken : JoltNextPCFrame.BranchTaken
      run.bytecode[last.rowIndex].instruction last.preState with
  | false =>
      have branchZero : witness.ShouldBranch cycle = 0 := by
        rw [taken] at decision
        simpa only [↓reduceIte] using decision
      have same := JoltNextPCFrame.branch_not_taken _ _ _ branch taken runs
      exact terminal_branch_untaken joltField joltInstance noWrap privateInputs
        witness context equations run last terminal cycle slot selected rowAt
        jumpFalse branchZero prepared same address postNext
  | true =>
      have branchOne : witness.ShouldBranch cycle = 1 := by
        rw [taken] at decision
        simpa only [↓reduceIte] using decision
      have valid := (expand_program_rows_valid joltInstance.program run.bytecode
        run.expands).rowValid last.rowIndex
      have rowAtRun : JoltConstraints.bytecodeRow run.bytecode slot.val =
          some run.bytecode[last.rowIndex] := by simpa only [bytecodeEq] using rowAt
      have accepted := (stall_cycle_selected_row joltInstance privateInputs context
        run.bytecode bytecodeEq slot run.bytecode[last.rowIndex] rowAtRun).1
      have sourceOk := pc_map_ok_addresses run.bytecode accepted last.rowIndex.val
        last.rowIndex.isLt
      simp only [bytecode_address_ok, Bool.and_eq_true, decide_eq_true_eq] at sourceOk
      exact terminal_branch_taken joltField joltInstance privateInputs witness context
        equations run last cycle atCycle nextBound nextReal slot selected rowAt lhs rhs imm
        shapes valid sourceOk.1 taken branchOne pc runs address postNext

/-- At the final row of a source expansion, a real successor makes the witness's
next unexpanded PC equal Sail's post-state next PC.
`atCycle` identifies the run's final row, and `nextReal` excludes padding.
For example, an ADDI at `0x80000000` followed by a real instruction selects
Sail's `0x80000004` as the next source address.
See jolt/crates/jolt-witness/src/witnesses/pc.rs (`NextUnexpandedPc::extract`)
and jolt/crates/jolt-witness/src/witnesses/flags.rs (`ShouldJump::extract`)
at 5def437f. -/
theorem terminal_next_unexpanded_pc
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (noWrap : joltInstance.program.NextPCNoWrap)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run.toTrace)
    (last : TraceRow run.bytecode) (atEnd : last ∈ run.rows.back?)
    (terminal : run.bytecode[last.rowIndex].virtual_sequence_remaining.getD 0 = 0)
    (cycle : Fin params.traceLength) (atCycle : cycle.val + 1 = run.rows.size)
    (nextBound : run.rows.size < params.traceLength)
    (nextReal : witness.InstructionFlags .IsNoop ⟨run.rows.size, nextBound⟩ ≠ 1)
    (address : BitVec 64)
    (postNext : last.postState.sail.regs.get? Register.nextPC = some address) :
    witness.NextUnexpandedPC cycle = (address.toNat : F) := by
  classical
  rcases Classical.em (∃ dst imm,
      run.bytecode[last.rowIndex].instruction = .JAL dst imm) with jal | jal
  · obtain ⟨dst, imm, jump⟩ := jal
    exact terminal_jal joltField joltInstance privateInputs witness context equations
      run bytecodeEq represented last atEnd cycle atCycle nextBound nextReal
      dst imm jump address postNext
  rcases Classical.em (∃ dst base imm,
      run.bytecode[last.rowIndex].instruction = .JALR dst base imm) with jalr | jalr
  · obtain ⟨dst, base, imm, jump⟩ := jalr
    exact terminal_jalr joltField joltInstance privateInputs witness context equations
      run bytecodeEq represented last atEnd cycle atCycle nextBound nextReal
      dst base imm jump address postNext
  rcases Classical.em (JoltMetadata.instructionFlag
      run.bytecode[last.rowIndex].instruction .Branch = true) with branch | branch
  · exact terminal_branch joltField joltInstance noWrap privateInputs witness context
      equations run bytecodeEq represented last atEnd terminal cycle atCycle nextBound
      nextReal branch address postNext
  have noBranch : JoltMetadata.instructionFlag
      run.bytecode[last.rowIndex].instruction .Branch = false :=
    Bool.eq_false_iff.mpr branch
  exact terminal_noncontrol joltField joltInstance noWrap privateInputs witness context
    equations run bytecodeEq represented last atEnd terminal cycle atCycle nextBound
    jal jalr noBranch address postNext

end JoltInstance
