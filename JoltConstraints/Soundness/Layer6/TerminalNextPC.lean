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
  obtain ⟨jumpZero, doNotZero, compressed⟩ := selected_terminal_nonjump_flags
    joltField joltInstance privateInputs witness context equations cycle slot selected
      run.bytecode[last.rowIndex] rowAt terminal jumpFalse
  have branchFlag : witness.InstructionFlags .Branch cycle = 0 := by
    rw [JoltConstraints.Soundness.instructionFlag_of_selected_bytecode
      (two_pow_127_lt_char joltField) context equations .Branch cycle slot selected]
    simp [JoltConstraints.bytecodeInstructionFlag, rowAt]
    exact notBranch
  have shouldBranch : witness.ShouldBranch cycle = 0 := by
    rw [equations.shouldBranchEqLookupOutputMulBranch cycle, branchFlag]
    ring
  have currentPC : witness.UnexpandedPC cycle =
      (run.bytecode[last.rowIndex].address.toNat : F) := by
    simpa [JoltConstraints.bytecodeAddress, rowAt] using
      JoltConstraints.Soundness.unexpandedPC_of_selected_bytecode
        (two_pow_127_lt_char joltField) context equations cycle slot selected
  have witnessNext := ordinary_row_next_pc_value witness
    run.bytecode[last.rowIndex].address run.bytecode[last.rowIndex].is_compressed
    equations.nextUnexpandedPCUpdateOtherwise cycle currentPC jumpZero shouldBranch
    doNotZero compressed
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
  sorry

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
