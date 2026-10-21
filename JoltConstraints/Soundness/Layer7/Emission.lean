import JoltConstraints.Soundness.Layer6.ExecutionPrefix
import JoltConstraints.trace_interface

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions JoltISA

namespace JoltInstance

/-- Every `row` of `bytecode` belongs to the emitted rows of a source
instruction in `image`. For example, MRET's JALR belongs to its one-row
expansion. See jolt/crates/jolt-program/src/expand/mod.rs:281-307
at 8bbb2357. -/
theorem expanded_row_has_source
    (image : Rv64ProgramImage SourceInstruction)
    (bytecode : Array JoltInstructionRow)
    (expanded : expand_program image = some bytecode)
    (row : JoltInstructionRow) (member : row ∈ bytecode.toList) :
    ∃ source ∈ image.instructions, ∃ rows,
      expand_instruction source = some rows ∧ row ∈ rows := by
  unfold expand_program at expanded
  cases mapped : image.instructions.toList.mapM expand_instruction with
  | none => simp [mapped] at expanded
  | some blocks =>
    simp only [mapped, Option.map_some, Option.some.injEq] at expanded
    subst bytecode
    rw [List.toList_toArray] at member
    obtain ⟨rows, inBlocks, inRows⟩ := List.mem_flatten.mp member
    obtain ⟨k, inRange, atK⟩ := List.mem_iff_getElem.mp inBlocks
    obtain ⟨lengths, steps⟩ := option_mapM_results expand_instruction _ blocks mapped
    have sourceRange : k < image.instructions.size := by
      simpa only [lengths, Array.length_toList] using inRange
    refine ⟨image.instructions[k], Array.getElem_mem sourceRange, rows, ?_, inRows⟩
    rw [← atK]
    simpa only [Array.getElem_toList sourceRange] using
      steps k (by simpa only [Array.length_toList] using sourceRange) inRange

/-- `NoJump instruction` means the instruction is neither JAL nor JALR.
For example, ADDI has `NoJump`. See
jolt/crates/jolt-riscv/src/instructions/mod.rs:534-537 at 8bbb2357. -/
private def NoJump (instruction : Instr) : Prop :=
  (¬ ∃ dst imm, instruction = Instr.JAL dst imm) ∧
  (¬ ∃ dst base imm, instruction = Instr.JALR dst base imm)
/-- `TerminalNoJump instructions` means the last emitted instruction is neither
JAL nor JALR. For example, the final ADDI in a DIV expansion is not a jump.
See jolt/crates/jolt-program/src/expand/mod.rs:126-170 at 8bbb2357. -/
private def TerminalNoJump (instructions : List Instr) : Prop :=
  ∀ instruction, instructions.getLast? = some instruction → NoJump instruction

private theorem terminalNoJump_divProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    TerminalNoJump (divProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold TerminalNoJump divProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_divuProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    TerminalNoJump (divuProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold TerminalNoJump divuProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_lbProgramAuto (rd rs1 : regidx) (imm : BitVec 12) :
    TerminalNoJump (lbProgramAuto rd rs1 imm).instrs := by
  unfold TerminalNoJump lbProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_lbuProgramAuto (rd rs1 : regidx) (imm : BitVec 12) :
    TerminalNoJump (lbuProgramAuto rd rs1 imm).instrs := by
  unfold TerminalNoJump lbuProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_lhProgramAuto (rd rs1 : regidx) (imm : BitVec 12) :
    TerminalNoJump (lhProgramAuto rd rs1 imm).instrs := by
  unfold TerminalNoJump lhProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_lhuProgramAuto (rd rs1 : regidx) (imm : BitVec 12) :
    TerminalNoJump (lhuProgramAuto rd rs1 imm).instrs := by
  unfold TerminalNoJump lhuProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_lwProgramAuto (rd rs1 : regidx) (imm : BitVec 12) :
    TerminalNoJump (lwProgramAuto rd rs1 imm).instrs := by
  unfold TerminalNoJump lwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_mulhProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (mulhProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump mulhProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_mulhsuProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (mulhsuProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump mulhsuProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_remProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    TerminalNoJump (remProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold TerminalNoJump remProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_remuProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    TerminalNoJump (remuProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold TerminalNoJump remuProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_sbProgramAuto (rs1 rs2 : regidx) (imm : BitVec 12) :
    TerminalNoJump (sbProgramAuto rs1 rs2 imm).instrs := by
  unfold TerminalNoJump sbProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_shProgramAuto (rs1 rs2 : regidx) (imm : BitVec 12) :
    TerminalNoJump (shProgramAuto rs1 rs2 imm).instrs := by
  unfold TerminalNoJump shProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_sllProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (sllProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump sllProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_slliProgramAuto (rd rs1 : regidx) (shamt : BitVec 6) :
    TerminalNoJump (slliProgramAuto rd rs1 shamt).instrs := by
  unfold TerminalNoJump slliProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_sraProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (sraProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump sraProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_sraiProgramAuto (rd rs1 : regidx) (shamt : BitVec 6) :
    TerminalNoJump (sraiProgramAuto rd rs1 shamt).instrs := by
  unfold TerminalNoJump sraiProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_srlProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (srlProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump srlProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_srliProgramAuto (rd rs1 : regidx) (shamt : BitVec 6) :
    TerminalNoJump (srliProgramAuto rd rs1 shamt).instrs := by
  unfold TerminalNoJump srliProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_swProgramAuto (rs1 rs2 : regidx) (imm : BitVec 12) :
    TerminalNoJump (swProgramAuto rs1 rs2 imm).instrs := by
  unfold TerminalNoJump swProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_slliwProgramAuto (rd rs1 : regidx) (shamt : BitVec 5) :
    TerminalNoJump (slliwProgramAuto rd rs1 shamt).instrs := by
  unfold TerminalNoJump slliwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_srliwProgramAuto (rd rs1 : regidx) (shamt : BitVec 5) :
    TerminalNoJump (srliwProgramAuto rd rs1 shamt).instrs := by
  unfold TerminalNoJump srliwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_sraiwProgramAuto (rd rs1 : regidx) (shamt : BitVec 5) :
    TerminalNoJump (sraiwProgramAuto rd rs1 shamt).instrs := by
  unfold TerminalNoJump sraiwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_sllwProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (sllwProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump sllwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_srlwProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (srlwProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump srlwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_srawProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (srawProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump srawProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_lwuProgramAuto (rd rs1 : regidx) (imm : BitVec 12) :
    TerminalNoJump (lwuProgramAuto rd rs1 imm).instrs := by
  unfold TerminalNoJump lwuProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_divuwProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    TerminalNoJump (divuwProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold TerminalNoJump divuwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_divwProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    TerminalNoJump (divwProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold TerminalNoJump divwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_remuwProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    TerminalNoJump (remuwProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold TerminalNoJump remuwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_remwProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    TerminalNoJump (remwProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold TerminalNoJump remwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_lrwProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (lrwProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump lrwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_scwProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (scwProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump scwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amoswapwProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amoswapwProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amoswapwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amoaddwProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amoaddwProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amoaddwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amoandwProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amoandwProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amoandwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amoorwProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amoorwProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amoorwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amoxorwProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amoxorwProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amoxorwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amominwProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amominwProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amominwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amomaxwProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amomaxwProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amomaxwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amominuwProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amominuwProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amominuwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amomaxuwProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amomaxuwProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amomaxuwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_lrdProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (lrdProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump lrdProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_scdProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (scdProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump scdProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amoswapdProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amoswapdProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amoswapdProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amoadddProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amoadddProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amoadddProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amoanddProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amoanddProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amoanddProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amoordProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amoordProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amoordProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amoxordProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amoxordProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amoxordProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amomindProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amomindProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amomindProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amomaxdProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amomaxdProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amomaxdProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amominudProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amominudProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amominudProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_amomaxudProgramAuto (rd rs1 rs2 : regidx) :
    TerminalNoJump (amomaxudProgramAuto rd rs1 rs2).instrs := by
  unfold TerminalNoJump amomaxudProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_advicelbProgramAuto (rd : regidx) :
    TerminalNoJump (advicelbProgramAuto rd).instrs := by
  unfold TerminalNoJump advicelbProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_adviceldProgramAuto (rd : regidx) :
    TerminalNoJump (adviceldProgramAuto rd).instrs := by
  unfold TerminalNoJump adviceldProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_advicelhProgramAuto (rd : regidx) :
    TerminalNoJump (advicelhProgramAuto rd).instrs := by
  unfold TerminalNoJump advicelhProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]
private theorem terminalNoJump_advicelwProgramAuto (rd : regidx) :
    TerminalNoJump (advicelwProgramAuto rd).instrs := by
  unfold TerminalNoJump advicelwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, NoJump]

private theorem terminalNoJump_csrrw (csr : SystemCSR) (rs1 rd : regidx) :
    TerminalNoJump (csrrwProgram csr rs1 rd).instrs := by
  unfold TerminalNoJump csrrwProgram
  split_ifs <;> simp [Program.instrs, NoJump]
private theorem terminalNoJump_csrrs (csr : SystemCSR) (rs1 rd : regidx) :
    TerminalNoJump (csrrsProgram csr rs1 rd).instrs := by
  unfold TerminalNoJump csrrsProgram
  split_ifs <;> simp [Program.instrs, pureWritebackRdZeroProgram, NoJump]

attribute [simp] terminalNoJump_divProgramAuto terminalNoJump_divuProgramAuto terminalNoJump_lbProgramAuto terminalNoJump_lbuProgramAuto terminalNoJump_lhProgramAuto terminalNoJump_lhuProgramAuto terminalNoJump_lwProgramAuto terminalNoJump_mulhProgramAuto terminalNoJump_mulhsuProgramAuto terminalNoJump_remProgramAuto terminalNoJump_remuProgramAuto terminalNoJump_sbProgramAuto terminalNoJump_shProgramAuto terminalNoJump_sllProgramAuto terminalNoJump_slliProgramAuto terminalNoJump_sraProgramAuto terminalNoJump_sraiProgramAuto terminalNoJump_srlProgramAuto terminalNoJump_srliProgramAuto terminalNoJump_swProgramAuto terminalNoJump_slliwProgramAuto terminalNoJump_srliwProgramAuto terminalNoJump_sraiwProgramAuto terminalNoJump_sllwProgramAuto terminalNoJump_srlwProgramAuto terminalNoJump_srawProgramAuto terminalNoJump_lwuProgramAuto terminalNoJump_divuwProgramAuto terminalNoJump_divwProgramAuto terminalNoJump_remuwProgramAuto terminalNoJump_remwProgramAuto terminalNoJump_lrwProgramAuto terminalNoJump_scwProgramAuto terminalNoJump_amoswapwProgramAuto terminalNoJump_amoaddwProgramAuto terminalNoJump_amoandwProgramAuto terminalNoJump_amoorwProgramAuto terminalNoJump_amoxorwProgramAuto terminalNoJump_amominwProgramAuto terminalNoJump_amomaxwProgramAuto terminalNoJump_amominuwProgramAuto terminalNoJump_amomaxuwProgramAuto terminalNoJump_lrdProgramAuto terminalNoJump_scdProgramAuto terminalNoJump_amoswapdProgramAuto terminalNoJump_amoadddProgramAuto terminalNoJump_amoanddProgramAuto terminalNoJump_amoordProgramAuto terminalNoJump_amoxordProgramAuto terminalNoJump_amomindProgramAuto terminalNoJump_amomaxdProgramAuto terminalNoJump_amominudProgramAuto terminalNoJump_amomaxudProgramAuto terminalNoJump_advicelbProgramAuto terminalNoJump_adviceldProgramAuto terminalNoJump_advicelhProgramAuto terminalNoJump_advicelwProgramAuto terminalNoJump_csrrw terminalNoJump_csrrs

/-- If a source expands to a sequence whose last row is JAL or JALR, the
source is ECALL, MRET, or EBREAK. For example, EBREAK's sole emitted row is
`JAL +0`; a DIV sequence ends in an ordinary writeback instruction.
See jolt/crates/jolt-program/src/expand/control_flow/ebreak.rs:1-20,
jolt/crates/jolt-program/src/expand/control_flow/ecall.rs:1-52, and
jolt/crates/jolt-program/src/expand/control_flow/mret.rs:15-20 at 8bbb2357. -/
theorem source_sequence_terminal_jump
    (source : SourceInstruction) (instructions : List Instr)
    (expanded : source.expand = some (.sequence instructions))
    (last : Instr) (terminal : instructions.getLast? = some last)
    (jump : (∃ dst imm, last = .JAL dst imm) ∨
      (∃ dst base imm, last = .JALR dst base imm)) :
    source = .riscv .ECALL ∨ source = .riscv .MRET ∨
      source = .riscv .EBREAK := by
  by_cases ecall : source = .riscv .ECALL
  · exact Or.inl ecall
  by_cases mret : source = .riscv .MRET
  · exact Or.inr (Or.inl mret)
  by_cases ebreak : source = .riscv .EBREAK
  · exact Or.inr (Or.inr ebreak)
  have noJump : TerminalNoJump instructions := by
    cases source with
    | riscv instruction =>
      cases instruction <;>
        simp only [SourceInstruction.expand, ExpandedSource.ofNative,
          ExpandedSource.ofProgram, ExpandedSource.ofPureProgram,
          JoltISA.Instr.rewriteNative] at expanded
      all_goals try exact False.elim (ecall rfl)
      all_goals try exact False.elim (mret rfl)
      all_goals try exact False.elim (ebreak rfl)
      all_goals try split_ifs at expanded
      all_goals try cases expanded
      all_goals first | assumption | (try simp)
    | jolt instruction =>
      cases instruction <;>
        simp only [SourceInstruction.expand, ExpandedSource.ofNative,
          ExpandedSource.ofProgram] at expanded
      all_goals try cases expanded
      all_goals first | assumption | (try simp)
  rcases jump with ⟨dst, imm, h⟩ | ⟨dst, base, imm, h⟩
  · exact False.elim ((noJump last terminal).1 ⟨dst, imm, h⟩)
  · exact False.elim ((noJump last terminal).2 ⟨dst, base, imm, h⟩)

/-- A JALR in a checked sequence is its last emitted instruction. For example,
ECALL's JALR is the seventh and final emitted row.
See jolt/crates/jolt-program/src/expand/control_flow/ecall.rs:1-52 at 8bbb2357. -/
private theorem sequence_jalr_terminal
    (source : SourceInstruction) (instructions : List Instr)
    (expanded : source.expand = some (.sequence instructions))
    (k : Nat) (inRange : k < instructions.length)
    (dst : Dst) (base : Src) (imm : BitVec 64)
    (jump : instructions[k] = .JALR dst base imm) :
    instructions.getLast? = some instructions[k] := by
  have good : ExpansionFacts.sequenceOk instructions = true :=
    ExpansionFacts.expand_ok source (.sequence instructions) expanded
  have rowsOk : ExpansionFacts.rowsOk instructions = true := by
    simp only [ExpansionFacts.sequenceOk, Bool.and_eq_true] at good
    exact good.1.1
  have ordinaryIfLater := (ExpansionRows.rowsOk_rows instructions rowsOk k inRange).2
  have noLater : ¬ k + 1 < instructions.length := by
    intro later
    have ordinary := ordinaryIfLater later
    rw [jump] at ordinary
    simp [ExpansionFacts.ordinary, JoltMetadata.opcodeFlag] at ordinary
  have lastIndex : instructions.length - 1 = k := by omega
  rw [List.getLast?_eq_getElem?, lastIndex, List.getElem?_eq_getElem inRange]
/-- Stamping a sequence preserves which JALR is last. For example, the stamped
MRET JALR is its only row and thus its terminal instruction.
See jolt/crates/jolt-program/src/expand/metadata.rs:25-53 at 8bbb2357. -/
private theorem stamp_sequence_jalr_terminal
    (source : SourceInstruction) (instructions : List Instr)
    (expanded : source.expand = some (.sequence instructions))
    (address : BitVec 64) (compressed : Bool)
    (row : JoltInstructionRow)
    (member : row ∈ stamp_sequence address compressed instructions)
    (dst : Dst) (base : Src) (imm : BitVec 64)
    (jump : row.instruction = .JALR dst base imm) :
    instructions.getLast? = some row.instruction := by
  obtain ⟨k, inRange, atK⟩ := List.mem_iff_getElem.mp member
  have instrRange : k < instructions.length := by
    simpa only [stamp_sequence, List.length_map, List.length_zipIdx] using inRange
  have instrEq : (stamp_sequence address compressed instructions)[k].instruction =
      instructions[k] := by
    simp [stamp_sequence, List.getElem_map, List.getElem_zipIdx]
  rw [← atK, instrEq] at jump ⊢
  exact sequence_jalr_terminal source instructions expanded k instrRange
    dst base imm jump

/-- A JALR row in `source`'s stamped sequence is exactly ECALL's jump through
`mtvec` or MRET's jump through `mepc`; both write the link to a virtual scratch
register. For example, MRET emits `JALR v40, 0(v36)`.
See jolt/crates/jolt-program/src/expand/control_flow/ecall.rs:47-52 and
jolt/crates/jolt-program/src/expand/control_flow/mret.rs:15-20 at 8bbb2357. -/
theorem sequence_jalr_system_form
    (source : SourceInstruction) (instructions : List Instr)
    (expanded : source.expand = some (.sequence instructions))
    (address : BitVec 64) (compressed : Bool)
    (row : JoltInstructionRow)
    (member : row ∈ stamp_sequence address compressed instructions)
    (dst : Dst) (base : Src) (imm : BitVec 64)
    (jump : row.instruction = .JALR dst base imm) :
    (source = .riscv .ECALL ∧
      row.instruction = .JALR (.vreg systemScratchVReg) (.vreg trapHandlerVReg) 0) ∨
    (source = .riscv .MRET ∧
      row.instruction = .JALR (.vreg systemScratchVReg) (.vreg mepcVReg) 0) := by
  have terminal := stamp_sequence_jalr_terminal source instructions expanded
    address compressed row member dst base imm jump
  rcases source_sequence_terminal_jump source instructions expanded row.instruction
      terminal (Or.inr ⟨dst, base, imm, jump⟩) with ecall | mret | ebreak
  · left
    refine ⟨ecall, ?_⟩
    subst source
    simp [SourceInstruction.expand, ExpandedSource.ofProgram] at expanded
    subst instructions
    simp [ecallProgram, Program.instrs] at terminal
    exact terminal.symm
  · right
    refine ⟨mret, ?_⟩
    subst source
    simp [SourceInstruction.expand, ExpandedSource.ofProgram] at expanded
    subst instructions
    simp [mretProgram, Program.instrs] at terminal
    exact terminal.symm
  · subst source
    simp [SourceInstruction.expand, ExpandedSource.ofProgram] at expanded
    subst instructions
    simp [ebreakProgram, Program.instrs] at terminal
    rw [jump] at terminal
    cases terminal

/-- An expanded JALR with an architectural base occupies its source's only
row. For example, native `jalr x1, 0(x2)` is one bytecode row, whereas MRET's
JALR reads a virtual base. See jolt/crates/jolt-program/src/expand/mod.rs:126-170
at 8bbb2357. -/
theorem expanded_arch_jalr_singleton
    (source : SourceInstructionRow SourceInstruction)
    (rows : List JoltInstructionRow)
    (expanded : expand_instruction source = some rows)
    (row : JoltInstructionRow) (member : row ∈ rows)
    (dst : Dst) (rs1 : regidx) (imm : BitVec 64)
    (jump : row.instruction = .JALR dst (.xreg rs1) imm) :
    rows = [row] := by
  unfold expand_instruction at expanded
  cases sourceExpansion : source.instruction.expand with
  | none => simp [sourceExpansion] at expanded
  | some result =>
    cases result with
    | native instruction =>
      simp only [sourceExpansion, Option.some.injEq] at expanded
      subst rows
      simp only [List.mem_singleton] at member
      subst row
      rfl
    | sequence instructions =>
      simp only [sourceExpansion] at expanded
      split_ifs at expanded
      simp only [Option.some.injEq] at expanded
      subst rows
      rcases sequence_jalr_system_form source.instruction instructions
          sourceExpansion source.address source.is_compressed row member dst
          (.xreg rs1) imm jump with ⟨_, systemJump⟩ | ⟨_, systemJump⟩
      · rw [jump] at systemJump
        cases systemJump
      · rw [jump] at systemJump
        cases systemJump

/-- `NoStore instructions` says that none of the emitted instructions has Jolt's
Store circuit flag. For example, the single JAL row emitted for EBREAK has no
Store flag. See jolt/crates/jolt-riscv/src/lib.rs:399-421 at 8bbb2357. -/
def NoStore (instructions : List Instr) : Prop :=
  ∀ instruction ∈ instructions, JoltMetadata.opcodeFlag instruction .Store = false

/-- ECALL's emitted AUIPC, ADDI, multiplication, and JALR rows do not store to
RAM. For example, the final JALR through `mtvec` has no Store flag.
See jolt/crates/jolt-program/src/expand/control_flow/ecall.rs:1-52 at 8bbb2357. -/
theorem ecallProgram_noStore : NoStore ecallProgram.instrs := by
  simp [NoStore, ecallProgram, Program.instrs, JoltMetadata.opcodeFlag]

/-- MRET's emitted JALR through `mepc` has no Store flag; its link destination
is a temporary virtual register. See
jolt/crates/jolt-program/src/expand/control_flow/mret.rs:15-20 at 8bbb2357. -/
theorem mretProgram_noStore : NoStore mretProgram.instrs := by
  simp [NoStore, mretProgram, Program.instrs, JoltMetadata.opcodeFlag]

/-- EBREAK's emitted JAL with zero offset has no Store flag. For example,
executing EBREAK does not update the termination RAM word.
See jolt/crates/jolt-program/src/expand/control_flow/ebreak.rs:1-20 at 8bbb2357. -/
theorem ebreakProgram_noStore : NoStore ebreakProgram.instrs := by
  simp [NoStore, ebreakProgram, Program.instrs, JoltMetadata.opcodeFlag]

/-- No ECALL row writes its JALR base, the virtual `mtvec` register. For example,
ECALL's AUIPC writes temporary v40 while the final JALR reads `mtvec` v34.
See jolt/crates/jolt-program/src/expand/control_flow/ecall.rs:1-52 at 8bbb2357. -/
theorem ecallProgram_base_unwritten :
    ∀ instruction ∈ ecallProgram.instrs, ∀ dst : JoltISA.Dst,
      instruction.destination? = some dst →
      TraceWitness.destinationRegisterAddress dst ≠
        TraceWitness.sourceRegisterAddress (.vreg trapHandlerVReg) := by
  simp [ecallProgram, Program.instrs, Instr.destination?,
    TraceWitness.destinationRegisterAddress, TraceWitness.sourceRegisterAddress,
    trapHandlerVReg, systemScratchVReg, mepcVReg, mcauseVReg, mtvalVReg,
    mstatusVReg, inlineTmp0, inlineTmp, inlineRegisterBase, riscvRegisterBase,
    numReservedVirtualRegisters, riscvRegisterCount]

/-- MRET's sole JALR writes a temporary and leaves its virtual `mepc` base
unwritten. For example, a return through `mepc` v36 writes the link to v40.
See jolt/crates/jolt-program/src/expand/control_flow/mret.rs:15-20 at 8bbb2357. -/
theorem mretProgram_base_unwritten :
    ∀ instruction ∈ mretProgram.instrs, ∀ dst : JoltISA.Dst,
      instruction.destination? = some dst →
      TraceWitness.destinationRegisterAddress dst ≠
        TraceWitness.sourceRegisterAddress (.vreg mepcVReg) := by
  simp [mretProgram, Program.instrs, Instr.destination?,
    TraceWitness.destinationRegisterAddress, TraceWitness.sourceRegisterAddress,
    mepcVReg, systemScratchVReg, inlineTmp0, inlineTmp, inlineRegisterBase,
    riscvRegisterBase, numReservedVirtualRegisters, riscvRegisterCount]

end JoltInstance
