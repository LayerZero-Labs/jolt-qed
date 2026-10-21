import JoltConstraints.Soundness.Layer6.ExecutionPrefix

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions JoltISA

namespace JoltInstance

/-- `NoControl rows` means no instruction in `rows` is JAL, JALR, or a branch.
For example, a list containing only an ADDI instruction has `NoControl`.
See jolt/crates/jolt-program/src/expand/mod.rs:126-170 at 8bbb2357. -/
def NoControl (rows : List Instr) : Prop :=
  ∀ instruction ∈ rows,
    (¬ ∃ dst imm, instruction = Instr.JAL dst imm) ∧
    (¬ ∃ dst base imm, instruction = Instr.JALR dst base imm) ∧
    JoltMetadata.instructionFlag instruction .Branch = false
private theorem noControl_divProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    NoControl (divProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold NoControl divProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_divuProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    NoControl (divuProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold NoControl divuProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_lbProgramAuto (rd rs1 : regidx) (imm : BitVec 12) :
    NoControl (lbProgramAuto rd rs1 imm).instrs := by
  unfold NoControl lbProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_lbuProgramAuto (rd rs1 : regidx) (imm : BitVec 12) :
    NoControl (lbuProgramAuto rd rs1 imm).instrs := by
  unfold NoControl lbuProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_lhProgramAuto (rd rs1 : regidx) (imm : BitVec 12) :
    NoControl (lhProgramAuto rd rs1 imm).instrs := by
  unfold NoControl lhProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_lhuProgramAuto (rd rs1 : regidx) (imm : BitVec 12) :
    NoControl (lhuProgramAuto rd rs1 imm).instrs := by
  unfold NoControl lhuProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_lwProgramAuto (rd rs1 : regidx) (imm : BitVec 12) :
    NoControl (lwProgramAuto rd rs1 imm).instrs := by
  unfold NoControl lwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_mulhProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (mulhProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl mulhProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_mulhsuProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (mulhsuProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl mulhsuProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_remProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    NoControl (remProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold NoControl remProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_remuProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    NoControl (remuProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold NoControl remuProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_sbProgramAuto (rs1 rs2 : regidx) (imm : BitVec 12) :
    NoControl (sbProgramAuto rs1 rs2 imm).instrs := by
  unfold NoControl sbProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_shProgramAuto (rs1 rs2 : regidx) (imm : BitVec 12) :
    NoControl (shProgramAuto rs1 rs2 imm).instrs := by
  unfold NoControl shProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_sllProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (sllProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl sllProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_slliProgramAuto (rd rs1 : regidx) (shamt : BitVec 6) :
    NoControl (slliProgramAuto rd rs1 shamt).instrs := by
  unfold NoControl slliProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_sraProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (sraProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl sraProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_sraiProgramAuto (rd rs1 : regidx) (shamt : BitVec 6) :
    NoControl (sraiProgramAuto rd rs1 shamt).instrs := by
  unfold NoControl sraiProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_srlProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (srlProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl srlProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_srliProgramAuto (rd rs1 : regidx) (shamt : BitVec 6) :
    NoControl (srliProgramAuto rd rs1 shamt).instrs := by
  unfold NoControl srliProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_swProgramAuto (rs1 rs2 : regidx) (imm : BitVec 12) :
    NoControl (swProgramAuto rs1 rs2 imm).instrs := by
  unfold NoControl swProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_slliwProgramAuto (rd rs1 : regidx) (shamt : BitVec 5) :
    NoControl (slliwProgramAuto rd rs1 shamt).instrs := by
  unfold NoControl slliwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_srliwProgramAuto (rd rs1 : regidx) (shamt : BitVec 5) :
    NoControl (srliwProgramAuto rd rs1 shamt).instrs := by
  unfold NoControl srliwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_sraiwProgramAuto (rd rs1 : regidx) (shamt : BitVec 5) :
    NoControl (sraiwProgramAuto rd rs1 shamt).instrs := by
  unfold NoControl sraiwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_sllwProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (sllwProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl sllwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_srlwProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (srlwProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl srlwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_srawProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (srawProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl srawProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_lwuProgramAuto (rd rs1 : regidx) (imm : BitVec 12) :
    NoControl (lwuProgramAuto rd rs1 imm).instrs := by
  unfold NoControl lwuProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_divuwProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    NoControl (divuwProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold NoControl divuwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_divwProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    NoControl (divwProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold NoControl divwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_remuwProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    NoControl (remuwProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold NoControl remuwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_remwProgramAuto (rd rs1 rs2 : regidx) (advice0 : BitVec 64) :
    NoControl (remwProgramAuto rd rs1 rs2 advice0).instrs := by
  unfold NoControl remwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_lrwProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (lrwProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl lrwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_scwProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (scwProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl scwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amoswapwProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amoswapwProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amoswapwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amoaddwProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amoaddwProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amoaddwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amoandwProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amoandwProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amoandwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amoorwProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amoorwProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amoorwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amoxorwProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amoxorwProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amoxorwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amominwProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amominwProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amominwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amomaxwProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amomaxwProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amomaxwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amominuwProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amominuwProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amominuwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amomaxuwProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amomaxuwProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amomaxuwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_lrdProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (lrdProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl lrdProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_scdProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (scdProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl scdProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amoswapdProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amoswapdProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amoswapdProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amoadddProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amoadddProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amoadddProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amoanddProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amoanddProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amoanddProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amoordProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amoordProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amoordProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amoxordProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amoxordProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amoxordProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amomindProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amomindProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amomindProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amomaxdProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amomaxdProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amomaxdProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amominudProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amominudProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amominudProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_amomaxudProgramAuto (rd rs1 rs2 : regidx) :
    NoControl (amomaxudProgramAuto rd rs1 rs2).instrs := by
  unfold NoControl amomaxudProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_advicelbProgramAuto (rd : regidx) :
    NoControl (advicelbProgramAuto rd).instrs := by
  unfold NoControl advicelbProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_adviceldProgramAuto (rd : regidx) :
    NoControl (adviceldProgramAuto rd).instrs := by
  unfold NoControl adviceldProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_advicelhProgramAuto (rd : regidx) :
    NoControl (advicelhProgramAuto rd).instrs := by
  unfold NoControl advicelhProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_advicelwProgramAuto (rd : regidx) :
    NoControl (advicelwProgramAuto rd).instrs := by
  unfold NoControl advicelwProgramAuto
  try split_ifs
  all_goals simp [Program.instrs, JoltMetadata.instructionFlag]

private theorem noControl_csrrw (csr : SystemCSR) (rs1 rd : regidx) :
    NoControl (csrrwProgram csr rs1 rd).instrs := by
  unfold NoControl csrrwProgram
  split_ifs <;> simp [Program.instrs, JoltMetadata.instructionFlag]
private theorem noControl_csrrs (csr : SystemCSR) (rs1 rd : regidx) :
    NoControl (csrrsProgram csr rs1 rd).instrs := by
  unfold NoControl csrrsProgram
  split_ifs <;> simp [Program.instrs, pureWritebackRdZeroProgram, JoltMetadata.instructionFlag]

attribute [simp] noControl_divProgramAuto noControl_divuProgramAuto noControl_lbProgramAuto noControl_lbuProgramAuto noControl_lhProgramAuto noControl_lhuProgramAuto noControl_lwProgramAuto noControl_mulhProgramAuto noControl_mulhsuProgramAuto noControl_remProgramAuto noControl_remuProgramAuto noControl_sbProgramAuto noControl_shProgramAuto noControl_sllProgramAuto noControl_slliProgramAuto noControl_sraProgramAuto noControl_sraiProgramAuto noControl_srlProgramAuto noControl_srliProgramAuto noControl_swProgramAuto noControl_slliwProgramAuto noControl_srliwProgramAuto noControl_sraiwProgramAuto noControl_sllwProgramAuto noControl_srlwProgramAuto noControl_srawProgramAuto noControl_lwuProgramAuto noControl_divuwProgramAuto noControl_divwProgramAuto noControl_remuwProgramAuto noControl_remwProgramAuto noControl_lrwProgramAuto noControl_scwProgramAuto noControl_amoswapwProgramAuto noControl_amoaddwProgramAuto noControl_amoandwProgramAuto noControl_amoorwProgramAuto noControl_amoxorwProgramAuto noControl_amominwProgramAuto noControl_amomaxwProgramAuto noControl_amominuwProgramAuto noControl_amomaxuwProgramAuto noControl_lrdProgramAuto noControl_scdProgramAuto noControl_amoswapdProgramAuto noControl_amoadddProgramAuto noControl_amoanddProgramAuto noControl_amoordProgramAuto noControl_amoxordProgramAuto noControl_amomindProgramAuto noControl_amomaxdProgramAuto noControl_amominudProgramAuto noControl_amomaxudProgramAuto noControl_advicelbProgramAuto noControl_adviceldProgramAuto noControl_advicelhProgramAuto noControl_advicelwProgramAuto noControl_csrrw noControl_csrrs

/-- If `source` expands to `instrs` and is neither ECALL, MRET, nor EBREAK,
`instrs` contains no JAL, JALR, or branch row. For example, an expanded DIV
sequence contains arithmetic and assertion rows but no control-flow row.
See jolt/crates/jolt-program/src/expand/mod.rs:126-170 at 8bbb2357. -/
theorem source_sequence_noControl
    (source : SourceInstruction) (instrs : List Instr)
    (expanded : source.expand = some (.sequence instrs))
    (notEcall : source ≠ .riscv .ECALL)
    (notMret : source ≠ .riscv .MRET)
    (notEbreak : source ≠ .riscv .EBREAK) :
    NoControl instrs := by
  cases source with
  | riscv instruction =>
      cases instruction <;>
        simp_all [SourceInstruction.expand, ExpandedSource.ofNative,
          ExpandedSource.ofProgram, ExpandedSource.ofPureProgram,
          JoltISA.Instr.rewriteNative]
      all_goals try split_ifs at expanded
      all_goals try cases expanded
      all_goals try simp_all
  | jolt instruction =>
      cases instruction <;>
        simp_all [SourceInstruction.expand, ExpandedSource.ofNative,
          ExpandedSource.ofProgram, ExpandedSource.ofPureProgram,
          JoltISA.Instr.rewriteNative]
      all_goals try cases expanded
      all_goals try simp_all

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
