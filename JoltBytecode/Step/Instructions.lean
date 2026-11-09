import JoltBytecode.RiscvInstruction
import JoltBytecode.Step.Lift
import JoltBytecode.Step.AmoFlags
import JoltBytecode.Step.Invariant

/-!
# Instruction theorems against Sail's `execute`

The per-instruction theorems prove each instruction's Jolt rows against the matching
`execute_X` function on the embedded Sail state. This file restates all of them
in one shape: the rows `joltRun i`, projected through
the CSR overlay, agree with `execute ast` on the projected state, for the Sail
instruction `ast` that `i` stands for (`Matches i ast`). That is the `hprog`
hypothesis of `Step.joltStep_base` and `Step.joltStep_compressed`, so each
instruction theorem lifts to a full `try_step`.

Two points need more than unfolding:
- FENCE: Jolt runs every Sail FENCE as one no-op row, so `Matches` relates
  `.FENCE` to every `fm`, `pred`, `succ`, `rs1`, `rd`.
- Atomics: the instruction theorems are stated with `aq = rl = false`;
  `Step.execute_AMO_flags` shows the bits never change Sail's semantics.

The proofs call the proved instruction theorems directly.
`joltRun_eq_execute` is the single dispatcher for retiring instructions.
ECALL needs a separate step theorem because Sail enters the trap handler.
EBREAK ends the whole-run comparison before its rows execute.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

namespace RiscvInstruction

/-- The Jolt rows that run each source instruction: a native row or an
expansion.
For example, ECALL runs `ecallProgram`, even though `Lifted` excludes it. -/
noncomputable def joltRun : RiscvInstruction → JoltMonad ExecutionResult
  | .LUI rd imm => JoltISA.execLUI imm rd
  | .AUIPC rd imm => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (JoltISA.Encoded.AUIPC (.xreg rd) imm))
  | .JAL rd imm => JoltISA.execInstr ((JoltISA.Encoded.JAL (.xreg rd) imm).rewriteNative)
  | .JALR rd rs1 imm => JoltISA.execInstr ((JoltISA.Encoded.JALR (.xreg rd) (.xreg rs1) imm).rewriteNative)
  | .BEQ rs1 rs2 imm => JoltISA.execInstr (JoltISA.Encoded.BEQ (.xreg rs1) (.xreg rs2) imm)
  | .BNE rs1 rs2 imm => JoltISA.execInstr (JoltISA.Encoded.BNE (.xreg rs1) (.xreg rs2) imm)
  | .BLT rs1 rs2 imm => JoltISA.execInstr (JoltISA.Encoded.BLT (.xreg rs1) (.xreg rs2) imm)
  | .BGE rs1 rs2 imm => JoltISA.execInstr (JoltISA.Encoded.BGE (.xreg rs1) (.xreg rs2) imm)
  | .BLTU rs1 rs2 imm => JoltISA.execInstr (JoltISA.Encoded.BLTU (.xreg rs1) (.xreg rs2) imm)
  | .BGEU rs1 rs2 imm => JoltISA.execInstr (JoltISA.Encoded.BGEU (.xreg rs1) (.xreg rs2) imm)
  | .LB rd rs1 imm => JoltISA.execProgram (JoltISA.lbProgramAuto rd rs1 imm)
  | .LH rd rs1 imm => JoltISA.execProgram (JoltISA.lhProgramAuto rd rs1 imm)
  | .LW rd rs1 imm => JoltISA.execProgram (JoltISA.lwProgramAuto rd rs1 imm)
  | .LBU rd rs1 imm => JoltISA.execProgram (JoltISA.lbuProgramAuto rd rs1 imm)
  | .LHU rd rs1 imm => JoltISA.execProgram (JoltISA.lhuProgramAuto rd rs1 imm)
  | .ADDI rd rs1 imm => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (JoltISA.Encoded.ADDI (.xreg rd) (.xreg rs1) imm))
  | .SLTI rd rs1 imm => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (JoltISA.Encoded.SLTI (.xreg rd) (.xreg rs1) imm))
  | .SLTIU rd rs1 imm => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (JoltISA.Encoded.SLTIU (.xreg rd) (.xreg rs1) imm))
  | .XORI rd rs1 imm => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (JoltISA.Encoded.XORI (.xreg rd) (.xreg rs1) imm))
  | .ORI rd rs1 imm => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (JoltISA.Encoded.ORI (.xreg rd) (.xreg rs1) imm))
  | .ANDI rd rs1 imm => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (JoltISA.Encoded.ANDI (.xreg rd) (.xreg rs1) imm))
  | .SLLI rd rs1 shamt => JoltISA.execProgram (JoltISA.slliProgramAuto rd rs1 shamt)
  | .SRLI rd rs1 shamt => JoltISA.execProgram (JoltISA.srliProgramAuto rd rs1 shamt)
  | .SRAI rd rs1 shamt => JoltISA.execProgram (JoltISA.sraiProgramAuto rd rs1 shamt)
  | .ADD rd rs1 rs2 => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .SUB rd rs1 rs2 => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .SLL rd rs1 rs2 => JoltISA.execProgram (JoltISA.sllProgramAuto rd rs1 rs2)
  | .SLT rd rs1 rs2 => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (.SLT (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .SLTU rd rs1 rs2 => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (.SLTU (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .XOR rd rs1 rs2 => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (.XOR (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .SRL rd rs1 rs2 => JoltISA.execProgram (JoltISA.srlProgramAuto rd rs1 rs2)
  | .SRA rd rs1 rs2 => JoltISA.execProgram (JoltISA.sraProgramAuto rd rs1 rs2)
  | .OR rd rs1 rs2 => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (.OR (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .AND rd rs1 rs2 => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (.AND (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .ANDN rd rs1 rs2 => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (.ANDN (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .FENCE => JoltISA.execInstr .FENCE
  | .ECALL => JoltISA.execProgram JoltISA.ecallProgram
  | .EBREAK => JoltISA.execProgram JoltISA.ebreakProgram
  | .LWU rd rs1 imm => JoltISA.execProgram (JoltISA.lwuProgramAuto rd rs1 imm)
  | .LD rd rs1 imm => JoltISA.execInstr (JoltISA.ldNativeInstr rd rs1 imm)
  | .ADDIW rd rs1 imm => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (JoltISA.Encoded.ADDIW (.xreg rd) (.xreg rs1) imm))
  | .SLLIW rd rs1 shamt => JoltISA.execProgram (JoltISA.slliwProgramAuto rd rs1 shamt)
  | .SRLIW rd rs1 shamt => JoltISA.execProgram (JoltISA.srliwProgramAuto rd rs1 shamt)
  | .SRAIW rd rs1 shamt => JoltISA.execProgram (JoltISA.sraiwProgramAuto rd rs1 shamt)
  | .ADDW rd rs1 rs2 => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (.ADDW (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .SUBW rd rs1 rs2 => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (.SUBW (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .SLLW rd rs1 rs2 => JoltISA.execProgram (JoltISA.sllwProgramAuto rd rs1 rs2)
  | .SRLW rd rs1 rs2 => JoltISA.execProgram (JoltISA.srlwProgramAuto rd rs1 rs2)
  | .SRAW rd rs1 rs2 => JoltISA.execProgram (JoltISA.srawProgramAuto rd rs1 rs2)
  | .MUL rd rs1 rs2 => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (.MUL (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .MULH rd rs1 rs2 => JoltISA.execProgram (JoltISA.mulhProgramAuto rd rs1 rs2)
  | .MULHU rd rs1 rs2 => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (.MULHU (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .MULHSU rd rs1 rs2 => JoltISA.execProgram (JoltISA.mulhsuProgramAuto rd rs1 rs2)
  | .DIV rd rs1 rs2 quotient => JoltISA.execProgram (JoltISA.divProgramAuto rd rs1 rs2 quotient)
  | .DIVU rd rs1 rs2 quotient => JoltISA.execProgram (JoltISA.divuProgramAuto rd rs1 rs2 quotient)
  | .REM rd rs1 rs2 quotientMagnitude => JoltISA.execProgram (JoltISA.remProgramAuto rd rs1 rs2 quotientMagnitude)
  | .REMU rd rs1 rs2 quotient => JoltISA.execProgram (JoltISA.remuProgramAuto rd rs1 rs2 quotient)
  | .MULW rd rs1 rs2 => JoltISA.execInstr (JoltISA.pureWritebackNativeInstr rd (.MULW (.xreg rd) (.xreg rs1) (.xreg rs2)))
  | .DIVW rd rs1 rs2 quotient => JoltISA.execProgram (JoltISA.divwProgramAuto rd rs1 rs2 quotient)
  | .DIVUW rd rs1 rs2 quotient => JoltISA.execProgram (JoltISA.divuwProgramAuto rd rs1 rs2 quotient)
  | .REMW rd rs1 rs2 quotientMagnitude => JoltISA.execProgram (JoltISA.remwProgramAuto rd rs1 rs2 quotientMagnitude)
  | .REMUW rd rs1 rs2 quotient => JoltISA.execProgram (JoltISA.remuwProgramAuto rd rs1 rs2 quotient)
  | .LR_W rd rs1 _aq _rl => JoltISA.execProgram (JoltISA.lrwProgramAuto rd rs1 (regidx.Regidx 0))
  | .SC_W rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.scwProgramAuto rd rs1 rs2)
  | .SB rs2 rs1 imm => JoltISA.execProgram (JoltISA.sbProgramAuto rs1 rs2 imm)
  | .SH rs2 rs1 imm => JoltISA.execProgram (JoltISA.shProgramAuto rs1 rs2 imm)
  | .SW rs2 rs1 imm => JoltISA.execProgram (JoltISA.swProgramAuto rs1 rs2 imm)
  | .SD rs2 rs1 imm => JoltISA.execInstr (JoltISA.Encoded.SD (.xreg rs1) (.xreg rs2) imm)
  | .AMOSWAP_W rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amoswapwProgramAuto rd rs1 rs2)
  | .AMOADD_W rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amoaddwProgramAuto rd rs1 rs2)
  | .AMOXOR_W rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amoxorwProgramAuto rd rs1 rs2)
  | .AMOAND_W rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amoandwProgramAuto rd rs1 rs2)
  | .AMOOR_W rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amoorwProgramAuto rd rs1 rs2)
  | .AMOMIN_W rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amominwProgramAuto rd rs1 rs2)
  | .AMOMAX_W rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amomaxwProgramAuto rd rs1 rs2)
  | .AMOMINU_W rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amominuwProgramAuto rd rs1 rs2)
  | .AMOMAXU_W rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amomaxuwProgramAuto rd rs1 rs2)
  | .LR_D rd rs1 _aq _rl => JoltISA.execProgram (JoltISA.lrdProgramAuto rd rs1 (regidx.Regidx 0))
  | .SC_D rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.scdProgramAuto rd rs1 rs2)
  | .AMOSWAP_D rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amoswapdProgramAuto rd rs1 rs2)
  | .AMOADD_D rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amoadddProgramAuto rd rs1 rs2)
  | .AMOXOR_D rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amoxordProgramAuto rd rs1 rs2)
  | .AMOAND_D rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amoanddProgramAuto rd rs1 rs2)
  | .AMOOR_D rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amoordProgramAuto rd rs1 rs2)
  | .AMOMIN_D rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amomindProgramAuto rd rs1 rs2)
  | .AMOMAX_D rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amomaxdProgramAuto rd rs1 rs2)
  | .AMOMINU_D rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amominudProgramAuto rd rs1 rs2)
  | .AMOMAXU_D rd rs1 rs2 _aq _rl => JoltISA.execProgram (JoltISA.amomaxudProgramAuto rd rs1 rs2)
  | .CSRRW rd csr rs1 => JoltISA.execProgram (JoltISA.csrrwProgram csr rs1 rd)
  | .CSRRS rd csr rs1 => JoltISA.execProgram (JoltISA.csrrsProgram csr rs1 rd)
  | .CSRRC rd csr rs1 => JoltISA.execProgram (JoltISA.csrrcProgram csr rs1 rd)
  | .CSRRWI rd csr uimm => JoltISA.execProgram (JoltISA.csrrwiProgram csr uimm rd)
  | .CSRRSI rd csr uimm => JoltISA.execProgram (JoltISA.csrrsiProgram csr uimm rd)
  | .CSRRCI rd csr uimm => JoltISA.execProgram (JoltISA.csrrciProgram csr uimm rd)
  | .MRET => JoltISA.execProgram JoltISA.mretProgram

/-- `Matches i ast`: `ast` is the Sail instruction that `i` stands for. FENCE
matches every Sail FENCE (Jolt runs all of them as a no-op), and atomics keep
their `aq`/`rl` bits. -/
def Matches : RiscvInstruction → instruction → Prop
  | .LUI rd imm, ast => ast = .UTYPE (imm, rd, uop.LUI)
  | .AUIPC rd imm, ast => ast = .UTYPE (imm, rd, uop.AUIPC)
  | .JAL rd imm, ast => ast = .JAL (imm, rd)
  | .JALR rd rs1 imm, ast => ast = .JALR (imm, rs1, rd)
  | .BEQ rs1 rs2 imm, ast => ast = .BTYPE (imm, rs2, rs1, bop.BEQ)
  | .BNE rs1 rs2 imm, ast => ast = .BTYPE (imm, rs2, rs1, bop.BNE)
  | .BLT rs1 rs2 imm, ast => ast = .BTYPE (imm, rs2, rs1, bop.BLT)
  | .BGE rs1 rs2 imm, ast => ast = .BTYPE (imm, rs2, rs1, bop.BGE)
  | .BLTU rs1 rs2 imm, ast => ast = .BTYPE (imm, rs2, rs1, bop.BLTU)
  | .BGEU rs1 rs2 imm, ast => ast = .BTYPE (imm, rs2, rs1, bop.BGEU)
  | .LB rd rs1 imm, ast => ast = .LOAD (imm, rs1, rd, false, 1)
  | .LH rd rs1 imm, ast => ast = .LOAD (imm, rs1, rd, false, 2)
  | .LW rd rs1 imm, ast => ast = .LOAD (imm, rs1, rd, false, 4)
  | .LBU rd rs1 imm, ast => ast = .LOAD (imm, rs1, rd, true, 1)
  | .LHU rd rs1 imm, ast => ast = .LOAD (imm, rs1, rd, true, 2)
  | .ADDI rd rs1 imm, ast => ast = .ITYPE (imm, rs1, rd, iop.ADDI)
  | .SLTI rd rs1 imm, ast => ast = .ITYPE (imm, rs1, rd, iop.SLTI)
  | .SLTIU rd rs1 imm, ast => ast = .ITYPE (imm, rs1, rd, iop.SLTIU)
  | .XORI rd rs1 imm, ast => ast = .ITYPE (imm, rs1, rd, iop.XORI)
  | .ORI rd rs1 imm, ast => ast = .ITYPE (imm, rs1, rd, iop.ORI)
  | .ANDI rd rs1 imm, ast => ast = .ITYPE (imm, rs1, rd, iop.ANDI)
  | .SLLI rd rs1 shamt, ast => ast = .SHIFTIOP (shamt, rs1, rd, sop.SLLI)
  | .SRLI rd rs1 shamt, ast => ast = .SHIFTIOP (shamt, rs1, rd, sop.SRLI)
  | .SRAI rd rs1 shamt, ast => ast = .SHIFTIOP (shamt, rs1, rd, sop.SRAI)
  | .ADD rd rs1 rs2, ast => ast = .RTYPE (rs2, rs1, rd, rop.ADD)
  | .SUB rd rs1 rs2, ast => ast = .RTYPE (rs2, rs1, rd, rop.SUB)
  | .SLL rd rs1 rs2, ast => ast = .RTYPE (rs2, rs1, rd, rop.SLL)
  | .SLT rd rs1 rs2, ast => ast = .RTYPE (rs2, rs1, rd, rop.SLT)
  | .SLTU rd rs1 rs2, ast => ast = .RTYPE (rs2, rs1, rd, rop.SLTU)
  | .XOR rd rs1 rs2, ast => ast = .RTYPE (rs2, rs1, rd, rop.XOR)
  | .SRL rd rs1 rs2, ast => ast = .RTYPE (rs2, rs1, rd, rop.SRL)
  | .SRA rd rs1 rs2, ast => ast = .RTYPE (rs2, rs1, rd, rop.SRA)
  | .OR rd rs1 rs2, ast => ast = .RTYPE (rs2, rs1, rd, rop.OR)
  | .AND rd rs1 rs2, ast => ast = .RTYPE (rs2, rs1, rd, rop.AND)
  | .ANDN rd rs1 rs2, ast => ast = .ZBB_RTYPE (rs2, rs1, rd, brop_zbb.ANDN)
  | .FENCE, ast => ∃ fm pred succ rs1 rd, ast = .FENCE (fm, pred, succ, rs1, rd)
  | .ECALL, ast => ast = .ECALL ()
  | .EBREAK, ast => ast = .EBREAK ()
  | .LWU rd rs1 imm, ast => ast = .LOAD (imm, rs1, rd, true, 4)
  | .LD rd rs1 imm, ast => ast = .LOAD (imm, rs1, rd, false, 8)
  | .ADDIW rd rs1 imm, ast => ast = .ADDIW (imm, rs1, rd)
  | .SLLIW rd rs1 shamt, ast => ast = .SHIFTIWOP (shamt, rs1, rd, sopw.SLLIW)
  | .SRLIW rd rs1 shamt, ast => ast = .SHIFTIWOP (shamt, rs1, rd, sopw.SRLIW)
  | .SRAIW rd rs1 shamt, ast => ast = .SHIFTIWOP (shamt, rs1, rd, sopw.SRAIW)
  | .ADDW rd rs1 rs2, ast => ast = .RTYPEW (rs2, rs1, rd, ropw.ADDW)
  | .SUBW rd rs1 rs2, ast => ast = .RTYPEW (rs2, rs1, rd, ropw.SUBW)
  | .SLLW rd rs1 rs2, ast => ast = .RTYPEW (rs2, rs1, rd, ropw.SLLW)
  | .SRLW rd rs1 rs2, ast => ast = .RTYPEW (rs2, rs1, rd, ropw.SRLW)
  | .SRAW rd rs1 rs2, ast => ast = .RTYPEW (rs2, rs1, rd, ropw.SRAW)
  | .MUL rd rs1 rs2, ast => ast = .MUL (rs2, rs1, rd, Natives.sailMulOp)
  | .MULH rd rs1 rs2, ast => ast = .MUL (rs2, rs1, rd, mulhOp)
  | .MULHU rd rs1 rs2, ast => ast = .MUL (rs2, rs1, rd, Natives.sailMulhuOp)
  | .MULHSU rd rs1 rs2, ast => ast = .MUL (rs2, rs1, rd, mulhsuOp)
  | .DIV rd rs1 rs2 _, ast => ast = .DIV (rs2, rs1, rd, false)
  | .DIVU rd rs1 rs2 _, ast => ast = .DIV (rs2, rs1, rd, true)
  | .REM rd rs1 rs2 _, ast => ast = .REM (rs2, rs1, rd, false)
  | .REMU rd rs1 rs2 _, ast => ast = .REM (rs2, rs1, rd, true)
  | .MULW rd rs1 rs2, ast => ast = .MULW (rs2, rs1, rd)
  | .DIVW rd rs1 rs2 _, ast => ast = .DIVW (rs2, rs1, rd, false)
  | .DIVUW rd rs1 rs2 _, ast => ast = .DIVW (rs2, rs1, rd, true)
  | .REMW rd rs1 rs2 _, ast => ast = .REMW (rs2, rs1, rd, false)
  | .REMUW rd rs1 rs2 _, ast => ast = .REMW (rs2, rs1, rd, true)
  | .LR_W rd rs1 aq rl, ast => ast = .LOADRES (aq, rl, rs1, 4, rd)
  | .SC_W rd rs1 rs2 aq rl, ast => ast = .STORECON (aq, rl, rs2, rs1, 4, rd)
  | .SB rs2 rs1 imm, ast => ast = .STORE (imm, rs2, rs1, 1)
  | .SH rs2 rs1 imm, ast => ast = .STORE (imm, rs2, rs1, 2)
  | .SW rs2 rs1 imm, ast => ast = .STORE (imm, rs2, rs1, 4)
  | .SD rs2 rs1 imm, ast => ast = .STORE (imm, rs2, rs1, 8)
  | .AMOSWAP_W rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOSWAP, aq, rl, rs2, rs1, 4, rd)
  | .AMOADD_W rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOADD, aq, rl, rs2, rs1, 4, rd)
  | .AMOXOR_W rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOXOR, aq, rl, rs2, rs1, 4, rd)
  | .AMOAND_W rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOAND, aq, rl, rs2, rs1, 4, rd)
  | .AMOOR_W rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOOR, aq, rl, rs2, rs1, 4, rd)
  | .AMOMIN_W rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOMIN, aq, rl, rs2, rs1, 4, rd)
  | .AMOMAX_W rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOMAX, aq, rl, rs2, rs1, 4, rd)
  | .AMOMINU_W rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOMINU, aq, rl, rs2, rs1, 4, rd)
  | .AMOMAXU_W rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOMAXU, aq, rl, rs2, rs1, 4, rd)
  | .LR_D rd rs1 aq rl, ast => ast = .LOADRES (aq, rl, rs1, 8, rd)
  | .SC_D rd rs1 rs2 aq rl, ast => ast = .STORECON (aq, rl, rs2, rs1, 8, rd)
  | .AMOSWAP_D rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOSWAP, aq, rl, rs2, rs1, 8, rd)
  | .AMOADD_D rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOADD, aq, rl, rs2, rs1, 8, rd)
  | .AMOXOR_D rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOXOR, aq, rl, rs2, rs1, 8, rd)
  | .AMOAND_D rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOAND, aq, rl, rs2, rs1, 8, rd)
  | .AMOOR_D rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOOR, aq, rl, rs2, rs1, 8, rd)
  | .AMOMIN_D rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOMIN, aq, rl, rs2, rs1, 8, rd)
  | .AMOMAX_D rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOMAX, aq, rl, rs2, rs1, 8, rd)
  | .AMOMINU_D rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOMINU, aq, rl, rs2, rs1, 8, rd)
  | .AMOMAXU_D rd rs1 rs2 aq rl, ast => ast = .AMO (amoop.AMOMAXU, aq, rl, rs2, rs1, 8, rd)
  | .CSRRW rd csr rs1, ast => ast = .CSRReg ((JoltISA.SystemCSR.address csr), rs1, rd, csrop.CSRRW)
  | .CSRRS rd csr rs1, ast => ast = .CSRReg ((JoltISA.SystemCSR.address csr), rs1, rd, csrop.CSRRS)
  | .CSRRC rd csr rs1, ast => ast = .CSRReg ((JoltISA.SystemCSR.address csr), rs1, rd, csrop.CSRRC)
  | .CSRRWI rd csr uimm, ast => ast = .CSRImm ((JoltISA.SystemCSR.address csr), uimm, rd, csrop.CSRRW)
  | .CSRRSI rd csr uimm, ast => ast = .CSRImm ((JoltISA.SystemCSR.address csr), uimm, rd, csrop.CSRRS)
  | .CSRRCI rd csr uimm, ast => ast = .CSRImm ((JoltISA.SystemCSR.address csr), uimm, rd, csrop.CSRRC)
  | .MRET, ast => ast = .MRET ()

/-- The instructions whose equivalence theorem this file lifts.
ECALL needs a non-retiring trap step, and the whole-run theorem stops before
the first EBREAK, as described in section 4 of `docs/riscv-alignment.md`.
For example, ADD, MRET and CSRRWI are lifted. -/
def Lifted : RiscvInstruction → Prop
  | .ECALL | .EBREAK => False
  | _ => True

/-- The advice operands of the division and remainder expansions are the
honest values. The soundness half of those theorems shows a retiring run with
`rd ≠ 0` has no other choice. Every other instruction has no advice. -/
def AdviceHonest : (i : RiscvInstruction) → (js : SailJoltState) → equivAssumptions i js → Prop
  | .DIV _ rs1 rs2 quotient, js, h => quotient = sail_div_value (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs1_val (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs2_val false
  | .DIVU _ rs1 rs2 quotient, js, h => quotient = sail_div_value (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs1_val (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs2_val true
  | .REM _ rs1 rs2 quotientMagnitude, js, h => quotientMagnitude = rem_advice_value (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs1_val (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs2_val
  | .REMU _ rs1 rs2 quotient, js, h => quotient = sail_div_value (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs1_val (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs2_val true
  | .DIVW _ rs1 rs2 quotient, js, h => quotient = divw_advice_value (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs1_val (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs2_val
  | .DIVUW _ rs1 rs2 quotient, js, h => quotient = sail_divuw_advice (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs1_val (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs2_val
  | .REMW _ rs1 rs2 quotientMagnitude, js, h => quotientMagnitude = remw_advice_value (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs1_val (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs2_val
  | .REMUW _ rs1 rs2 quotient, js, h => quotient = sail_divuw_advice (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs1_val (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js).rs2_val
  | _, _, _ => True

/-- **Every lifted instruction theorem, against `execute`.** For each wired
instruction, the Jolt rows projected through the CSR overlay agree with Sail's
`execute` of the matching instruction, on the projected state. This is the
`hprog` hypothesis of `Step.joltStep_base`. -/
theorem joltRun_eq_execute :
    (i : RiscvInstruction) → i.Lifted → (ast : instruction) → Matches i ast →
    (js : SailJoltState) → (h : equivAssumptions i js) → AdviceHonest i js h →
    System.systemProjectResult (joltRun i js) = execute ast (System.systemProject js)
  | .LUI rd imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.luiInstr_eq_sail imm rd js h
  | .AUIPC rd imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.auipcInstr_eq_sail imm rd js h
  | .JAL rd imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.jalInstr_eq_sail imm rd js h
  | .JALR rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.jalrInstr_eq_sail imm rs1 rd js h
  | .BEQ rs1 rs2 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.beqInstr_eq_sail imm rs2 rs1 js h
  | .BNE rs1 rs2 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.bneInstr_eq_sail imm rs2 rs1 js h
  | .BLT rs1 rs2 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.bltInstr_eq_sail imm rs2 rs1 js h
  | .BGE rs1 rs2 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.bgeInstr_eq_sail imm rs2 rs1 js h
  | .BLTU rs1 rs2 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.bltuInstr_eq_sail imm rs2 rs1 js h
  | .BGEU rs1 rs2 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.bgeuInstr_eq_sail imm rs2 rs1 js h
  | .LB rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact LB_main.lbProgram_eq_sail imm rs1 rd js h
  | .LH rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact LH_main.lhProgram_eq_sail imm rs1 rd js h
  | .LW rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact LW_main.lwProgram_eq_sail imm rs1 rd js h
  | .LBU rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact LBU_main.lbuProgram_eq_sail imm rs1 rd js h
  | .LHU rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact LHU_main.lhuProgram_eq_sail imm rs1 rd js h
  | .ADDI rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.addiInstr_eq_sail imm rs1 rd js h
  | .SLTI rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.sltiInstr_eq_sail imm rs1 rd js h
  | .SLTIU rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.sltiuInstr_eq_sail imm rs1 rd js h
  | .XORI rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.xoriInstr_eq_sail imm rs1 rd js h
  | .ORI rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.oriInstr_eq_sail imm rs1 rd js h
  | .ANDI rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.andiInstr_eq_sail imm rs1 rd js h
  | .SLLI rd rs1 shamt, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact slliProgram_eq_sail shamt rs1 rd js h
  | .SRLI rd rs1 shamt, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact srliProgram_eq_sail shamt rs1 rd js h
  | .SRAI rd rs1 shamt, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact sraiProgram_eq_sail shamt rs1 rd js h
  | .ADD rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.addInstr_eq_sail rs2 rs1 rd js h
  | .SUB rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.subInstr_eq_sail rs2 rs1 rd js h
  | .SLL rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact sllProgram_eq_sail rs2 rs1 rd js h
  | .SLT rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.sltInstr_eq_sail rs2 rs1 rd js h
  | .SLTU rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.sltuInstr_eq_sail rs2 rs1 rd js h
  | .XOR rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.xorInstr_eq_sail rs2 rs1 rd js h
  | .SRL rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact srlProgram_eq_sail rs2 rs1 rd js h
  | .SRA rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact sraProgram_eq_sail rs2 rs1 rd js h
  | .OR rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.orInstr_eq_sail rs2 rs1 rd js h
  | .AND rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.andInstr_eq_sail rs2 rs1 rd js h
  | .ANDN rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.andnInstr_eq_sail rs2 rs1 rd js h
  | .FENCE, _, ast, hm, js, h, _ => by
      obtain ⟨fm, pred, succ, rs1, rd, rfl⟩ := hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (Natives.fenceInstr_eq_sail js h) fm pred succ rs1 rd
  | .ECALL, hi, _, _, _, _, _ => hi.elim
  | .EBREAK, hi, _, _, _, _, _ => hi.elim
  | .LWU rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact LWU_main.lwuProgram_eq_sail imm rs1 rd js h
  | .LD rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.ldInstr_eq_sail imm rs1 rd js h
  | .ADDIW rd rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.addiwInstr_eq_sail imm rs1 rd js h
  | .SLLIW rd rs1 shamt, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact slliwProgram_eq_sail shamt rs1 rd js h
  | .SRLIW rd rs1 shamt, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact srliwProgram_eq_sail shamt rs1 rd js h
  | .SRAIW rd rs1 shamt, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact sraiwProgram_eq_sail shamt rs1 rd js h
  | .ADDW rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.addwInstr_eq_sail rs2 rs1 rd js h
  | .SUBW rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.subwInstr_eq_sail rs2 rs1 rd js h
  | .SLLW rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact sllwProgram_eq_sail rs2 rs1 rd js h
  | .SRLW rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact srlwProgram_eq_sail rs2 rs1 rd js h
  | .SRAW rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact srawProgram_eq_sail rs2 rs1 rd js h
  | .MUL rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.mulInstr_eq_sail rs2 rs1 rd js h
  | .MULH rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact mulhProgram_eq_sail rs2 rs1 rd js h
  | .MULHU rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.mulhuInstr_eq_sail rs2 rs1 rd js h
  | .MULHSU rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact mulhsuProgram_eq_sail rs2 rs1 rd js h
  | .DIV rd rs1 rs2 quotient, _, ast, hm, js, h, hadv => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (divProgram_eq_sail rs2 rs1 rd quotient js h).1 hadv
  | .DIVU rd rs1 rs2 quotient, _, ast, hm, js, h, hadv => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (divuProgram_eq_sail rs2 rs1 rd quotient js h).1 hadv
  | .REM rd rs1 rs2 quotientMagnitude, _, ast, hm, js, h, hadv => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (remProgram_eq_sail rs2 rs1 rd quotientMagnitude js h).1 hadv
  | .REMU rd rs1 rs2 quotient, _, ast, hm, js, h, hadv => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (remuProgram_eq_sail rs2 rs1 rd quotient js h).1 hadv
  | .MULW rd rs1 rs2, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.mulwInstr_eq_sail rs2 rs1 rd js h
  | .DIVW rd rs1 rs2 quotient, _, ast, hm, js, h, hadv => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (divwProgram_eq_sail rs2 rs1 rd quotient js h).1 hadv
  | .DIVUW rd rs1 rs2 quotient, _, ast, hm, js, h, hadv => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (divuwProgram_eq_sail rs2 rs1 rd quotient js h).1 hadv
  | .REMW rd rs1 rs2 quotientMagnitude, _, ast, hm, js, h, hadv => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (remwProgram_eq_sail rs2 rs1 rd quotientMagnitude js h).1 hadv
  | .REMUW rd rs1 rs2 quotient, _, ast, hm, js, h, hadv => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (remuwProgram_eq_sail rs2 rs1 rd quotient js h).1 hadv
  | .LR_W rd rs1 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      exact SystemProofs.lrRows_eq_execute false aq rl rd rs1 js h
  | .SC_W rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      exact SystemProofs.scRows_eq_execute false aq rl rd rs1 rs2 js h
  | .SB rs2 rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact SB_main.sbProgram_eq_sail imm rs2 rs1 js h
  | .SH rs2 rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact SH_main.shProgram_eq_sail imm rs2 rs1 js h
  | .SW rs2 rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact SW_main.swProgram_eq_sail imm rs2 rs1 js h
  | .SD rs2 rs1 imm, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact Natives.sdInstr_eq_sail imm rs2 rs1 js h
  | .AMOSWAP_W rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amoswapwProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOSWAP aq rl rs2 rs1 4 rd).symm js.sail)
  | .AMOADD_W rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amoaddwProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOADD aq rl rs2 rs1 4 rd).symm js.sail)
  | .AMOXOR_W rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amoxorwProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOXOR aq rl rs2 rs1 4 rd).symm js.sail)
  | .AMOAND_W rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amoandwProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOAND aq rl rs2 rs1 4 rd).symm js.sail)
  | .AMOOR_W rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amoorwProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOOR aq rl rs2 rs1 4 rd).symm js.sail)
  | .AMOMIN_W rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amominwProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOMIN aq rl rs2 rs1 4 rd).symm js.sail)
  | .AMOMAX_W rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amomaxwProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOMAX aq rl rs2 rs1 4 rd).symm js.sail)
  | .AMOMINU_W rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amominuwProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOMINU aq rl rs2 rs1 4 rd).symm js.sail)
  | .AMOMAXU_W rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amomaxuwProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOMAXU aq rl rs2 rs1 4 rd).symm js.sail)
  | .LR_D rd rs1 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      exact SystemProofs.lrRows_eq_execute true aq rl rd rs1 js h
  | .SC_D rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      exact SystemProofs.scRows_eq_execute true aq rl rd rs1 rs2 js h
  | .AMOSWAP_D rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amoswapdProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOSWAP aq rl rs2 rs1 8 rd).symm js.sail)
  | .AMOADD_D rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amoadddProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOADD aq rl rs2 rs1 8 rd).symm js.sail)
  | .AMOXOR_D rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amoxordProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOXOR aq rl rs2 rs1 8 rd).symm js.sail)
  | .AMOAND_D rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amoanddProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOAND aq rl rs2 rs1 8 rd).symm js.sail)
  | .AMOOR_D rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amoordProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOOR aq rl rs2 rs1 8 rd).symm js.sail)
  | .AMOMIN_D rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amomindProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOMIN aq rl rs2 rs1 8 rd).symm js.sail)
  | .AMOMAX_D rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amomaxdProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOMAX aq rl rs2 rs1 8 rd).symm js.sail)
  | .AMOMINU_D rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amominudProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOMINU aq rl rs2 rs1 8 rd).symm js.sail)
  | .AMOMAXU_D rd rs1 rs2 aq rl, _, ast, hm, js, h, _ => by
      subst hm
      have hl : LinkedCSRs js := by unfold equivAssumptions at h; exact h.linkedCSRs
      rw [Projection.systemProject_eq_sail_of_compatible js hl]
      exact (AtomicFamily.amomaxudProgram_eq_sail rs2 rs1 rd js h).trans (congrFun (Step.execute_AMO_flags amoop.AMOMAXU aq rl rs2 rs1 8 rd).symm js.sail)
  | .CSRRW rd csr rs1, _, ast, hm, js, h, _ => by
      subst hm
      exact SystemProofs.csrrwProgram_eq_execute csr rs1 rd js h.rs1_val h.invariant
        h.linkedCSRs h.rs1_read h.mstatus_bits h.mtvec_mode h.mepc_align
  | .CSRRS rd csr rs1, _, ast, hm, js, h, _ => by
      subst hm
      exact SystemProofs.csrBitUpdateProgram_eq_execute false csr rs1 rd js h.rs1_val
        h.invariant h.linkedCSRs h.rs1_read h.mstatus_bits h.mtvec_mode h.mepc_align
  | .CSRRC rd csr rs1, _, ast, hm, js, h, _ => by
      subst hm
      exact SystemProofs.csrBitUpdateProgram_eq_execute true csr rs1 rd js h.rs1_val
        h.invariant h.linkedCSRs h.rs1_read h.mstatus_bits h.mtvec_mode h.mepc_align
  | .CSRRWI rd csr imm, _, ast, hm, js, h, _ => by
      subst hm
      exact SystemProofs.csrrwiProgram_eq_execute csr imm rd js h.invariant
        h.mstatus_bits h.mtvec_mode h.mepc_align
  | .CSRRSI rd csr imm, _, ast, hm, js, h, _ => by
      subst hm
      exact SystemProofs.csrImmediateBitUpdateProgram_eq_execute false csr imm rd js h.invariant
        h.mstatus_bits h.mtvec_mode h.mepc_align
  | .CSRRCI rd csr imm, _, ast, hm, js, h, _ => by
      subst hm
      exact SystemProofs.csrImmediateBitUpdateProgram_eq_execute true csr imm rd js h.invariant
        h.mstatus_bits h.mtvec_mode h.mepc_align
  | .MRET, _, ast, hm, js, h, _ => by
      subst hm
      exact SystemProofs.mretProgram_eq_execute js h.invariant h.mstatus_bits h.mepc_align

/-- **One Sail step per lifted instruction, 32-bit encodings.** If Sail fetches
and decodes `ast` from the projected state, `i` stands for `ast`, the
instruction's assumptions hold after the step prelude, and `ast` retires, then
the Jolt step running `i`'s rows agrees with `try_step`. -/
theorem joltStep_eq_try_step_base (n : Nat) (i : RiscvInstruction) (hi : i.Lifted)
    (js : SailJoltState) (hinv : Step.StepInvariant (System.systemProject js))
    (inc : Bool) (hinc : should_inc_minstret Privilege.Machine js.sail = .ok inc js.sail)
    (pc : BitVec 64) (hpc : js.sail.regs.get? Register.PC = some pc)
    (w : BitVec 32) (ast : instruction) (hm : Matches i ast)
    (hfetch : fetch () (Step.setReg (System.systemProject js) Register.minstret_increment inc) =
      .ok (.F_Base w) (Step.setReg (System.systemProject js) Register.minstret_increment inc))
    (hdec : ext_decode w (Step.setReg (System.systemProject js) Register.minstret_increment inc) =
      .ok ast (Step.setReg (System.systemProject js) Register.minstret_increment inc))
    (h : equivAssumptions i (Step.preludeJolt js inc pc 4))
    (hadv : AdviceHonest i (Step.preludeJolt js inc pc 4) h)
    (hretire : ∀ r s', execute ast (System.systemProject (Step.preludeJolt js inc pc 4)) =
      .ok r s' → r = RETIRE_SUCCESS) :
    System.systemProjectResult (Step.joltStep 4 (zero_extend (m := 32) w) (joltRun i) js) =
      try_step n false (System.systemProject js) :=
  Step.joltStep_base n js hinv inc hinc pc hpc w ast hfetch hdec (joltRun i)
    (joltRun_eq_execute i hi ast hm _ h hadv) hretire

/-- **One Sail step per lifted instruction, compressed encodings.** As
`joltStep_eq_try_step_base`, for a 16-bit parcel that Sail decodes to the
compressed AST `cast`, which runs as the base AST `base` that `i` stands for. -/
theorem joltStep_eq_try_step_compressed (n : Nat) (i : RiscvInstruction) (hi : i.Lifted)
    (js : SailJoltState) (hinv : Step.StepInvariant (System.systemProject js))
    (inc : Bool) (hinc : should_inc_minstret Privilege.Machine js.sail = .ok inc js.sail)
    (pc : BitVec 64) (hpc : js.sail.regs.get? Register.PC = some pc)
    (c : BitVec 16) (cast base : instruction) (hm : Matches i base)
    (hfetch : fetch () (Step.setReg (System.systemProject js) Register.minstret_increment inc) =
      .ok (.F_RVC c) (Step.setReg (System.systemProject js) Register.minstret_increment inc))
    (hdec : ext_decode_compressed c
        (Step.setReg (System.systemProject js) Register.minstret_increment inc) =
      .ok cast (Step.setReg (System.systemProject js) Register.minstret_increment inc))
    (hexec : ∀ s', Step.StepInvariant s' → Step.executeFull cast s' = Step.executeFull base s')
    (h : equivAssumptions i (Step.preludeJolt js inc pc 2))
    (hadv : AdviceHonest i (Step.preludeJolt js inc pc 2) h)
    (hretire : ∀ r s', execute base (System.systemProject (Step.preludeJolt js inc pc 2)) =
      .ok r s' → r = RETIRE_SUCCESS) :
    System.systemProjectResult (Step.joltStep 2 (zero_extend (m := 32) c) (joltRun i) js) =
      try_step n false (System.systemProject js) :=
  Step.joltStep_compressed n js hinv inc hinc pc hpc c cast base hfetch hdec hexec (joltRun i)
    (joltRun_eq_execute i hi base hm _ h hadv) hretire

/-- Every instruction's rows write only `Step.JoltWritable` registers. -/
theorem joltRun_regFrame (i : RiscvInstruction) (js : SailJoltState) :
    Step.RegFrame js (Step.resultState (joltRun i js)) := by
  cases i <;> simp only [joltRun, JoltISA.execLUI] <;> first
    | exact Step.execInstr_regFrame _ js
    | exact Step.execProgram_regFrame _ js

/-- **A lifted instruction's Jolt step preserves the step invariant**, under
the hypotheses of `joltStep_eq_try_step_base`: the instruction's assumptions
after the prelude and a retiring `execute`. -/
theorem joltStep_stepInvariant (len : Int) (bits : BitVec 32) (i : RiscvInstruction)
    (hi : i.Lifted) (js : SailJoltState) (hinv : Step.StepInvariant (System.systemProject js))
    (inc : Bool) (hinc : should_inc_minstret Privilege.Machine js.sail = .ok inc js.sail)
    (pc : BitVec 64) (hpc : js.sail.regs.get? Register.PC = some pc)
    (ast : instruction) (hm : Matches i ast)
    (h : equivAssumptions i (Step.preludeJolt js inc pc len))
    (hadv : AdviceHonest i (Step.preludeJolt js inc pc len) h)
    (hretire : ∀ r s', execute ast (System.systemProject (Step.preludeJolt js inc pc len)) =
      .ok r s' → r = RETIRE_SUCCESS)
    {b : Bool} {js' : SailJoltState} (hrun : Step.joltStep len bits (joltRun i) js = .ok b js') :
    Step.StepInvariant (System.systemProject js') := by
  refine Step.joltStep_stepInvariant len bits (joltRun i) (joltRun_regFrame i) js hinv inc hinc
    pc hpc (fun r js1 hr => ?_) hrun
  have he := joltRun_eq_execute i hi ast hm _ h hadv
  rw [hr] at he
  exact hretire r _ he.symm

end RiscvInstruction
