/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/


import LeanRV64D.InstsEnd
import JoltBytecode.Bundles
import JoltBytecode.JoltISA.Semantics
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Expansions.Atomics
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.JoltISA.Expansions.LoadReserved
import JoltBytecode.JoltISA.Expansions.Mul
import JoltBytecode.JoltISA.Expansions.Store
import JoltBytecode.JoltISA.Expansions.System
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Sll
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Sllw
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Sra
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Sraw
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Srl
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Rtype.Srlw
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Itype.Slli
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Itype.Slliw
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Itype.Srai
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Itype.Sraiw
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Itype.Srli
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Itype.Srliw
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Mult.Mulh
import JoltBytecode.InstructionEquivalence.Instructions.ALUFamily.Mult.Mulhsu
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Div
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divu
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divuw
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divw
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Rem
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Remu
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Remuw
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Remw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoaddd
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoaddw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoandd
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoandw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomaxd
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomaxud
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomaxuw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomaxw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amomind
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amominud
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amominuw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amominw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoord
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoorw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoswapd
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoswapw
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoxord
import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Amoxorw
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.Sb_main
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.Sh_main
import JoltBytecode.InstructionEquivalence.Instructions.StoreFamily.Sw_main
import JoltBytecode.InstructionEquivalence.Instructions.System.Mret
import JoltBytecode.InstructionEquivalence.Instructions.System.Csrrw
import JoltBytecode.InstructionEquivalence.Instructions.System.Csrrs
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Add
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Addi
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Addiw
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Addw
import JoltBytecode.InstructionEquivalence.Instructions.Natives.And
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Andn
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Andi
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Auipc
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Beq
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Bge
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Bgeu
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Blt
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Bltu
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Bne
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Fence
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Jal
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Jalr
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Ld
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Lui
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Mul
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Mulhu
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Mulw
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Or
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Ori
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Sd
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Slt
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Slti
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Sltiu
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Sltu
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Sub
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Subw
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Xor
import JoltBytecode.InstructionEquivalence.Instructions.Natives.Xori
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LB_main
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LBU_main
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LH_main
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LHU_main
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LW_main
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LWU_main

/-!
# RISC-V Instructions

THis can be thought of as the projects "main" file. 
For every RISC-V instruction, we tell you 
what the equivalence proposition is, what assumptions are needed,
and finally where the proof is.
-/

open Sail PreSail

/-- A CSR address is the 12-bit `csr` field used by Zicsr instructions. -/
abbrev CsrAddr := BitVec 12

/-- Guest RISC-V instruction constructors with operands.

Sources:
* Jolt accepted source instruction list:
  `/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-riscv/src/lib.rs`,
  `for_each_instruction_kind!`.
* Jolt source extension assignment:
  `/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-riscv/src/kind.rs`,
  `source_extension_for_marker`.
* RV32I base integer instructions:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html
* RV64I base integer additions:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/rv64.html
* M extension:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html
* A extension:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/a-st-ext.html
* Zicsr extension:
  https://docs.riscv.org/reference/isa/v20260120/unpriv/zicsr.html
* MRET privileged instruction listing:
  https://docs.riscv.org/reference/isa/v20260120/priv/priv-insns.html
-/
inductive RiscvInstruction where
  /- RV32I base integer instruction set, inherited by RV64I.
     Source: https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html -/
  | LUI (rd : regidx) (imm : BitVec 20)
  | AUIPC (rd : regidx) (imm : BitVec 20)
  | JAL (rd : regidx) (imm : BitVec 21)
  | JALR (rd rs1 : regidx) (imm : BitVec 12)
  | BEQ (rs1 rs2 : regidx) (imm : BitVec 13)
  | BNE (rs1 rs2 : regidx) (imm : BitVec 13)
  | BLT (rs1 rs2 : regidx) (imm : BitVec 13)
  | BGE (rs1 rs2 : regidx) (imm : BitVec 13)
  | BLTU (rs1 rs2 : regidx) (imm : BitVec 13)
  | BGEU (rs1 rs2 : regidx) (imm : BitVec 13)
  | LB (rd rs1 : regidx) (imm : BitVec 12)
  | LH (rd rs1 : regidx) (imm : BitVec 12)
  | LW (rd rs1 : regidx) (imm : BitVec 12)
  | LBU (rd rs1 : regidx) (imm : BitVec 12)
  | LHU (rd rs1 : regidx) (imm : BitVec 12)
  | SB (rs2 rs1 : regidx) (imm : BitVec 12)
  | SH (rs2 rs1 : regidx) (imm : BitVec 12)
  | SW (rs2 rs1 : regidx) (imm : BitVec 12)
  | ADDI (rd rs1 : regidx) (imm : BitVec 12)
  | SLTI (rd rs1 : regidx) (imm : BitVec 12)
  | SLTIU (rd rs1 : regidx) (imm : BitVec 12)
  | XORI (rd rs1 : regidx) (imm : BitVec 12)
  | ORI (rd rs1 : regidx) (imm : BitVec 12)
  | ANDI (rd rs1 : regidx) (imm : BitVec 12)
  | SLLI (rd rs1 : regidx) (shamt : BitVec 6)
  | SRLI (rd rs1 : regidx) (shamt : BitVec 6)
  | SRAI (rd rs1 : regidx) (shamt : BitVec 6)
  | ADD (rd rs1 rs2 : regidx)
  | SUB (rd rs1 rs2 : regidx)
  | SLL (rd rs1 rs2 : regidx)
  | SLT (rd rs1 rs2 : regidx)
  | SLTU (rd rs1 rs2 : regidx)
  | XOR (rd rs1 rs2 : regidx)
  | SRL (rd rs1 rs2 : regidx)
  | SRA (rd rs1 rs2 : regidx)
  | OR (rd rs1 rs2 : regidx)
  | AND (rd rs1 rs2 : regidx)
  | ANDN (rd rs1 rs2 : regidx)
  | FENCE
  | ECALL
  | EBREAK

  /- RV64I base integer additions.
     Source: https://docs.riscv.org/reference/isa/v20260120/unpriv/rv64.html -/
  | LWU (rd rs1 : regidx) (imm : BitVec 12)
  | LD (rd rs1 : regidx) (imm : BitVec 12)
  | SD (rs2 rs1 : regidx) (imm : BitVec 12)
  | ADDIW (rd rs1 : regidx) (imm : BitVec 12)
  | SLLIW (rd rs1 : regidx) (shamt : BitVec 5)
  | SRLIW (rd rs1 : regidx) (shamt : BitVec 5)
  | SRAIW (rd rs1 : regidx) (shamt : BitVec 5)
  | ADDW (rd rs1 rs2 : regidx)
  | SUBW (rd rs1 rs2 : regidx)
  | SLLW (rd rs1 rs2 : regidx)
  | SRLW (rd rs1 rs2 : regidx)
  | SRAW (rd rs1 rs2 : regidx)

  /- M extension for integer multiplication and division.
     Source: https://docs.riscv.org/reference/isa/v20260120/unpriv/m-st-ext.html -/
  | MUL (rd rs1 rs2 : regidx)
  | MULH (rd rs1 rs2 : regidx)
  | MULHU (rd rs1 rs2 : regidx)
  | MULHSU (rd rs1 rs2 : regidx)
  | DIV (rd rs1 rs2 : regidx) (quotient : BitVec 64)
  | DIVU (rd rs1 rs2 : regidx) (quotient : BitVec 64)
  | REM (rd rs1 rs2 : regidx) (quotientMagnitude : BitVec 64)
  | REMU (rd rs1 rs2 : regidx) (quotient : BitVec 64)
  | MULW (rd rs1 rs2 : regidx)
  | DIVW (rd rs1 rs2 : regidx) (quotient : BitVec 64)
  | DIVUW (rd rs1 rs2 : regidx) (quotient : BitVec 64)
  | REMW (rd rs1 rs2 : regidx) (quotientMagnitude : BitVec 64)
  | REMUW (rd rs1 rs2 : regidx) (quotient : BitVec 64)

  /- A extension for atomic instructions. The `aq` and `rl` operands are the
     acquire and release bits in the atomic instruction encoding.
     Source: https://docs.riscv.org/reference/isa/v20260120/unpriv/a-st-ext.html -/
  | LR_W (rd rs1 : regidx) (aq rl : Bool)
  | SC_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOSWAP_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOADD_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOXOR_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOAND_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOOR_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMIN_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMAX_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMINU_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMAXU_W (rd rs1 rs2 : regidx) (aq rl : Bool)
  | LR_D (rd rs1 : regidx) (aq rl : Bool)
  | SC_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOSWAP_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOADD_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOXOR_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOAND_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOOR_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMIN_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMAX_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMINU_D (rd rs1 rs2 : regidx) (aq rl : Bool)
  | AMOMAXU_D (rd rs1 rs2 : regidx) (aq rl : Bool)

  /- Jolt-supported Zicsr source instructions.
     Source: https://docs.riscv.org/reference/isa/v20260120/unpriv/zicsr.html -/
  | CSRRW (rd : regidx) (csr : JoltISA.SystemCSR) (rs1 : regidx)
  | CSRRS (rd : regidx) (csr : JoltISA.SystemCSR) (rs1 : regidx)

  /- Jolt-supported RvPrivileged source instruction.
     Source: https://docs.riscv.org/reference/isa/v20260120/priv/priv-insns.html -/
  | MRET
  deriving Repr

namespace RiscvInstruction

abbrev SailExecution := SailM ExecutionResult

/-- Assumption payload for the equivalence statement.

The advice-backed ALU instructions all need source-register read facts; their
advice operands live in the `RiscvInstruction` constructor itself. -/
def equivAssumptions : (instr : RiscvInstruction) → SailJoltState → Type
  | .LUI _rd _imm, js =>
      NoSourceReadWithLinkedCSRs js
  | .AUIPC _rd _imm, js =>
      AuipcInstrEqSailAssumptions js
  | .JAL _rd imm, js =>
      JalInstrEqSailAssumptions imm js
  | .JALR _rd rs1 imm, js =>
      JalrInstrEqSailAssumptions imm rs1 js
  | .BEQ rs1 rs2 _imm, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .BNE rs1 rs2 _imm, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .BLT rs1 rs2 _imm, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .BGE rs1 rs2 _imm, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .BLTU rs1 rs2 _imm, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .BGEU rs1 rs2 _imm, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .FENCE, js =>
      FenceProgramEqSailAssumptions js
  | .LB _rd rs1 imm, js =>
      LoadProgramEqSailAssumptions imm rs1 js
  | .LH _rd rs1 imm, js =>
      LoadProgramEqSailAssumptions imm rs1 js
  | .LW _rd rs1 imm, js =>
      LoadProgramEqSailAssumptions imm rs1 js
  | .LBU _rd rs1 imm, js =>
      LoadProgramEqSailAssumptions imm rs1 js
  | .LHU _rd rs1 imm, js =>
      LoadProgramEqSailAssumptions imm rs1 js
  | .LWU _rd rs1 imm, js =>
      LoadProgramEqSailAssumptions imm rs1 js
  | .SLLI _rd rs1 _shamt, js =>
      UnarySourceReadWithLinkedCSRs rs1 js
  | .SRLI _rd rs1 _shamt, js =>
      UnarySourceReadWithLinkedCSRs rs1 js
  | .SRAI _rd rs1 _shamt, js =>
      UnarySourceReadWithLinkedCSRs rs1 js
  | .ADDI _rd rs1 _imm, js =>
      UnarySourceReadWithLinkedCSRs rs1 js
  | .SLTI _rd rs1 _imm, js =>
      UnarySourceReadWithLinkedCSRs rs1 js
  | .SLTIU _rd rs1 _imm, js =>
      UnarySourceReadWithLinkedCSRs rs1 js
  | .XORI _rd rs1 _imm, js =>
      UnarySourceReadWithLinkedCSRs rs1 js
  | .ORI _rd rs1 _imm, js =>
      UnarySourceReadWithLinkedCSRs rs1 js
  | .ANDI _rd rs1 _imm, js =>
      UnarySourceReadWithLinkedCSRs rs1 js
  | .ADD _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .SUB _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .SLT _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .SLTU _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .XOR _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .OR _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .AND _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .ANDN _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .SLL _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .SRL _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .SRA _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .ADDIW _rd rs1 _imm, js =>
      UnarySourceReadWithLinkedCSRs rs1 js
  | .SLLIW _rd rs1 _shamt, js =>
      UnarySourceReadWithLinkedCSRs rs1 js
  | .SRLIW _rd rs1 _shamt, js =>
      UnarySourceReadWithLinkedCSRs rs1 js
  | .SRAIW _rd rs1 _shamt, js =>
      UnarySourceReadWithLinkedCSRs rs1 js
  | .ADDW _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .SUBW _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .SLLW _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .SRLW _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .SRAW _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .MULH _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .MULHSU _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .MULW _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .DIV _rd rs1 rs2 _quotient, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .DIVU _rd rs1 rs2 _quotient, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .REM _rd rs1 rs2 _quotientMagnitude, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .REMU _rd rs1 rs2 _quotient, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .DIVW _rd rs1 rs2 _quotient, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .DIVUW _rd rs1 rs2 _quotient, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .REMW _rd rs1 rs2 _quotientMagnitude, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .REMUW _rd rs1 rs2 _quotient, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .LD _rd rs1 imm, js =>
      LoadProgramEqSailAssumptions imm rs1 js
  | .SB rs2 rs1 imm, js =>
      StoreProgramEqSailAssumptions imm rs2 rs1 js
  | .SH rs2 rs1 imm, js =>
      StoreProgramEqSailAssumptions imm rs2 rs1 js
  | .SW rs2 rs1 imm, js =>
      StoreProgramEqSailAssumptions imm rs2 rs1 js
  | .SD rs2 rs1 imm, js =>
      StoreProgramEqSailAssumptions imm rs2 rs1 js
  | .MUL _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .MULHU _rd rs1 rs2, js =>
      BinarySourceReadWithLinkedCSRs rs2 rs1 js
  | .AMOSWAP_W rd rs1 rs2 _aq _rl, js =>
      AmoWordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js
  | .AMOADD_W rd rs1 rs2 _aq _rl, js =>
      AmoWordProgramEqSailAssumptions amoop.AMOADD rs2 rs1 rd js
  | .AMOXOR_W rd rs1 rs2 _aq _rl, js =>
      AmoWordProgramEqSailAssumptions amoop.AMOXOR rs2 rs1 rd js
  | .AMOAND_W rd rs1 rs2 _aq _rl, js =>
      AmoWordProgramEqSailAssumptions amoop.AMOAND rs2 rs1 rd js
  | .AMOOR_W rd rs1 rs2 _aq _rl, js =>
      AmoWordProgramEqSailAssumptions amoop.AMOOR rs2 rs1 rd js
  | .AMOMIN_W rd rs1 rs2 _aq _rl, js =>
      AmoWordProgramEqSailAssumptions amoop.AMOMIN rs2 rs1 rd js
  | .AMOMAX_W rd rs1 rs2 _aq _rl, js =>
      AmoWordProgramEqSailAssumptions amoop.AMOMAX rs2 rs1 rd js
  | .AMOMINU_W rd rs1 rs2 _aq _rl, js =>
      AmoWordProgramEqSailAssumptions amoop.AMOMINU rs2 rs1 rd js
  | .AMOMAXU_W rd rs1 rs2 _aq _rl, js =>
      AmoWordProgramEqSailAssumptions amoop.AMOMAXU rs2 rs1 rd js
  | .AMOSWAP_D rd rs1 rs2 _aq _rl, js =>
      AmoDwordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js
  | .AMOADD_D rd rs1 rs2 _aq _rl, js =>
      AmoDwordProgramEqSailAssumptions amoop.AMOADD rs2 rs1 rd js
  | .AMOXOR_D rd rs1 rs2 _aq _rl, js =>
      AmoDwordProgramEqSailAssumptions amoop.AMOXOR rs2 rs1 rd js
  | .AMOAND_D rd rs1 rs2 _aq _rl, js =>
      AmoDwordProgramEqSailAssumptions amoop.AMOAND rs2 rs1 rd js
  | .AMOOR_D rd rs1 rs2 _aq _rl, js =>
      AmoDwordProgramEqSailAssumptions amoop.AMOOR rs2 rs1 rd js
  | .AMOMIN_D rd rs1 rs2 _aq _rl, js =>
      AmoDwordProgramEqSailAssumptions amoop.AMOMIN rs2 rs1 rd js
  | .AMOMAX_D rd rs1 rs2 _aq _rl, js =>
      AmoDwordProgramEqSailAssumptions amoop.AMOMAX rs2 rs1 rd js
  | .AMOMINU_D rd rs1 rs2 _aq _rl, js =>
      AmoDwordProgramEqSailAssumptions amoop.AMOMINU rs2 rs1 rd js
  | .AMOMAXU_D rd rs1 rs2 _aq _rl, js =>
      AmoDwordProgramEqSailAssumptions amoop.AMOMAXU rs2 rs1 rd js
  | .CSRRW rd csr rs1, js =>
      System.CsrrwSystemAssumptions js csr rs1 rd
  | .CSRRS rd csr rs1, js =>
      System.CsrrsSystemAssumptions js csr rs1 rd
  | .MRET, js =>
      System.MretProgramEqSailAssumptions js
  | _, _ => Unit

/-- Given RISC-V instruction and assumptions return the proposition that we prove-/
def equivalenceStatement :
    (instr : RiscvInstruction) →
    (js : SailJoltState) →
    equivAssumptions instr js →
    Prop
  | instr, js, _h =>
    match instr with
    | .LUI rd imm =>
      Natives.luiInstrEqSailStatement imm rd js _h
    | .AUIPC rd imm =>
      Natives.auipcInstrEqSailStatement imm rd js _h
    | .JAL rd imm =>
      Natives.jalInstrEqSailStatement imm rd js _h
    | .JALR rd rs1 imm =>
      Natives.jalrInstrEqSailStatement imm rs1 rd js _h
    | .BEQ rs1 rs2 imm =>
      Natives.beqInstrEqSailStatement imm rs2 rs1 js _h
    | .BNE rs1 rs2 imm =>
      Natives.bneInstrEqSailStatement imm rs2 rs1 js _h
    | .BLT rs1 rs2 imm =>
      Natives.bltInstrEqSailStatement imm rs2 rs1 js _h
    | .BGE rs1 rs2 imm =>
      Natives.bgeInstrEqSailStatement imm rs2 rs1 js _h
    | .BLTU rs1 rs2 imm =>
      Natives.bltuInstrEqSailStatement imm rs2 rs1 js _h
    | .BGEU rs1 rs2 imm =>
      Natives.bgeuInstrEqSailStatement imm rs2 rs1 js _h
    | .LB rd rs1 imm =>
      LB_main.lbProgramEqSailStatement imm rs1 rd js _h
    | .LH rd rs1 imm =>
      LH_main.lhProgramEqSailStatement imm rs1 rd js _h
    | .LW rd rs1 imm =>
      LW_main.lwProgramEqSailStatement imm rs1 rd js _h
    | .LBU rd rs1 imm =>
      LBU_main.lbuProgramEqSailStatement imm rs1 rd js _h
    | .LHU rd rs1 imm =>
      LHU_main.lhuProgramEqSailStatement imm rs1 rd js _h
    | .ADDI rd rs1 imm =>
      Natives.addiInstrEqSailStatement imm rs1 rd js _h
    | .SLTI rd rs1 imm =>
      Natives.sltiInstrEqSailStatement imm rs1 rd js _h
    | .SLTIU rd rs1 imm =>
      Natives.sltiuInstrEqSailStatement imm rs1 rd js _h
    | .XORI rd rs1 imm =>
      Natives.xoriInstrEqSailStatement imm rs1 rd js _h
    | .ORI rd rs1 imm =>
      Natives.oriInstrEqSailStatement imm rs1 rd js _h
    | .ANDI rd rs1 imm =>
      Natives.andiInstrEqSailStatement imm rs1 rd js _h
    | .SLLI rd rs1 shamt =>
      slliProgramEqSailStatement shamt rs1 rd js _h
    | .SRLI rd rs1 shamt =>
      srliProgramEqSailStatement shamt rs1 rd js _h
    | .SRAI rd rs1 shamt =>
      sraiProgramEqSailStatement shamt rs1 rd js _h
    | .ADD rd rs1 rs2 =>
      Natives.addInstrEqSailStatement rs2 rs1 rd js _h
    | .SUB rd rs1 rs2 =>
      Natives.subInstrEqSailStatement rs2 rs1 rd js _h
    | .SLL rd rs1 rs2 =>
      sllProgramEqSailStatement rs2 rs1 rd js _h
    | .SLT rd rs1 rs2 =>
      Natives.sltInstrEqSailStatement rs2 rs1 rd js _h
    | .SLTU rd rs1 rs2 =>
      Natives.sltuInstrEqSailStatement rs2 rs1 rd js _h
    | .XOR rd rs1 rs2 =>
      Natives.xorInstrEqSailStatement rs2 rs1 rd js _h
    | .SRL rd rs1 rs2 =>
      srlProgramEqSailStatement rs2 rs1 rd js _h
    | .SRA rd rs1 rs2 =>
      sraProgramEqSailStatement rs2 rs1 rd js _h
    | .OR rd rs1 rs2 =>
      Natives.orInstrEqSailStatement rs2 rs1 rd js _h
    | .AND rd rs1 rs2 =>
      Natives.andInstrEqSailStatement rs2 rs1 rd js _h
    | .ANDN rd rs1 rs2 =>
      Natives.andnInstrEqSailStatement rs2 rs1 rd js _h
    | .FENCE =>
      Natives.fenceInstrEqSailStatement js _h
    | .ECALL =>
      False -- WARNING: unwired instruction equivalence
    | .EBREAK =>
      False -- WARNING: unwired instruction equivalence
    | .LWU rd rs1 imm =>
      LWU_main.lwuProgramEqSailStatement imm rs1 rd js _h
    | .LD rd rs1 imm =>
      Natives.ldInstrEqSailStatement imm rs1 rd js _h
    | .ADDIW rd rs1 imm =>
      Natives.addiwInstrEqSailStatement imm rs1 rd js _h
    | .SLLIW rd rs1 shamt =>
      slliwProgramEqSailStatement shamt rs1 rd js _h
    | .SRLIW rd rs1 shamt =>
      srliwProgramEqSailStatement shamt rs1 rd js _h
    | .SRAIW rd rs1 shamt =>
      sraiwProgramEqSailStatement shamt rs1 rd js _h
    | .ADDW rd rs1 rs2 =>
      Natives.addwInstrEqSailStatement rs2 rs1 rd js _h
    | .SUBW rd rs1 rs2 =>
      Natives.subwInstrEqSailStatement rs2 rs1 rd js _h
    | .SLLW rd rs1 rs2 =>
      sllwProgramEqSailStatement rs2 rs1 rd js _h
    | .SRLW rd rs1 rs2 =>
      srlwProgramEqSailStatement rs2 rs1 rd js _h
    | .SRAW rd rs1 rs2 =>
      srawProgramEqSailStatement rs2 rs1 rd js _h
    | .MUL rd rs1 rs2 =>
      Natives.mulInstrEqSailStatement rs2 rs1 rd js _h
    | .MULH rd rs1 rs2 =>
      mulhProgramEqSailStatement rs2 rs1 rd js _h
    | .MULHU rd rs1 rs2 =>
      Natives.mulhuInstrEqSailStatement rs2 rs1 rd js _h
    | .MULHSU rd rs1 rs2 =>
      mulhsuProgramEqSailStatement rs2 rs1 rd js _h
    | .DIV rd rs1 rs2 quotient =>
      divProgramEqSailStatement rs2 rs1 rd quotient js _h
    | .DIVU rd rs1 rs2 quotient =>
      divuProgramEqSailStatement rs2 rs1 rd quotient js _h
    | .REM rd rs1 rs2 quotientMagnitude =>
      remProgramEqSailStatement rs2 rs1 rd quotientMagnitude js _h
    | .REMU rd rs1 rs2 quotient =>
      remuProgramEqSailStatement rs2 rs1 rd quotient js _h
    | .MULW rd rs1 rs2 =>
      Natives.mulwInstrEqSailStatement rs2 rs1 rd js _h
    | .DIVW rd rs1 rs2 quotient =>
      divwProgramEqSailStatement rs2 rs1 rd quotient js _h
    | .DIVUW rd rs1 rs2 quotient =>
      divuwProgramEqSailStatement rs2 rs1 rd quotient js _h
    | .REMW rd rs1 rs2 quotientMagnitude =>
      remwProgramEqSailStatement rs2 rs1 rd quotientMagnitude js _h
    | .REMUW rd rs1 rs2 quotient =>
      remuwProgramEqSailStatement rs2 rs1 rd quotient js _h
    | .LR_W _rd _rs1 _aq _rl =>
      False -- WARNING: unwired instruction equivalence
    | .SC_W _rd _rs1 _rs2 _aq _rl =>
      False -- WARNING: unwired instruction equivalence
    | .SB rs2 rs1 imm =>
      SB_main.sbProgramEqSailStatement imm rs2 rs1 js _h
    | .SH rs2 rs1 imm =>
      SH_main.shProgramEqSailStatement imm rs2 rs1 js _h
    | .SW rs2 rs1 imm =>
      SW_main.swProgramEqSailStatement imm rs2 rs1 js _h
    | .SD rs2 rs1 imm =>
      Natives.sdInstrEqSailStatement imm rs2 rs1 js _h
    | .AMOSWAP_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoswapwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOADD_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoaddwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOXOR_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoxorwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOAND_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoandwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOOR_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoorwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMIN_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amominwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMAX_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amomaxwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMINU_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amominuwProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMAXU_W rd rs1 rs2 _aq _rl =>
      AtomicFamily.amomaxuwProgramEqSailStatement rs2 rs1 rd js _h
    | .LR_D _rd _rs1 _aq _rl =>
      False -- WARNING: unwired instruction equivalence
    | .SC_D _rd _rs1 _rs2 _aq _rl =>
      False -- WARNING: unwired instruction equivalence
    | .AMOSWAP_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoswapdProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOADD_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoadddProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOXOR_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoxordProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOAND_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoanddProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOOR_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amoordProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMIN_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amomindProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMAX_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amomaxdProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMINU_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amominudProgramEqSailStatement rs2 rs1 rd js _h
    | .AMOMAXU_D rd rs1 rs2 _aq _rl =>
      AtomicFamily.amomaxudProgramEqSailStatement rs2 rs1 rd js _h
    | .CSRRW rd csr rs1 =>
      System.csrrwProgramEqSailStatement js csr rs1 rd _h
    | .CSRRS rd csr rs1 =>
      System.csrrsProgramEqSailStatement js csr rs1 rd _h
    | .MRET =>
      System.mretProgramEqSailStatement js _h

/-- Given Risc indtruction and equivalence assumptions, 
    give me the proof of the equivalence statement-/
theorem equivalenceStatement_holds :
    (instr : RiscvInstruction) →
    (js : SailJoltState) →
    (h : equivAssumptions instr js) →
    equivalenceStatement instr js h
  | .ADDW rd rs1 rs2, js, h =>
      Natives.addwInstr_eq_sail rs2 rs1 rd js h
  | .DIV rd rs1 rs2 quotient, js, h =>
      divProgram_eq_sail rs2 rs1 rd quotient js h
  | .DIVU rd rs1 rs2 quotient, js, h =>
      divuProgram_eq_sail rs2 rs1 rd quotient js h
  | .REM rd rs1 rs2 quotientMagnitude, js, h =>
      remProgram_eq_sail rs2 rs1 rd quotientMagnitude js h
  | .REMU rd rs1 rs2 quotient, js, h =>
      remuProgram_eq_sail rs2 rs1 rd quotient js h
  | .DIVW rd rs1 rs2 quotient, js, h =>
      divwProgram_eq_sail rs2 rs1 rd quotient js h
  | .DIVUW rd rs1 rs2 quotient, js, h =>
      divuwProgram_eq_sail rs2 rs1 rd quotient js h
  | .REMW rd rs1 rs2 quotientMagnitude, js, h =>
      remwProgram_eq_sail rs2 rs1 rd quotientMagnitude js h
  | .REMUW rd rs1 rs2 quotient, js, h =>
      remuwProgram_eq_sail rs2 rs1 rd quotient js h
  | .LUI rd imm, js, h =>
      Natives.luiInstr_eq_sail imm rd js h
  | .AUIPC rd imm, js, h =>
      Natives.auipcInstr_eq_sail imm rd js h
  | .LB rd rs1 imm, js, h =>
      LB_main.lbProgram_eq_sail imm rs1 rd js h
  | .LH rd rs1 imm, js, h =>
      LH_main.lhProgram_eq_sail imm rs1 rd js h
  | .LW rd rs1 imm, js, h =>
      LW_main.lwProgram_eq_sail imm rs1 rd js h
  | .LBU rd rs1 imm, js, h =>
      LBU_main.lbuProgram_eq_sail imm rs1 rd js h
  | .LHU rd rs1 imm, js, h =>
      LHU_main.lhuProgram_eq_sail imm rs1 rd js h
  | .ADDI rd rs1 imm, js, h =>
      Natives.addiInstr_eq_sail imm rs1 rd js h
  | .SLTI rd rs1 imm, js, h =>
      Natives.sltiInstr_eq_sail imm rs1 rd js h
  | .SLTIU rd rs1 imm, js, h =>
      Natives.sltiuInstr_eq_sail imm rs1 rd js h
  | .XORI rd rs1 imm, js, h =>
      Natives.xoriInstr_eq_sail imm rs1 rd js h
  | .ORI rd rs1 imm, js, h =>
      Natives.oriInstr_eq_sail imm rs1 rd js h
  | .ANDI rd rs1 imm, js, h =>
      Natives.andiInstr_eq_sail imm rs1 rd js h
  | .SLLI rd rs1 shamt, js, h =>
      slliProgram_eq_sail shamt rs1 rd js h
  | .SRLI rd rs1 shamt, js, h =>
      srliProgram_eq_sail shamt rs1 rd js h
  | .SRAI rd rs1 shamt, js, h =>
      sraiProgram_eq_sail shamt rs1 rd js h
  | .ADD rd rs1 rs2, js, h =>
      Natives.addInstr_eq_sail rs2 rs1 rd js h
  | .SUB rd rs1 rs2, js, h =>
      Natives.subInstr_eq_sail rs2 rs1 rd js h
  | .SLL rd rs1 rs2, js, h =>
      sllProgram_eq_sail rs2 rs1 rd js h
  | .SLT rd rs1 rs2, js, h =>
      Natives.sltInstr_eq_sail rs2 rs1 rd js h
  | .SLTU rd rs1 rs2, js, h =>
      Natives.sltuInstr_eq_sail rs2 rs1 rd js h
  | .XOR rd rs1 rs2, js, h =>
      Natives.xorInstr_eq_sail rs2 rs1 rd js h
  | .SRL rd rs1 rs2, js, h =>
      srlProgram_eq_sail rs2 rs1 rd js h
  | .SRA rd rs1 rs2, js, h =>
      sraProgram_eq_sail rs2 rs1 rd js h
  | .OR rd rs1 rs2, js, h =>
      Natives.orInstr_eq_sail rs2 rs1 rd js h
  | .AND rd rs1 rs2, js, h =>
      Natives.andInstr_eq_sail rs2 rs1 rd js h
  | .ANDN rd rs1 rs2, js, h =>
      Natives.andnInstr_eq_sail rs2 rs1 rd js h
  | .LWU rd rs1 imm, js, h =>
      LWU_main.lwuProgram_eq_sail imm rs1 rd js h
  | .LD rd rs1 imm, js, h =>
      Natives.ldInstr_eq_sail imm rs1 rd js h
  | .ADDIW rd rs1 imm, js, h =>
      Natives.addiwInstr_eq_sail imm rs1 rd js h
  | .SLLIW rd rs1 shamt, js, h =>
      slliwProgram_eq_sail shamt rs1 rd js h
  | .SRLIW rd rs1 shamt, js, h =>
      srliwProgram_eq_sail shamt rs1 rd js h
  | .SRAIW rd rs1 shamt, js, h =>
      sraiwProgram_eq_sail shamt rs1 rd js h
  | .SUBW rd rs1 rs2, js, h =>
      Natives.subwInstr_eq_sail rs2 rs1 rd js h
  | .SLLW rd rs1 rs2, js, h =>
      sllwProgram_eq_sail rs2 rs1 rd js h
  | .SRLW rd rs1 rs2, js, h =>
      srlwProgram_eq_sail rs2 rs1 rd js h
  | .SRAW rd rs1 rs2, js, h =>
      srawProgram_eq_sail rs2 rs1 rd js h
  | .MUL rd rs1 rs2, js, h =>
      Natives.mulInstr_eq_sail rs2 rs1 rd js h
  | .MULH rd rs1 rs2, js, h =>
      mulhProgram_eq_sail rs2 rs1 rd js h
  | .MULHU rd rs1 rs2, js, h =>
      Natives.mulhuInstr_eq_sail rs2 rs1 rd js h
  | .MULHSU rd rs1 rs2, js, h =>
      mulhsuProgram_eq_sail rs2 rs1 rd js h
  | .MULW rd rs1 rs2, js, h =>
      Natives.mulwInstr_eq_sail rs2 rs1 rd js h
  | .SB rs2 rs1 imm, js, h =>
      SB_main.sbProgram_eq_sail imm rs2 rs1 js h
  | .SH rs2 rs1 imm, js, h =>
      SH_main.shProgram_eq_sail imm rs2 rs1 js h
  | .SW rs2 rs1 imm, js, h =>
      SW_main.swProgram_eq_sail imm rs2 rs1 js h
  | .SD rs2 rs1 imm, js, h =>
      Natives.sdInstr_eq_sail imm rs2 rs1 js h
  | .AMOSWAP_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoswapwProgram_eq_sail rs2 rs1 rd js h
  | .AMOADD_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoaddwProgram_eq_sail rs2 rs1 rd js h
  | .AMOXOR_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoxorwProgram_eq_sail rs2 rs1 rd js h
  | .AMOAND_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoandwProgram_eq_sail rs2 rs1 rd js h
  | .AMOOR_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoorwProgram_eq_sail rs2 rs1 rd js h
  | .AMOMIN_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amominwProgram_eq_sail rs2 rs1 rd js h
  | .AMOMAX_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amomaxwProgram_eq_sail rs2 rs1 rd js h
  | .AMOMINU_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amominuwProgram_eq_sail rs2 rs1 rd js h
  | .AMOMAXU_W rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amomaxuwProgram_eq_sail rs2 rs1 rd js h
  | .AMOSWAP_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoswapdProgram_eq_sail rs2 rs1 rd js h
  | .AMOADD_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoadddProgram_eq_sail rs2 rs1 rd js h
  | .AMOXOR_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoxordProgram_eq_sail rs2 rs1 rd js h
  | .AMOAND_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoanddProgram_eq_sail rs2 rs1 rd js h
  | .AMOOR_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amoordProgram_eq_sail rs2 rs1 rd js h
  | .AMOMIN_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amomindProgram_eq_sail rs2 rs1 rd js h
  | .AMOMAX_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amomaxdProgram_eq_sail rs2 rs1 rd js h
  | .AMOMINU_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amominudProgram_eq_sail rs2 rs1 rd js h
  | .AMOMAXU_D rd rs1 rs2 _aq _rl, js, h =>
      AtomicFamily.amomaxudProgram_eq_sail rs2 rs1 rd js h
    | .JAL rd imm, js, h =>
      Natives.jalInstr_eq_sail imm rd js h
  | .JALR rd rs1 imm, js, h =>
      Natives.jalrInstr_eq_sail imm rs1 rd js h
  | .BEQ rs1 rs2 imm, js, h =>
      Natives.beqInstr_eq_sail imm rs2 rs1 js h
  | .BNE rs1 rs2 imm, js, h =>
      Natives.bneInstr_eq_sail imm rs2 rs1 js h
  | .BLT rs1 rs2 imm, js, h =>
      Natives.bltInstr_eq_sail imm rs2 rs1 js h
  | .BGE rs1 rs2 imm, js, h =>
      Natives.bgeInstr_eq_sail imm rs2 rs1 js h
  | .BLTU rs1 rs2 imm, js, h =>
      Natives.bltuInstr_eq_sail imm rs2 rs1 js h
  | .BGEU rs1 rs2 imm, js, h =>
      Natives.bgeuInstr_eq_sail imm rs2 rs1 js h
  | .FENCE, js, h =>
      Natives.fenceInstr_eq_sail js h
  -- This will be proved shortly, once we confirm Jolt has the right set of assumptions.
  | .CSRRW rd csr rs1, js, h =>
      System.csrrwProgram_eq_sail_projected js csr rs1 rd h
  | .CSRRS rd csr rs1, js, h =>
      System.csrrsProgram_eq_sail_projected js csr rs1 rd h
  -- Jolt does not support User mode even with user extension enabled.
  -- See: https://randomwalks.xyz/blog/csrrw-bug/#mret-issue
  | .MRET, js, h =>
      System.mretProgram_eq_sail_projected js h
  -- Sail side just returns Trap (cannot be proven)
  | .ECALL, _js, _h => by
      sorry
  | .EBREAK, _js, _h => by
      sorry
   --- Cannot be proven :-( due to opaque axioms for 
   -- load_reservation
   -- cancel_resevation 
   -- match_reservation 
  | .LR_W _rd _rs1 _aq _rl, _js, _h => by
      sorry
  | .SC_W _rd _rs1 _rs2 _aq _rl, _js, _h => by
      sorry
  | .LR_D _rd _rs1 _aq _rl, _js, _h => by
      sorry
  | .SC_D _rd _rs1 _rs2 _aq _rl, _js, _h => by
      sorry
end RiscvInstruction
