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
import JoltBytecode.InstructionEquivalence.Instructions.System.Trap
import JoltBytecode.InstructionEquivalence.Instructions.System.CsrReg
import JoltBytecode.InstructionEquivalence.Instructions.System.Sc

open LeanRV64D

/-!
# RISC-V Instructions

THis can be thought of as the projects "main" file. 
For every RISC-V instruction, we tell you 
what the equivalence proposition is, what assumptions are needed,
and finally where the proof is.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D

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
  | CSRRC (rd : regidx) (csr : JoltISA.SystemCSR) (rs1 : regidx)
  | CSRRWI (rd : regidx) (csr : JoltISA.SystemCSR) (uimm : BitVec 5)
  | CSRRSI (rd : regidx) (csr : JoltISA.SystemCSR) (uimm : BitVec 5)
  | CSRRCI (rd : regidx) (csr : JoltISA.SystemCSR) (uimm : BitVec 5)

  /- Jolt-supported RvPrivileged source instruction.
     Source: https://docs.riscv.org/reference/isa/v20260120/priv/priv-insns.html -/
  | MRET
  deriving Repr

namespace RiscvInstruction

abbrev SailExecution := SailM ExecutionResult

/-- MRET runs on Jolt's active Machine-mode hart with legal persistent system
registers.
For example, a legal saved mepc is even and v39 contains only MIE and MPIE. -/
structure MretEqAssumptions (js : SailJoltState) : Type where
  invariant : Step.StepInvariant (System.systemProject js)
  mstatus_bits : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88#64) = 0#64
  mepc_align : (js.vregs JoltISA.mepcVReg).getLsbD 0 = false

/-- CSR instructions run on the active Machine-mode hart with legal stored
CSR values: v39 contains only MIE and MPIE, mtvec has mode 0 or 1, and mepc is even.
For example, zero raw system registers satisfy all three value restrictions. -/
structure CsrEqAssumptions (js : SailJoltState) : Type where
  invariant : Step.StepInvariant (System.systemProject js)
  mstatus_bits : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88#64) = 0#64
  mtvec_mode : (js.vregs JoltISA.trapHandlerVReg).getLsbD 1 = false
  mepc_align : (js.vregs JoltISA.mepcVReg).getLsbD 0 = false

/-- Register CSR instructions also read their source and link the persistent
system registers to Sail.
For example, CSRRW reads rs1 before writing the old CSR value to rd. -/
structure CsrRegEqAssumptions (rs1 : regidx) (js : SailJoltState) : Type
    extends CsrEqAssumptions js, UnarySourceReadWithLinkedCSRs rs1 js

/-- Recover the CSR overlay agreement from a register CSR bundle.
For example, this transports its source read to the projected state. -/
theorem CsrRegEqAssumptions.linkedCSRs {rs1 : regidx} {js : SailJoltState}
    (h : CsrRegEqAssumptions rs1 js) : LinkedCSRs js :=
  h.toUnarySourceReadWithLinkedCSRs.linkedCSRs

/-- Assumption payload for the equivalence statement.

The advice-backed ALU instructions all need source-register read facts; their
advice operands live in the `RiscvInstruction` constructor itself. -/
def equivAssumptions : (instr : RiscvInstruction) → SailJoltState → Type
  | .SC_W _ rs1 rs2 _ _, js => SystemProofs.ReservationStoreEqAssumptions false rs2 rs1 js
  | .SC_D _ rs1 rs2 _ _, js => SystemProofs.ReservationStoreEqAssumptions true rs2 rs1 js
  | .LR_W _ rs1 _ _, js => SystemProofs.ReservationReadEqAssumptions false rs1 js
  | .LR_D _ rs1 _ _, js => SystemProofs.ReservationReadEqAssumptions true rs1 js
  | .MRET, js => MretEqAssumptions js
  | .CSRRW _ _ rs1, js | .CSRRS _ _ rs1, js | .CSRRC _ _ rs1, js =>
      CsrRegEqAssumptions rs1 js
  | .CSRRWI .., js | .CSRRSI .., js | .CSRRCI .., js => CsrEqAssumptions js
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
  | _, _ => Unit

end RiscvInstruction
