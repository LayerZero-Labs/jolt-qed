/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/

import JoltBytecode.JoltISA.VirtualRegisters

/-!
# Jolt ISA syntax

This is the data layer for final Jolt trace-row instructions. Source
instructions that Rust lowers through `inline_sequence` belong in the expansion
layer, not as constructors here.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- An instruction source operand: either a virtual register or an
architectural Sail register. -/
inductive Src where
  | vreg : VReg → Src
  | xreg : regidx → Src
  deriving Repr

/-- An instruction destination operand: either a virtual register or an
architectural Sail register. -/
inductive Dst where
  | vreg : VReg → Dst
  | xreg : regidx → Dst
  deriving Repr

/-- Sail-facing fault classification for a Jolt `LD` row.

Rust/Jolt does not carry a separate opcode bit for normal loads versus the read
side of an AMO expansion. Sail does distinguish those pathways when classifying
memory exceptions. This marker is Lean proof metadata used to preserve the Rust
row shape while selecting the Sail exception class expected at that expansion
boundary. It does not change the successful load path.
-/
inductive LoadFaultClass where
  | normal
  | amo
  deriving Repr

-- To make sure the Sail Pipeline does not complain.
def LoadFaultClass.alignFault : LoadFaultClass → ExceptionType
  | .normal => ExceptionType.E_Load_Addr_Align ()
  | .amo => ExceptionType.E_SAMO_Addr_Align ()

-- Opcodes (Jolt ISA)
-- Preserve immediate fields even when execution ignores them: Rust's Imm witness
-- still records them. Zero defaults describe the existing generated expansions;
-- importing a Rust row must supply its actual immediate.
-- Rust: [instruction formats](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction/format).
inductive Instr where
  | ADDI (dst : Dst) (src : Src) (imm : BitVec 12)
  | ADDIW (dst : Dst) (src : Src) (imm : BitVec 12)
  | ANDI (dst : Dst) (src : Src) (imm : BitVec 12)
  | ORI  (dst : Dst) (src : Src) (imm : BitVec 12)
  | XORI (dst : Dst) (src : Src) (imm : BitVec 12)
  | SLTI (dst : Dst) (src : Src) (imm : BitVec 12)
  | SLTIU (dst : Dst) (src : Src) (imm : BitVec 12)
  | LUI  (dst : Dst) (imm : BitVec 64)
  | AUIPC (dst : Dst) (imm : BitVec 20)
  | JAL (dst : Dst) (imm : BitVec 21)
  | JALR (dst : Dst) (base : Src) (imm : BitVec 12)
  | BEQ (lhs rhs : Src) (imm : BitVec 13)
  | BNE (lhs rhs : Src) (imm : BitVec 13)
  | BLT (lhs rhs : Src) (imm : BitVec 13)
  | BGE (lhs rhs : Src) (imm : BitVec 13)
  | BLTU (lhs rhs : Src) (imm : BitVec 13)
  | BGEU (lhs rhs : Src) (imm : BitVec 13)
  | FENCE
  | ADD  (dst : Dst) (lhs rhs : Src)
  | ADDW (dst : Dst) (lhs rhs : Src)
  | SUB  (dst : Dst) (lhs rhs : Src)
  | SUBW (dst : Dst) (lhs rhs : Src)
  | MUL  (dst : Dst) (lhs rhs : Src)
  | MULW (dst : Dst) (lhs rhs : Src)
  | MULHU (dst : Dst) (lhs rhs : Src)
  | ANDN (dst : Dst) (lhs rhs : Src)
  | VirtualMULI (dst : Dst) (src : Src) (imm : BitVec 64)
  | VirtualMULIW (dst : Dst) (src : Src) (imm : BitVec 64)
  | VirtualPow2 (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
  | VirtualPow2W (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
  | VirtualPow2I (dst : Dst) (imm : Nat)
  | VirtualPow2IW (dst : Dst) (imm : Nat)
  | VirtualShiftRightBitmask (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
  | VirtualShiftRightBitmaskI (dst : Dst) (imm : Nat)
  | VirtualShiftRightBitmaskW (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
  | VirtualSRLI (dst : Dst) (src : Src) (bitmask : Nat)
  | VirtualSRAI (dst : Dst) (src : Src) (bitmask : Nat)
  | VirtualSRLIW (dst : Dst) (src : Src) (bitmask : Nat)
  | VirtualSRAIW (dst : Dst) (src : Src) (bitmask : Nat)
  | VirtualSRL (dst : Dst) (value bitmask : Src)
  | VirtualSRA (dst : Dst) (value bitmask : Src)
  | VirtualSRLW (dst : Dst) (value bitmask : Src)
  | VirtualSRAW (dst : Dst) (value bitmask : Src)
  | VirtualROTRI (dst : Dst) (src : Src) (bitmask : Nat)
  | VirtualROTRIW (dst : Dst) (src : Src) (bitmask : Nat)
  | VirtualRev8W (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
  | VirtualXORROT32 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROT24 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROT16 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROT63 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROTW16 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROTW12 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROTW8 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROTW7 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROTW22 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROTW19 (dst : Dst) (lhs rhs : Src)
  | VirtualXORROTW6 (dst : Dst) (lhs rhs : Src)
  | OR   (dst : Dst) (lhs rhs : Src)
  | XOR  (dst : Dst) (lhs rhs : Src)
  | AND  (dst : Dst) (lhs rhs : Src)
  | SLT  (dst : Dst) (lhs rhs : Src)
  | SLTU (dst : Dst) (lhs rhs : Src)
  | VirtualAlignAddr (dst : Dst) (base : Src) (imm : BitVec 12)
  | VirtualWindowMaskB (dst : Dst) (base : Src) (imm : BitVec 12)
  | VirtualWindowMaskH (dst : Dst) (base : Src) (imm : BitVec 12)
  | VirtualWindowMaskW (dst : Dst) (base : Src) (imm : BitVec 12)
  | VirtualPext (dst : Dst) (value mask : Src)
  | VirtualPextSigned (dst : Dst) (value mask : Src)
  | VirtualShiftDataB (dst : Dst) (value address : Src)
  | VirtualShiftDataH (dst : Dst) (value address : Src)
  | VirtualShiftDataW (dst : Dst) (value address : Src)
  | VirtualSignExtendWord (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
  | VirtualZeroExtendWord (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
  | VirtualMovsign (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
  | VirtualAssertHalfwordAlignment (base : regidx) (imm : BitVec 12) (fault : ExceptionType)
  | VirtualAssertWordAlignment (base : regidx) (imm : BitVec 12) (fault : ExceptionType)
  | LD (faultClass : LoadFaultClass) (dst : Dst) (base : Src) (imm : BitVec 12)
  | SD (base value : Src) (imm : BitVec 12)
  | VirtualAdvice (dst : Dst) (value : BitVec 64) (imm : BitVec 64 := 0)
  | VirtualAdviceLoad (dst : Dst) (byteCount : BitVec 64)
  -- Rust captures src even though computing the advice length ignores it.
  -- Rust: [VirtualAdviceLen format](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction/virtual_advice_len.rs:9).
  | VirtualAdviceLen (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
  -- Rust captures src before execution and dst afterward, even though HOST_IO
  -- does not write dst. Preserve the final row's operands, including rd=x0 rewrites.
  -- Rust: [VirtualHostIO format](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction/virtual_host_io.rs:8).
  -- Rust: [FormatI capture](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction/format/format_i.rs:72).
  | VirtualHostIO (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
  | VirtualAssertEQ (lhs rhs : Src) (imm: BitVec 13)
  | VirtualAssertValidDiv0 (divisor quotient : Src) (imm : BitVec 128 := 0)
  | VirtualNegateIf (dst : Dst) (signSource value : Src)
  | VirtualAssertValidUnsignedRemainder (remainder divisor : Src) (imm : BitVec 128 := 0)
  | VirtualAssertMulUNoOverflow (lhs rhs : Src) (imm : BitVec 128 := 0)
  | VirtualAssertLTE (lhs rhs : Src) (imm : BitVec 128 := 0)
  deriving Repr

/-- Source instructions that Rust expands before final Jolt bytecode.

This mirrors the built-in `SourceInstructionKind` cases handled by
`/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/expand/mod.rs`
in `expand_source_only_instruction`. -/
inductive Expanded where
  | MULH (dst : Dst) (lhs rhs : Src)
  | MULHSU (dst : Dst) (lhs rhs : Src)
  | LB (dst : Dst) (base : Src) (imm : BitVec 12)
  | LBU (dst : Dst) (base : Src) (imm : BitVec 12)
  | LH (dst : Dst) (base : Src) (imm : BitVec 12)
  | LHU (dst : Dst) (base : Src) (imm : BitVec 12)
  | LW (dst : Dst) (base : Src) (imm : BitVec 12)
  | LWU (dst : Dst) (base : Src) (imm : BitVec 12)
  | AdviceLB (dst : Dst)
  | AdviceLH (dst : Dst)
  | AdviceLW (dst : Dst)
  | AdviceLD (dst : Dst)
  | AMOADDD (dst : Dst) (addr value : Src)
  | AMOANDD (dst : Dst) (addr value : Src)
  | AMOORD (dst : Dst) (addr value : Src)
  | AMOXORD (dst : Dst) (addr value : Src)
  | AMOSWAPD (dst : Dst) (addr value : Src)
  | AMOMAXD (dst : Dst) (addr value : Src)
  | AMOMAXUD (dst : Dst) (addr value : Src)
  | AMOMIND (dst : Dst) (addr value : Src)
  | AMOMINUD (dst : Dst) (addr value : Src)
  | AMOADDW (dst : Dst) (addr value : Src)
  | AMOANDW (dst : Dst) (addr value : Src)
  | AMOORW (dst : Dst) (addr value : Src)
  | AMOXORW (dst : Dst) (addr value : Src)
  | AMOSWAPW (dst : Dst) (addr value : Src)
  | AMOMAXW (dst : Dst) (addr value : Src)
  | AMOMAXUW (dst : Dst) (addr value : Src)
  | AMOMINW (dst : Dst) (addr value : Src)
  | AMOMINUW (dst : Dst) (addr value : Src)
  | LRD (dst : Dst) (addr : Src)
  | LRW (dst : Dst) (addr : Src)
  | DIV (dst : Dst) (lhs rhs : Src)
  | DIVU (dst : Dst) (lhs rhs : Src)
  | DIVW (dst : Dst) (lhs rhs : Src)
  | DIVUW (dst : Dst) (lhs rhs : Src)
  | REM (dst : Dst) (lhs rhs : Src)
  | REMU (dst : Dst) (lhs rhs : Src)
  | REMW (dst : Dst) (lhs rhs : Src)
  | REMUW (dst : Dst) (lhs rhs : Src)
  | SB (base value : Src) (imm : BitVec 12)
  | SCD (dst : Dst) (addr value : Src)
  | SCW (dst : Dst) (addr value : Src)
  | SH (base value : Src) (imm : BitVec 12)
  | SW (base value : Src) (imm : BitVec 12)
  | CSRRW (dst : Dst) (src : Src) (csr : BitVec 12)
  | CSRRS (dst : Dst) (src : Src) (csr : BitVec 12)
  | EBREAK
  | ECALL
  | MRET
  | SLL (dst : Dst) (value shamt : Src)
  | SLLI (dst : Dst) (src : Src) (shamt : BitVec 6)
  | SLLW (dst : Dst) (value shamt : Src)
  | SLLIW (dst : Dst) (src : Src) (shamt : BitVec 5)
  | SRL (dst : Dst) (value shamt : Src)
  | SRLI (dst : Dst) (src : Src) (shamt : BitVec 6)
  | SRA (dst : Dst) (value shamt : Src)
  | SRAI (dst : Dst) (src : Src) (shamt : BitVec 6)
  | SRLIW (dst : Dst) (src : Src) (shamt : BitVec 5)
  | SRAIW (dst : Dst) (src : Src) (shamt : BitVec 5)
  | SRLW (dst : Dst) (value shamt : Src)
  | SRAW (dst : Dst) (value shamt : Src)
  deriving Repr

/-- Structured Jolt bytecode programs.

`instr i next` means: execute `i`; if it retires successfully, continue with
`next`; otherwise return the non-retire result immediately. -/
inductive Program where
  | done (result : ExecutionResult)
  | instr (instr : Instr) (next : Program)
  deriving Repr

/-- Given a list of instructions build a straight-line "run every instruction, then retire"
program -/
def Program.seq (instrs : List Instr) : Program :=
  instrs.foldr Program.instr (.done RETIRE_SUCCESS)

/-- Append two Jolt programs. -/
def Program.append : Program → Program → Program
  | .done (.Retire_Success ()), second => second
  | .done result, _ => .done result
  | .instr instruction rest, second => .instr instruction (rest.append second)

/-- Rust's trace-dispatch replacement for pure writeback instructions whose
destination is architectural `x0`: emit a single no-op `ADDI x0, x0, 0` row. -/
def pureWritebackRdZeroProgram : Program :=
  .instr (.ADDI (.xreg (regidx.Regidx 0)) (.xreg (regidx.Regidx 0)) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Boolean test for architectural register `x0`. -/
def isX0 (rd : regidx) : Bool :=
  match rd with
  | regidx.Regidx bits => decide (bits.toNat = 0)

/-- Rust's trace-dispatch rule for pure writeback instructions. -/
def pureWritebackTraceProgram (rd : regidx) (normal : Program) : Program :=
  if isX0 rd then pureWritebackRdZeroProgram else normal

/-- The first virtual register Rust's `allocate()` returns for top-level
side-effecting `rd = x0` source rewrites. 
-/
abbrev rdZeroRewriteVReg : VReg := inlineTmp 0

/-- Rust's source-materialization rule for side-effecting instructions with
`rd = x0`: keep the side effect, but rewrite the destination to a temporary
virtual register so the final row never writes `x0`. -/
def sideEffectingRdZeroDst (rd : regidx) : Dst :=
  if isX0 rd then .vreg rdZeroRewriteVReg else .xreg rd

/-- Lift Rust's source-materialization rule to an already-parsed destination. -/
def sideEffectingDst : Dst → Dst
  | .xreg rd => sideEffectingRdZeroDst rd
  | .vreg v => .vreg v

@[simp] theorem sideEffectingDst_vreg (v : VReg) :
    sideEffectingDst (.vreg v) = .vreg v := rfl

end JoltISA
