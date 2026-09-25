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
-- Final immediates are already decoded; inline expansion may emit full u64
-- operands (e.g. ADDI with 4096). Source encoding widths belong in Encoded below.
-- Rust: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/expand/inline.rs#L204-L245
-- Rust formats: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/tracer/src/instruction/format/format_i.rs#L9-L14
-- FormatB retains a signed i128; proof-trace conversion separately bounds its magnitude.
-- Rust: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/tracer/src/instruction/format/format_b.rs#L9-L14
inductive Instr where
  | ADDI (dst : Dst) (src : Src) (imm : BitVec 64)
  | ADDIW (dst : Dst) (src : Src) (imm : BitVec 64)
  | ANDI (dst : Dst) (src : Src) (imm : BitVec 64)
  | ORI  (dst : Dst) (src : Src) (imm : BitVec 64)
  | XORI (dst : Dst) (src : Src) (imm : BitVec 64)
  | SLTI (dst : Dst) (src : Src) (imm : BitVec 64)
  | SLTIU (dst : Dst) (src : Src) (imm : BitVec 64)
  | LUI  (dst : Dst) (imm : BitVec 64)
  | AUIPC (dst : Dst) (imm : BitVec 64)
  | JAL (dst : Dst) (imm : BitVec 64)
  | JALR (dst : Dst) (base : Src) (imm : BitVec 64)
  | BEQ (lhs rhs : Src) (imm : BitVec 128)
  | BNE (lhs rhs : Src) (imm : BitVec 128)
  | BLT (lhs rhs : Src) (imm : BitVec 128)
  | BGE (lhs rhs : Src) (imm : BitVec 128)
  | BLTU (lhs rhs : Src) (imm : BitVec 128)
  | BGEU (lhs rhs : Src) (imm : BitVec 128)
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
  | VirtualXORROTL1 (dst : Dst) (lhs rhs : Src)
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
  | VirtualAlignAddr (dst : Dst) (base : Src) (imm : BitVec 64)
  | VirtualWindowMaskB (dst : Dst) (base : Src) (imm : BitVec 64)
  | VirtualWindowMaskH (dst : Dst) (base : Src) (imm : BitVec 64)
  | VirtualWindowMaskW (dst : Dst) (base : Src) (imm : BitVec 64)
  | VirtualPext (dst : Dst) (value mask : Src)
  | VirtualPextSigned (dst : Dst) (value mask : Src)
  | VirtualShiftDataB (dst : Dst) (value address : Src)
  | VirtualShiftDataH (dst : Dst) (value address : Src)
  | VirtualShiftDataW (dst : Dst) (value address : Src)
  | VirtualSignExtendWord (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
  | VirtualZeroExtendWord (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
  | VirtualMovsign (dst : Dst) (src : Src) (imm : BitVec 64 := 0)
  | VirtualAssertHalfwordAlignment (base : Src) (imm : BitVec 64) (fault : ExceptionType)
  | VirtualAssertWordAlignment (base : Src) (imm : BitVec 64) (fault : ExceptionType)
  | LD (faultClass : LoadFaultClass) (dst : Dst) (base : Src) (imm : BitVec 64)
  | SD (base value : Src) (imm : BitVec 64)
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
  | VirtualAssertEQ (lhs rhs : Src) (imm: BitVec 128)
  | VirtualAssertValidDiv0 (divisor quotient : Src) (imm : BitVec 128 := 0)
  | VirtualNegateIf (dst : Dst) (signSource value : Src)
  | VirtualAssertValidUnsignedRemainder (remainder divisor : Src) (imm : BitVec 128 := 0)
  | VirtualAssertMulUNoOverflow (lhs rhs : Src) (imm : BitVec 128 := 0)
  | VirtualAssertLTE (lhs rhs : Src) (imm : BitVec 128 := 0)
  deriving Repr

/-! Decode source operands before constructing final rows. These are abbreviations,
not extra execution rules: every resulting instruction runs through execInstr.
AUIPC's encoded upper immediate is shifted once here, just as in Rust's decoder.
Rust: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/image/decode.rs#L471-L485
-/
namespace Encoded

abbrev ADDI (dst : Dst) (src : Src) (imm : BitVec 12) : Instr :=
  .ADDI dst src (sign_extend (m := 64) imm)

abbrev ADDIW (dst : Dst) (src : Src) (imm : BitVec 12) : Instr :=
  .ADDIW dst src (sign_extend (m := 64) imm)

abbrev ANDI (dst : Dst) (src : Src) (imm : BitVec 12) : Instr :=
  .ANDI dst src (sign_extend (m := 64) imm)

abbrev ORI (dst : Dst) (src : Src) (imm : BitVec 12) : Instr :=
  .ORI dst src (sign_extend (m := 64) imm)

abbrev XORI (dst : Dst) (src : Src) (imm : BitVec 12) : Instr :=
  .XORI dst src (sign_extend (m := 64) imm)

abbrev SLTI (dst : Dst) (src : Src) (imm : BitVec 12) : Instr :=
  .SLTI dst src (sign_extend (m := 64) imm)

abbrev SLTIU (dst : Dst) (src : Src) (imm : BitVec 12) : Instr :=
  .SLTIU dst src (sign_extend (m := 64) imm)

abbrev JALR (dst : Dst) (src : Src) (imm : BitVec 12) : Instr :=
  .JALR dst src (sign_extend (m := 64) imm)

abbrev VirtualAlignAddr (dst : Dst) (src : Src) (imm : BitVec 12) : Instr :=
  .VirtualAlignAddr dst src (sign_extend (m := 64) imm)

abbrev VirtualWindowMaskB (dst : Dst) (src : Src) (imm : BitVec 12) : Instr :=
  .VirtualWindowMaskB dst src (sign_extend (m := 64) imm)

abbrev VirtualWindowMaskH (dst : Dst) (src : Src) (imm : BitVec 12) : Instr :=
  .VirtualWindowMaskH dst src (sign_extend (m := 64) imm)

abbrev VirtualWindowMaskW (dst : Dst) (src : Src) (imm : BitVec 12) : Instr :=
  .VirtualWindowMaskW dst src (sign_extend (m := 64) imm)

abbrev LD (fault : LoadFaultClass) (dst : Dst) (base : Src) (imm : BitVec 12) : Instr :=
  .LD fault dst base (sign_extend (m := 64) imm)

abbrev SD (base value : Src) (imm : BitVec 12) : Instr :=
  .SD base value (sign_extend (m := 64) imm)

abbrev BEQ (lhs rhs : Src) (imm : BitVec 13) : Instr :=
  .BEQ lhs rhs (sign_extend (m := 128) imm)

abbrev BNE (lhs rhs : Src) (imm : BitVec 13) : Instr :=
  .BNE lhs rhs (sign_extend (m := 128) imm)

abbrev BLT (lhs rhs : Src) (imm : BitVec 13) : Instr :=
  .BLT lhs rhs (sign_extend (m := 128) imm)

abbrev BGE (lhs rhs : Src) (imm : BitVec 13) : Instr :=
  .BGE lhs rhs (sign_extend (m := 128) imm)

abbrev BLTU (lhs rhs : Src) (imm : BitVec 13) : Instr :=
  .BLTU lhs rhs (sign_extend (m := 128) imm)

abbrev BGEU (lhs rhs : Src) (imm : BitVec 13) : Instr :=
  .BGEU lhs rhs (sign_extend (m := 128) imm)

abbrev VirtualAssertEQ (lhs rhs : Src) (imm : BitVec 13) : Instr :=
  .VirtualAssertEQ lhs rhs (sign_extend (m := 128) imm)

abbrev VirtualAssertHalfwordAlignment (base : regidx) (imm : BitVec 12) (fault : ExceptionType) : Instr :=
  .VirtualAssertHalfwordAlignment (.xreg base) (sign_extend (m := 64) imm) fault

abbrev VirtualAssertWordAlignment (base : regidx) (imm : BitVec 12) (fault : ExceptionType) : Instr :=
  .VirtualAssertWordAlignment (.xreg base) (sign_extend (m := 64) imm) fault

abbrev AUIPC (dst : Dst) (imm : BitVec 20) : Instr :=
  .AUIPC dst (sign_extend (m := 64) (imm +++ (0 : BitVec 12)))

abbrev JAL (dst : Dst) (imm : BitVec 21) : Instr :=
  .JAL dst (sign_extend (m := 64) imm)

end Encoded

/-- Nat-valued helper parameters denote Rust u64 immediates. Keep Nat for the
arithmetic helper API, but reject values that Rust's final format cannot store.
Rust: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/tracer/src/instruction/format/format_virtual_right_shift_i.rs#L9-L14
-/
def Instr.OperandsRepresentable : Instr → Prop
  | .VirtualPow2I _ imm | .VirtualPow2IW _ imm | .VirtualShiftRightBitmaskI _ imm
  | .VirtualSRLI _ _ imm | .VirtualSRAI _ _ imm | .VirtualSRLIW _ _ imm
  | .VirtualSRAIW _ _ imm | .VirtualROTRI _ _ imm | .VirtualROTRIW _ _ imm =>
      imm < 2 ^ 64
  | _ => True

/-- FormatB carries i128, but successful proof-trace conversion requires a u64
magnitude. Preserve the signed immediate, including values ignored by execution.
Rust: https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-riscv/src/trace_row.rs#L279-L283
-/
def Instr.CompactImmediateFits : Instr → Prop
  | .BEQ _ _ imm | .BNE _ _ imm | .BLT _ _ imm | .BGE _ _ imm
  | .BLTU _ _ imm | .BGEU _ _ imm | .VirtualAssertEQ _ _ imm
  | .VirtualAssertValidDiv0 _ _ imm | .VirtualAssertValidUnsignedRemainder _ _ imm
  | .VirtualAssertMulUNoOverflow _ _ imm | .VirtualAssertLTE _ _ imm =>
      imm.toInt.natAbs < 2 ^ 64
  | _ => True


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
  .instr (JoltISA.Encoded.ADDI (.xreg (regidx.Regidx 0)) (.xreg (regidx.Regidx 0)) (0 : BitVec 12)) <|
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
