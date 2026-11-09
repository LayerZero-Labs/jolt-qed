/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/


import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.SystemCSR

open LeanRV64D

/-!
# System-instruction Jolt expansion programs

These programs transcribe Jolt's expander at `669cf17ea` (a16z/jolt branch
`align/system-semantics`; the same `crates/jolt-program` as a16z/jolt#2384):
`crates/jolt-program/src/expand/control_flow/{ecall,mret,csr,csrrw,csrrs,csrrc,csr_immediate}.rs`
(`expand_ecall`, `expand_mret`, `emit_csr_read`, `emit_csr_swap`,
`emit_csr_bit_update`, and the immediate expanders).
The programs are ECALL, EBREAK, MRET, CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI and
CSRRCI; EBREAK retains its existing self-loop sequence.

The reserved virtual registers follow `tracer/src/utils/virtual_registers.rs`:

* `v32`: word reservation address
* `v33`: doubleword reservation address
* `v34`: trap handler / `mtvec`
* `v35`: `mscratch`
* `v36`: `mepc`
* `v37`: `mcause`
* `v38`: `mtval`
* `v39`: `mstatus`
* `v40`: first scratch register allocated for an instruction expansion
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

namespace JoltISA

/-- Rust's first `allocate()` result for system expansions. -/
def systemScratchVReg : VReg := inlineTmp0

/-- Rust `VirtualRegisterAllocator::csr_to_virtual_register` for the supported
machine CSR whitelist.
For example, 0x300 selects mstatus; an address outside the whitelist returns
`none`, matching Jolt's expander's `UnsupportedCsr` error. -/
def systemCSR? (csr : BitVec 12) : Option SystemCSR :=
  if csr = SystemCSR.address .mstatus then some .mstatus
  else if csr = SystemCSR.address .mtvec then some .mtvec
  else if csr = SystemCSR.address .mscratch then some .mscratch
  else if csr = SystemCSR.address .mepc then some .mepc
  else if csr = SystemCSR.address .mcause then some .mcause
  else if csr = SystemCSR.address .mtval then some .mtval
  else none

/-- Boolean architectural-register equality used by Rust's `rd == rs1` CSR
clobber cases. The generated `regidx` wrapper does not provide a direct
`DecidableEq` instance. -/
def sameXReg (lhs rhs : regidx) : Bool :=
  match lhs, rhs with
  | regidx.Regidx l, regidx.Regidx r => decide (l = r)

/-- Jolt's machine-mode ECALL trap entry at a86ec3716.
For example, MIE moves from bit 3 to MPIE at bit 7 before the jump to mtvec. -/
def ecallProgram : Program :=
  -- Rust: AUIPC mepc, 0.
  .instr (.AUIPC (.vreg mepcVReg) 0) <|
  -- Rust: ADDI mcause, x0, 11.
  .instr (.ADDI (.vreg mcauseVReg) (.xreg zreg) 11) <|
  -- Rust: ADDI mtval, x0, 0.
  .instr (.ADDI (.vreg mtvalVReg) (.xreg zreg) 0) <|
  -- Rust: ANDI temp, mstatus, MSTATUS_MIE; first allocate() is v40.
  .instr (.ANDI (.vreg inlineTmp0) (.vreg mstatusVReg) 8) <|
  -- Rust: SLLI mstatus, temp, 4, lowered to VirtualMULI by 16.
  .instr (.VirtualMULI (.vreg mstatusVReg) (.vreg inlineTmp0) 16) <|
  -- Rust: JALR temp, trap_handler, 0.
  .instr (.JALR (.vreg inlineTmp0) (.vreg trapHandlerVReg) 0) <|
  .done RETIRE_SUCCESS

/-- Rust `expand_ebreak`: emit `JAL scratch, 0`, a self-loop termination marker. -/
def ebreakProgram : Program :=
  .instr (JoltISA.Encoded.JAL (.vreg systemScratchVReg) (0 : BitVec 21)) <|
  .done RETIRE_SUCCESS

/-- Jolt's machine-mode trap return at a86ec3716.
For example, MPIE moves to MIE, MPIE becomes one, and execution jumps to mepc. -/
def mretProgram : Program :=
  -- Rust: SRLI mstatus, mstatus, 4, lowered to the right-shift bitmask row.
  .instr (.VirtualSRLI (.vreg mstatusVReg) (.vreg mstatusVReg) (srliBitmask (4#6))) <|
  -- Rust: ORI mstatus, mstatus, MSTATUS_MPIE.
  .instr (.ORI (.vreg mstatusVReg) (.vreg mstatusVReg) 0x80) <|
  -- Rust: JALR jalr_rd, mepc, 0; first allocate() is v40.
  .instr (.JALR (.vreg inlineTmp0) (.vreg mepcVReg) 0) <|
  .done RETIRE_SUCCESS

/-- Rust's `emit_csr_read`, with the caller's optional read of rd folded in.
The continuation runs after the read; for example, reading mstatus ORs in
the read-only MPP bits, while rd = x0 emits no read row. -/
def csrReadInto (csr : SystemCSR) (rd : regidx) (next : Program) : Program :=
  if isX0 rd then next
  else if csr = .mstatus then
    -- Rust: ORI rd, virtual_reg, MSTATUS_READ_ONLY_ONES.
    .instr (.ORI (.xreg rd) (.vreg (SystemCSR.vreg csr)) 0x1800) next
  else
    -- Rust: ADDI rd, virtual_reg, 0.
    .instr (.ADDI (.xreg rd) (.vreg (SystemCSR.vreg csr)) 0) next

/-- The final write in Rust's ordinary `emit_csr_swap` path.
For example, a mepc write clears source bit 0 with the full-width immediate -2. -/
def csrSwapWrite (csr : SystemCSR) (source : Src) : Program :=
  let vr := SystemCSR.vreg csr
  match csr with
  | .mstatus =>
    -- Rust: ANDI virtual_reg, source, MSTATUS_WRITABLE.
    .instr (.ANDI (.vreg vr) source 0x88) <| .done RETIRE_SUCCESS
  | .mepc =>
    -- Rust: ANDI virtual_reg, source, format_i_imm(-2).
    .instr (.ANDI (.vreg vr) source 0xffff_ffff_ffff_fffe) <| .done RETIRE_SUCCESS
  | _ =>
    -- Rust: ADDI virtual_reg, source, 0.
    .instr (.ADDI (.vreg vr) source 0) <| .done RETIRE_SUCCESS

/-- Rust's `expand_csrrw` and `emit_csr_swap` at a86ec3716, row for row.
For example, an aliased raw-CSR swap saves rs1 in v40 before reading rd;
mtvec instead consumes rs1 into a masked difference before the read. -/
def csrrwProgram (csr : SystemCSR) (rs1 rd : regidx) : Program :=
  let vr := SystemCSR.vreg csr
  if csr = .mtvec ∧ isX0 rs1 = false then
    -- Rust: XOR diff, source, virtual_reg; first allocate() is v40.
    .instr (.XOR (.vreg inlineTmp0) (.xreg rs1) (.vreg vr)) <|
    -- Rust: ANDI mask, source, 2; second allocate() is v41.
    .instr (.ANDI (.vreg inlineTmp1) (.xreg rs1) 2) <|
    -- Rust: VirtualShiftRightBitmask mask, mask, 0.
    .instr (.VirtualShiftRightBitmask (.vreg inlineTmp1) (.vreg inlineTmp1) 0) <|
    -- Rust: AND diff, diff, mask; mask is then released.
    .instr (.AND (.vreg inlineTmp0) (.vreg inlineTmp0) (.vreg inlineTmp1)) <|
    -- Rust: emit_csr_read if rd != 0.
    csrReadInto csr rd <|
    -- Rust: XOR virtual_reg, virtual_reg, diff.
    .instr (.XOR (.vreg vr) (.vreg vr) (.vreg inlineTmp0)) <|
    .done RETIRE_SUCCESS
  else if !isX0 rd && sameXReg rd rs1 then
    -- Rust: ADDI temp, source, 0; preserve an aliased source in v40.
    .instr (.ADDI (.vreg inlineTmp0) (.xreg rs1) 0) <|
    csrReadInto csr rd (csrSwapWrite csr (.vreg inlineTmp0))
  else
    csrReadInto csr rd (csrSwapWrite csr (.xreg rs1))

/-- Rust's shared `emit_csr_bit_update` at a86ec3716.
`clear = false` sets bits (CSRRS); `clear = true` clears them (CSRRC).
For example, setting mstatus first masks rs1 to MIE and MPIE in v40. -/
def csrBitUpdateProgram (clear : Bool) (csr : SystemCSR) (rs1 rd : regidx) : Program :=
  let vr := SystemCSR.vreg csr
  if isX0 rs1 then
    if isX0 rd then
      -- Rust: ADDI x0, x0, 0.
      pureWritebackRdZeroProgram
    else csrReadInto csr rd (.done RETIRE_SUCCESS)
  else
    let finish := fun bits =>
      csrReadInto csr rd <|
        -- Rust: OR virtual_reg, virtual_reg, bits, or ANDN for Clear.
        .instr (if clear then .ANDN (.vreg vr) (.vreg vr) bits
          else .OR (.vreg vr) (.vreg vr) bits) <|
        .done RETIRE_SUCCESS
    if !clear && decide (csr = .mstatus) then
      -- Rust: ANDI temp, bits, MSTATUS_WRITABLE; first allocate() is v40.
      .instr (.ANDI (.vreg inlineTmp0) (.xreg rs1) 0x88) <|
      finish (.vreg inlineTmp0)
    else if !clear && decide (csr = .mepc) then
      -- Rust: ANDI temp, bits, format_i_imm(-2).
      .instr (.ANDI (.vreg inlineTmp0) (.xreg rs1) 0xffff_ffff_ffff_fffe) <|
      finish (.vreg inlineTmp0)
    else if !clear && decide (csr = .mtvec) then
      -- Rust: ANDI temp, bits, 2.
      .instr (.ANDI (.vreg inlineTmp0) (.xreg rs1) 2) <|
      -- Rust: VirtualShiftRightBitmask temp, temp, 0.
      .instr (.VirtualShiftRightBitmask (.vreg inlineTmp0) (.vreg inlineTmp0) 0) <|
      -- Rust: AND temp, bits, temp.
      .instr (.AND (.vreg inlineTmp0) (.xreg rs1) (.vreg inlineTmp0)) <|
      finish (.vreg inlineTmp0)
    else if !isX0 rd && sameXReg rd rs1 then
      -- Rust: ADDI temp, bits, 0; preserve an aliased source in v40.
      .instr (.ADDI (.vreg inlineTmp0) (.xreg rs1) 0) <|
      finish (.vreg inlineTmp0)
    else finish (.xreg rs1)

/-- Rust's CSRRS sequence; for example, rs1 = x0 suppresses the CSR write. -/
def csrrsProgram (csr : SystemCSR) (rs1 rd : regidx) : Program :=
  csrBitUpdateProgram false csr rs1 rd

/-- Rust's CSRRC sequence; for example, a nonzero rs1 clears its bits with ANDN. -/
def csrrcProgram (csr : SystemCSR) (rs1 rd : regidx) : Program :=
  csrBitUpdateProgram true csr rs1 rd

/-- Rust's `expand_csrrwi` at a86ec3716, with a zero-extended five-bit source.
For example, a reserved mtvec MODE keeps the old MODE and replaces BASE. -/
def csrrwiProgram (csr : SystemCSR) (uimm : BitVec 5) (rd : regidx) : Program :=
  let vr := SystemCSR.vreg csr
  let bits := uimm.zeroExtend 64
  csrReadInto csr rd <|
  match csr with
  | .mstatus =>
    -- Rust: ADDI virtual_reg, x0, uimm & MSTATUS_WRITABLE.
    .instr (.ADDI (.vreg vr) (.xreg zreg) (bits &&& 0x88)) <| .done RETIRE_SUCCESS
  | .mepc =>
    -- Rust: ADDI virtual_reg, x0, uimm & !1.
    .instr (.ADDI (.vreg vr) (.xreg zreg) (bits &&& 0xffff_ffff_ffff_fffe)) <|
    .done RETIRE_SUCCESS
  | .mtvec =>
    if bits &&& 2 != 0 then
      -- Rust: ANDI virtual_reg, virtual_reg, 1.
      .instr (.ANDI (.vreg vr) (.vreg vr) 1) <|
      if bits &&& 0xffff_ffff_ffff_fffc != 0 then
        -- Rust: ORI virtual_reg, virtual_reg, uimm & !3, if BASE != 0.
        .instr (.ORI (.vreg vr) (.vreg vr) (bits &&& 0xffff_ffff_ffff_fffc)) <|
        .done RETIRE_SUCCESS
      else .done RETIRE_SUCCESS
    else
      -- Rust: ADDI virtual_reg, x0, uimm.
      .instr (.ADDI (.vreg vr) (.xreg zreg) bits) <| .done RETIRE_SUCCESS
  | _ =>
    -- Rust: ADDI virtual_reg, x0, uimm.
    .instr (.ADDI (.vreg vr) (.xreg zreg) bits) <| .done RETIRE_SUCCESS

/-- Rust's compile-time operand mask for immediate CSR bit updates.
For example, setting mtvec with reserved MODE removes both MODE bits,
whereas clearing mtvec removes only the reserved bit 1 from the operand. -/
def csrImmediateMask (clear : Bool) (csr : SystemCSR) (uimm : BitVec 5) : BitVec 64 :=
  let bits := uimm.zeroExtend 64
  match csr with
  | .mstatus => bits &&& 0x88
  | .mepc => bits &&& 0xffff_ffff_ffff_fffe
  | .mtvec =>
    if !clear && (bits &&& 2 != 0) then bits &&& 0xffff_ffff_ffff_fffc
    else bits &&& 0xffff_ffff_ffff_fffd
  | _ => bits

/-- Rust's `expand_bit_update` for immediate CSR forms at a86ec3716.
For example, a zero effective mask emits only the read, or one no-op for rd = x0. -/
def csrImmediateBitUpdateProgram
    (clear : Bool) (csr : SystemCSR) (uimm : BitVec 5) (rd : regidx) : Program :=
  let vr := SystemCSR.vreg csr
  let mask := csrImmediateMask clear csr uimm
  csrReadInto csr rd <|
  if mask != 0 then
    -- Rust: ORI virtual_reg, virtual_reg, mask, or ANDI with format_i_imm(!mask).
    .instr (if clear then .ANDI (.vreg vr) (.vreg vr) (~~~mask)
      else .ORI (.vreg vr) (.vreg vr) mask) <|
    .done RETIRE_SUCCESS
  else if isX0 rd then
    -- Rust: ADDI x0, x0, 0.
    pureWritebackRdZeroProgram
  else .done RETIRE_SUCCESS

/-- Rust's CSRRSI sequence; for example, immediate 8 sets mstatus.MIE. -/
def csrrsiProgram (csr : SystemCSR) (uimm : BitVec 5) (rd : regidx) : Program :=
  csrImmediateBitUpdateProgram false csr uimm rd

/-- Rust's CSRRCI sequence; for example, immediate 8 clears mstatus.MIE. -/
def csrrciProgram (csr : SystemCSR) (uimm : BitVec 5) (rd : regidx) : Program :=
  csrImmediateBitUpdateProgram true csr uimm rd

/-- Decode a supported raw CSR address before Jolt's CSRRW expansion.
For example, 0x300 selects the mstatus program and an unsupported address returns none. -/
def csrrwProgram? (csr : BitVec 12) (rs1 rd : regidx) : Option Program :=
  match systemCSR? csr with
  | some supported => some (csrrwProgram supported rs1 rd)
  | none => none

/-- Decode a supported raw CSR address before Jolt's CSRRS expansion.
For example, 0x300 selects the mstatus program and an unsupported address returns none. -/
def csrrsProgram? (csr : BitVec 12) (rs1 rd : regidx) : Option Program :=
  match systemCSR? csr with
  | some supported => some (csrrsProgram supported rs1 rd)
  | none => none

/-- Decode a supported raw CSR address before Jolt's CSRRC expansion.
For example, 0x300 selects the mstatus program and an unsupported address returns none. -/
def csrrcProgram? (csr : BitVec 12) (rs1 rd : regidx) : Option Program :=
  match systemCSR? csr with
  | some supported => some (csrrcProgram supported rs1 rd)
  | none => none

/-- Decode a supported raw CSR address before Jolt's CSRRWI expansion.
For example, 0x300 selects the mstatus program and an unsupported address returns none. -/
def csrrwiProgram? (csr : BitVec 12) (uimm : BitVec 5) (rd : regidx) : Option Program :=
  match systemCSR? csr with
  | some supported => some (csrrwiProgram supported uimm rd)
  | none => none

/-- Decode a supported raw CSR address before Jolt's CSRRSI expansion.
For example, 0x300 selects the mstatus program and an unsupported address returns none. -/
def csrrsiProgram? (csr : BitVec 12) (uimm : BitVec 5) (rd : regidx) : Option Program :=
  match systemCSR? csr with
  | some supported => some (csrrsiProgram supported uimm rd)
  | none => none

/-- Decode a supported raw CSR address before Jolt's CSRRCI expansion.
For example, 0x300 selects the mstatus program and an unsupported address returns none. -/
def csrrciProgram? (csr : BitVec 12) (uimm : BitVec 5) (rd : regidx) : Option Program :=
  match systemCSR? csr with
  | some supported => some (csrrciProgram supported uimm rd)
  | none => none

end JoltISA
