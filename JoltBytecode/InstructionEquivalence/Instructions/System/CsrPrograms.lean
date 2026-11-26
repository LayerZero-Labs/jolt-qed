import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.JoltISA.ExpansionsHandwritten

open LeanRV64D
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D.Functions

/-!
# Structured views of the generated CSR register programs

Jolt's expander builds CSRRW, CSRRS and CSRRC from a few shared pieces in
`crates/jolt-program/src/expand/control_flow/csr.rs` at `504dd78a2`:
`emit_csr_read` (here `csrReadInto`), the final write of `emit_csr_swap`
(here `csrSwapWrite`), and `emit_csr_bit_update` (here `csrBitUpdateProgram`).
The generated programs in `ExpansionsAutomated.lean` are flat, one branch per case.
These definitions rebuild the same programs from the shared pieces, and the
`*_eq` theorems prove that each generated program equals its structured view,
so proofs can follow the shared pieces once instead of every flat branch.
These definitions are used only by proofs.
Based on Quang Dao's `JoltISA/Expansions/System.lean` in PR #73.
-/

namespace JoltISA

/-- Boolean equality of two architectural registers, used for Jolt's `rd == rs1`
cases; for example, `sameXReg x5 x5 = true`. -/
def sameXReg (lhs rhs : regidx) : Bool :=
  match lhs, rhs with
  | regidx.Regidx l, regidx.Regidx r => decide (l = r)

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

/-- Rust's `expand_csrrw` and `emit_csr_swap` at 504dd78a2, row for row.
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

/-- Rust's shared `emit_csr_bit_update` at 504dd78a2.
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

/-- `isX0` on a register index is the test `index = 0`; for example, x0 gives true. -/
private theorem isX0_regidx (r : BitVec 5) : isX0 (regidx.Regidx r) = decide (r = 0) := by
  simp only [isX0]
  rw [decide_eq_decide]
  exact ⟨fun h => BitVec.eq_of_toNat_eq (by simpa using h), fun h => by simp [h]⟩

/-- The derived equality test on register indices is index equality; for example,
`x5 == x5` is true. -/
private theorem regidx_beq (a b : BitVec 5) :
    (regidx.Regidx a == regidx.Regidx b) = decide (a = b) := by
  show (a == b) = decide (a = b)
  by_cases h : a = b <;> simp [h]

/-- The generated CSRRW program is its structured view.
For example, CSRRW x5, mscratch, x5 saves x5 in v40, reads mscratch into x5,
and writes v40 to mscratch in both forms. -/
theorem csrrwProgramAuto_eq (csr : SystemCSR) (rd rs1 : regidx) :
    csrrwProgramAuto csr rd rs1 = csrrwProgram csr rs1 rd := by
  obtain ⟨r⟩ := rs1
  obtain ⟨d⟩ := rd
  cases csr <;> by_cases hr : r = 0 <;> by_cases hd : d = 0 <;> by_cases hdr : d = r <;>
    (try subst hr) <;> (try subst hd) <;>
    simp_all [csrrwProgramAuto, csrrwProgram, csrReadInto, csrSwapWrite, isX0_regidx,
      regidx_beq, sameXReg, Encoded.ANDI, Encoded.ADDI, SystemCSR.vreg,
      mstatusVReg, trapHandlerVReg, mscratchVReg, mepcVReg, mcauseVReg, mtvalVReg,
      inlineTmp0, inlineTmp1, inlineTmp, inlineRegisterBase,
      riscvRegisterBase, riscvRegisterCount, numReservedVirtualRegisters] <;> decide

/-- The generated CSRRS program is its structured view.
For example, CSRRS x0, mstatus, x5 masks x5 to MIE and MPIE in v40 and ORs v40
into v39 in both forms. -/
theorem csrrsProgramAuto_eq (csr : SystemCSR) (rd rs1 : regidx) :
    csrrsProgramAuto csr rd rs1 = csrrsProgram csr rs1 rd := by
  obtain ⟨r⟩ := rs1
  obtain ⟨d⟩ := rd
  cases csr <;> by_cases hr : r = 0 <;> by_cases hd : d = 0 <;> by_cases hdr : d = r <;>
    (try subst hr) <;> (try subst hd) <;>
    simp_all [csrrsProgramAuto, csrrsProgram, csrBitUpdateProgram, csrReadInto, isX0_regidx,
      regidx_beq, sameXReg, pureWritebackRdZeroProgram, Encoded.ANDI, Encoded.ADDI,
      SystemCSR.vreg, mstatusVReg, trapHandlerVReg, mscratchVReg, mepcVReg, mcauseVReg,
      mtvalVReg, inlineTmp0, inlineTmp, inlineRegisterBase,
      riscvRegisterBase, riscvRegisterCount, numReservedVirtualRegisters] <;> decide

/-- The generated CSRRC program is its structured view.
For example, CSRRC x0, mscratch, x5 clears x5's bits from v35 with ANDN in both forms. -/
theorem csrrcProgramAuto_eq (csr : SystemCSR) (rd rs1 : regidx) :
    csrrcProgramAuto csr rd rs1 = csrrcProgram csr rs1 rd := by
  obtain ⟨r⟩ := rs1
  obtain ⟨d⟩ := rd
  cases csr <;> by_cases hr : r = 0 <;> by_cases hd : d = 0 <;> by_cases hdr : d = r <;>
    (try subst hr) <;> (try subst hd) <;>
    simp_all [csrrcProgramAuto, csrrcProgram, csrBitUpdateProgram, csrReadInto, isX0_regidx,
      regidx_beq, sameXReg, pureWritebackRdZeroProgram, Encoded.ANDI, Encoded.ADDI,
      SystemCSR.vreg, mstatusVReg, trapHandlerVReg, mscratchVReg, mepcVReg, mcauseVReg,
      mtvalVReg, inlineTmp0, inlineTmp, inlineRegisterBase,
      riscvRegisterBase, riscvRegisterCount, numReservedVirtualRegisters] <;> decide

end JoltISA
