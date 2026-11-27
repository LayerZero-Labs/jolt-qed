/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari, Quang Dao
-/
import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.SystemCSR

/-!
# Hand-written Jolt-ISA expansion programs

Every expansion program is either generated into `ExpansionsAutomated.lean` by
Jolt's `jolt-lean-gen` or written by hand in this file.
This file holds only the expansions the generator cannot produce yet.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

namespace JoltISA

/-! ## Immediate CSR forms

FIXME: This needs to be translated.
CSRRWI, CSRRSI and CSRRCI are written by hand because Jolt's Lean generator
(`crates/jolt-lean-gen`) cannot produce them yet: Jolt computes a mask from the
5-bit immediate before it emits rows, so one sample instruction does not show
the rows for every immediate.
Each definition below transcribes Jolt's Rust at `504dd78a2`.
-/

/-- Jolt's `emit_csr_read` (`crates/jolt-program/src/expand/control_flow/csr.rs`):
copy the CSR's virtual register into `rd`, then run `next`.
Reading mstatus also sets bits 12:11 (MPP = Machine).
Jolt's callers skip the read when `rd = x0`; this definition folds that test in.
For example, `csrReadInto .mstatus x5 next` is `ORI x5, v39, 0x1800` followed by `next`.

FIXME: This needs to be translated. -/
def csrReadInto (csr : SystemCSR) (rd : regidx) (next : Program) : Program :=
  if isX0 rd then next
  else if csr = .mstatus then
    .instr (.ORI (.xreg rd) (.vreg (SystemCSR.vreg csr)) 0x1800) next
  else
    .instr (.ADDI (.xreg rd) (.vreg (SystemCSR.vreg csr)) 0) next

/-- Jolt's `expand_csrrwi` (`crates/jolt-program/src/expand/control_flow/csr_immediate.rs`).
`uimm` is the 5-bit immediate, zero-extended to 64 bits as `bits`.
Jolt reads the old CSR into `rd` (unless `rd = x0`), then writes the legal part
of `bits`: mstatus keeps only MIE and MPIE (`0x88`), mepc clears bit 0, and an
mtvec write with the reserved MODE bit 1 keeps the old MODE and writes only BASE.
For example, `csrrwiProgram .mstatus 9 x0` is the single row `ADDI v39, x0, 8`.

FIXME: This needs to be translated. -/
def csrrwiProgram (csr : SystemCSR) (uimm : BitVec 5) (rd : regidx) : Program :=
  let vr := SystemCSR.vreg csr
  let bits := uimm.zeroExtend 64
  csrReadInto csr rd <|
  match csr with
  | .mstatus =>
    .instr (.ADDI (.vreg vr) (.xreg (regidx.Regidx 0)) (bits &&& 0x88)) <|
    .done RETIRE_SUCCESS
  | .mepc =>
    .instr (.ADDI (.vreg vr) (.xreg (regidx.Regidx 0)) (bits &&& ~~~1)) <|
    .done RETIRE_SUCCESS
  | .mtvec =>
    if bits &&& 2 != 0 then
      .instr (.ANDI (.vreg vr) (.vreg vr) 1) <|
      if bits &&& ~~~3 != 0 then
        .instr (.ORI (.vreg vr) (.vreg vr) (bits &&& ~~~3)) <|
        .done RETIRE_SUCCESS
      else .done RETIRE_SUCCESS
    else
      .instr (.ADDI (.vreg vr) (.xreg (regidx.Regidx 0)) bits) <|
      .done RETIRE_SUCCESS
  | _ =>
    .instr (.ADDI (.vreg vr) (.xreg (regidx.Regidx 0)) bits) <|
    .done RETIRE_SUCCESS

/-- The mask Jolt's `expand_bit_update` computes from the immediate
(`crates/jolt-program/src/expand/control_flow/csr_immediate.rs`).
`clear = false` is CSRRSI (set bits), `clear = true` is CSRRCI (clear bits).
mstatus keeps only MIE and MPIE (`0x88`) and mepc clears bit 0.
For mtvec, a set with the reserved MODE bit 1 clears bits 0 and 1;
otherwise bit 1 is cleared.
For example, `csrImmediateMask false .mstatus 9` is `8`.

FIXME: This needs to be translated. -/
def csrImmediateMask (clear : Bool) (csr : SystemCSR) (uimm : BitVec 5) : BitVec 64 :=
  let bits := uimm.zeroExtend 64
  match csr with
  | .mstatus => bits &&& 0x88
  | .mepc => bits &&& ~~~1
  | .mtvec =>
    if !clear && (bits &&& 2 != 0) then bits &&& ~~~3
    else bits &&& ~~~2
  | _ => bits

/-- Jolt's `expand_bit_update` (`crates/jolt-program/src/expand/control_flow/csr_immediate.rs`),
shared by CSRRSI (`clear = false`) and CSRRCI (`clear = true`).
Jolt reads the old CSR into `rd` (unless `rd = x0`); then, if the mask from
`csrImmediateMask` is nonzero, it sets the mask bits with ORI or clears them
with ANDI and the complement. A zero mask writes nothing, and with `rd = x0`
emits the no-op `ADDI x0, x0, 0` instead.
For example, `csrImmediateBitUpdateProgram false .mstatus 1 x0` is the no-op,
because bit 0 of mstatus is not writable.

FIXME: This needs to be translated. -/
def csrImmediateBitUpdateProgram
    (clear : Bool) (csr : SystemCSR) (uimm : BitVec 5) (rd : regidx) : Program :=
  let vr := SystemCSR.vreg csr
  let mask := csrImmediateMask clear csr uimm
  csrReadInto csr rd <|
  if mask != 0 then
    .instr (if clear then .ANDI (.vreg vr) (.vreg vr) (~~~mask)
      else .ORI (.vreg vr) (.vreg vr) mask) <|
    .done RETIRE_SUCCESS
  else if isX0 rd then
    pureWritebackRdZeroProgram
  else .done RETIRE_SUCCESS

/-- Jolt's CSRRSI expansion (`expand_csrrsi`): set the immediate's legal bits.
For example, `csrrsiProgram .mstatus 8 x0` is the single row `ORI v39, v39, 8`.

FIXME: This needs to be translated. -/
def csrrsiProgram (csr : SystemCSR) (uimm : BitVec 5) (rd : regidx) : Program :=
  csrImmediateBitUpdateProgram false csr uimm rd

/-- Jolt's CSRRCI expansion (`expand_csrrci`): clear the immediate's legal bits.
For example, `csrrciProgram .mstatus 8 x0` is the single row `ANDI v39, v39, ~~~8`.

FIXME: This needs to be translated. -/
def csrrciProgram (csr : SystemCSR) (uimm : BitVec 5) (rd : regidx) : Program :=
  csrImmediateBitUpdateProgram true csr uimm rd

end JoltISA
