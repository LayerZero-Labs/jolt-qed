/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/


import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.JoltISA.VirtualRegisters

/-!
# Load-reserved Jolt expansion programs

These are the Jolt-ISA data-level programs for the RV64 load-reserved
instructions. They mirror the Rust tracer sources:

* `tracer/src/instruction/lrw.rs::inline_sequence_64`
* `tracer/src/instruction/lrd.rs::inline_sequence`

The LR trace rows update the persistent reservation virtual registers before
performing the ordinary Jolt-side load. The Sail theorem bridges that ordinary
load trace to Sail's reserved-load semantics.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- First temporary register used by the inlined RV64 `LW` tail. -/
def lrwAddrVReg : VReg := inlineTmp0

/-- Second temporary register used by the inlined RV64 `LW` tail. -/
def lrwDwordVReg : VReg := inlineTmp1

/-- Scratch register used by the inlined RV64 `SRL` tail inside `LW`. -/
def lrwShiftMaskVReg : VReg := inlineTmp2

/-- Rust-facing RV64 `LR.W` expansion surface.

Faithful to `lrw.rs::inline_sequence_64`:

1. write `rs1` into `reservation_w`;
2. clear `reservation_d`;
3. emit the RV64 `LW` inline sequence at offset zero. -/
def lrwProgram (rs1 rd : regidx) : Program :=
  .instr (.ADDI (.vreg reservationWReg) (.xreg rs1) (0 : BitVec 12)) <|
  .instr (.ADDI (.vreg reservationDReg) (.xreg (regidx.Regidx 0)) (0 : BitVec 12)) <|
  .instr (.VirtualAssertWordAlignment rs1 (0 : BitVec 12)
    (ExceptionType.E_Load_Addr_Align ())) <|
  .instr (.ADDI (.vreg lrwAddrVReg) (.xreg rs1) (0 : BitVec 12)) <|
  .instr (.ANDI (.vreg lrwDwordVReg) (.vreg lrwAddrVReg) (-8 : BitVec 12)) <|
  .instr (.LD .normal (.vreg lrwDwordVReg) (.vreg lrwDwordVReg) (0 : BitVec 12)) <|
  slliBlock (.vreg lrwAddrVReg) (.vreg lrwAddrVReg) (3 : BitVec 6) <|
  srlBlock (.vreg lrwDwordVReg) (.vreg lrwDwordVReg) (.vreg lrwAddrVReg)
    lrwShiftMaskVReg <|
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg lrwDwordVReg)) <|
  .done RETIRE_SUCCESS

/-- Rust-facing RV64 `LR.D` expansion surface.

Faithful to `lrd.rs::inline_sequence`:

1. write `rs1` into `reservation_d`;
2. write `rs1` into `reservation_w`, since an 8-byte reservation covers
   subsequent word stores at the same address;
3. emit the final Jolt-ISA `LD` row. -/
def lrdProgram (rs1 rd : regidx) : Program :=
  .instr (.ADDI (.vreg reservationDReg) (.xreg rs1) (0 : BitVec 12)) <|
  .instr (.ADDI (.vreg reservationWReg) (.xreg rs1) (0 : BitVec 12)) <|
  .instr (.LD .normal (.xreg rd) (.xreg rs1) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

end JoltISA
