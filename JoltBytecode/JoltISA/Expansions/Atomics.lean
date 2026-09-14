/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/

import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.VirtualRegisters

/-!
# Atomic Jolt expansion programs

Small wrappers around atomic expansions that make proof writing a little bit more 
ergonomic.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust `v_rd`/`v0`: old AMO value for dword select and word binop paths. -/
def amoOldVReg : VReg := inlineTmp0

/-- Rust `v1`/`v_rs2`: computed AMO value for dword select and word binop paths. -/
def amoNewVReg : VReg := inlineTmp1

/-- Rust `v2`: temporary delta/product register in dword select paths. -/
def amoTmpVReg : VReg := inlineTmp2

/-- Rust `v_mask` for word binop paths. -/
def amoMaskVReg : VReg := inlineTmp2

/-- Rust `v_dword` for word binop paths. -/
def amoDwordVReg : VReg := inlineTmp3

/-- Rust `v_shift` for word binop paths. -/
def amoShiftVReg : VReg := inlineTmp4

/-- Recursive `SRL`/`SLL` scratch after the word-binop outer registers. -/
def amoInlineTmpVReg : VReg := inlineTmp5

/-- Rust `v_rs2`: computed result register for dword binop paths. -/
def amoDoubleBinopNewVReg : VReg := inlineTmp0

/-- Rust `v_rd`: loaded old value register for dword binop paths. -/
def amoDoubleBinopOldVReg : VReg := inlineTmp1

/-- Rust `v_mask` for `AMOSWAP.W` RV64. -/
def amoWordSwapMaskVReg : VReg := inlineTmp0

/-- Rust `v_dword` for `AMOSWAP.W` RV64. -/
def amoWordSwapDwordVReg : VReg := inlineTmp1

/-- Rust `v_shift` for `AMOSWAP.W` RV64. -/
def amoWordSwapShiftVReg : VReg := inlineTmp2

/-- Rust `v_rd` for `AMOSWAP.W` RV64. -/
def amoWordSwapOldVReg : VReg := inlineTmp3

/-- Recursive `SRL`/`SLL` scratch after the `AMOSWAP.W` RV64 outer registers. -/
def amoWordSwapInlineTmpVReg : VReg := inlineTmp4

/-- Rust `v_rd` for word min/max RV64 paths. -/
def amoWordSelectOldVReg : VReg := inlineTmp0

/-- Rust `v_dword` for word min/max RV64 paths. -/
def amoWordSelectDwordVReg : VReg := inlineTmp1

/-- Rust `v_shift` for word min/max RV64 paths. -/
def amoWordSelectShiftVReg : VReg := inlineTmp2

/-- Rust `v_rs2` for word min/max RV64 paths. -/
def amoWordSelectNewVReg : VReg := inlineTmp3

/-- Rust `v0`, reused as the postlude mask, for word min/max RV64 paths. -/
def amoWordSelectMaskVReg : VReg := inlineTmp4

/-- Recursive `SRL`/`SLL` scratch after the word-select outer registers. -/
def amoWordSelectInlineTmpVReg : VReg := inlineTmp5

/-- Rust source `rd = x0` rewrite destination for side-effecting AMO
expansions. -/
def amoDstFor (rd : regidx) : Dst :=
  sideEffectingRdZeroDst rd

/-- Rust AMO scratch slot `n`, shifted when `rd = x0` consumes the first
temporary. -/
def amoVRegFor (rd : regidx) (n : Nat) : VReg :=
  if isX0 rd then inlineTmp (n + 1) else inlineTmp n

def amoOldVRegFor (rd : regidx) : VReg := amoVRegFor rd 0
def amoNewVRegFor (rd : regidx) : VReg := amoVRegFor rd 1
def amoTmpVRegFor (rd : regidx) : VReg := amoVRegFor rd 2
def amoMaskVRegFor (rd : regidx) : VReg := amoVRegFor rd 2
def amoDwordVRegFor (rd : regidx) : VReg := amoVRegFor rd 3
def amoShiftVRegFor (rd : regidx) : VReg := amoVRegFor rd 4
def amoInlineTmpVRegFor (rd : regidx) : VReg := amoVRegFor rd 5

def amoDoubleBinopNewVRegFor (rd : regidx) : VReg := amoVRegFor rd 0
def amoDoubleBinopOldVRegFor (rd : regidx) : VReg := amoVRegFor rd 1

def amoWordSwapMaskVRegFor (rd : regidx) : VReg := amoVRegFor rd 0
def amoWordSwapDwordVRegFor (rd : regidx) : VReg := amoVRegFor rd 1
def amoWordSwapShiftVRegFor (rd : regidx) : VReg := amoVRegFor rd 2
def amoWordSwapOldVRegFor (rd : regidx) : VReg := amoVRegFor rd 3
def amoWordSwapInlineTmpVRegFor (rd : regidx) : VReg := amoVRegFor rd 4

def amoWordSelectOldVRegFor (rd : regidx) : VReg := amoVRegFor rd 0
def amoWordSelectDwordVRegFor (rd : regidx) : VReg := amoVRegFor rd 1
def amoWordSelectShiftVRegFor (rd : regidx) : VReg := amoVRegFor rd 2
def amoWordSelectNewVRegFor (rd : regidx) : VReg := amoVRegFor rd 3
def amoWordSelectMaskVRegFor (rd : regidx) : VReg := amoVRegFor rd 4
def amoWordSelectInlineTmpVRegFor (rd : regidx) : VReg := amoVRegFor rd 5

/-- Shared Rust `amo_pre64`: assert word alignment, load the containing
doubleword, then extract the addressed word into `old`.

The final argument is the scratch register allocated by the recursive `SRL`
inline expansion at that call site. -/
def amoPre64ProgramWithScratch
    (rs1 : regidx) (old dword shift inlineTmp : VReg) (tail : Program) :
    Program :=
  .instr (.VirtualAssertWordAlignment rs1 (0 : BitVec 12) (ExceptionType.E_SAMO_Addr_Align ())) <|
  .instr (.ANDI (.vreg shift) (.xreg rs1) (-8 : BitVec 12)) <|
  .instr (.LD .amo (.vreg dword) (.vreg shift) (0 : BitVec 12)) <|
  .instr (.VirtualMULI (.vreg shift) (.xreg rs1) (8 : BitVec 64)) <|
  .instr (.VirtualShiftRightBitmask (.vreg inlineTmp) (.vreg shift)) <|
  .instr (.VirtualSRL (.vreg old) (.vreg dword) (.vreg inlineTmp)) <|
  tail

/-- Word-binop instance of Rust `amo_pre64`, where the recursive `SRL`
scratch is the first register after `v_rd`, `v_rs2`, `v_mask`, `v_dword`, and
`v_shift`. -/
def amoPre64Program (rs1 : regidx) (old dword shift : VReg) (tail : Program) :
    Program :=
  amoPre64ProgramWithScratch rs1 old dword shift amoInlineTmpVReg tail

/-- Shared Rust `amo_post64`: splice `newValue` into the containing doubleword,
store it back, and sign-extend the old word into `rd`.

The final argument is the scratch register allocated by each recursive `SLL`
inline expansion inside the postlude. -/
def amoPost64ProgramWithScratch
    (rs1 rd : regidx) (newValue : Src) (dword shift mask old inlineTmp : VReg) :
    Program :=
  let dst := amoDstFor rd
  .instr (.ORI (.vreg mask) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
  .instr (.VirtualSRLI (.vreg mask) (.vreg mask) (srliBitmask (32 : BitVec 6))) <|
  .instr (.VirtualPow2 (.vreg inlineTmp) (.vreg shift)) <|
  .instr (.MUL (.vreg mask) (.vreg mask) (.vreg inlineTmp)) <|
  .instr (.VirtualPow2 (.vreg inlineTmp) (.vreg shift)) <|
  .instr (.MUL (.vreg shift) newValue (.vreg inlineTmp)) <|
  .instr (.XOR (.vreg shift) (.vreg dword) (.vreg shift)) <|
  .instr (.AND (.vreg shift) (.vreg shift) (.vreg mask)) <|
  .instr (.XOR (.vreg dword) (.vreg dword) (.vreg shift)) <|
  .instr (.ANDI (.vreg mask) (.xreg rs1) (-8 : BitVec 12)) <|
  .instr (.SD (.vreg mask) (.vreg dword) (0 : BitVec 12)) <|
  .instr (.VirtualSignExtendWord dst (.vreg old)) <|
  .done RETIRE_SUCCESS

/-- Word-binop instance of Rust `amo_post64`, where recursive `SLL` calls reuse
the first register after the word-binop outer temporaries. -/
def amoPost64Program
    (rs1 rd : regidx) (newValue : Src) (dword shift mask old : VReg) : Program :=
  amoPost64ProgramWithScratch rs1 rd newValue dword shift mask old
    amoInlineTmpVReg

def amoDoubleBinopProgram
    (op : Dst → Src → Src → Instr) (rs2 rs1 rd : regidx) : Program :=
  let old := amoDoubleBinopOldVRegFor rd
  let new := amoDoubleBinopNewVRegFor rd
  let dst := amoDstFor rd
  .instr (.LD .amo (.vreg old) (.xreg rs1) (0 : BitVec 12)) <|
  .instr (op (.vreg new) (.vreg old) (.xreg rs2)) <|
  .instr (.SD (.xreg rs1) (.vreg new) (0 : BitVec 12)) <|
  .instr (.ADDI dst (.vreg old) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

def amoDoubleSelectProgram
    (cmpInstr : Dst → Src → Src → Instr) (cmpLhs cmpRhs : Src)
    (rs2 rs1 rd : regidx) : Program :=
  let old := amoOldVRegFor rd
  let new := amoNewVRegFor rd
  let tmp := amoTmpVRegFor rd
  let dst := amoDstFor rd
  .instr (.LD .amo (.vreg old) (.xreg rs1) (0 : BitVec 12)) <|
  .instr (cmpInstr (.vreg new) cmpLhs cmpRhs) <|
  .instr (.SUB (.vreg tmp) (.xreg rs2) (.vreg old)) <|
  .instr (.MUL (.vreg tmp) (.vreg tmp) (.vreg new)) <|
  .instr (.ADD (.vreg new) (.vreg old) (.vreg tmp)) <|
  .instr (.SD (.xreg rs1) (.vreg new) (0 : BitVec 12)) <|
  .instr (.ADDI dst (.vreg old) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

def amoWordBinopProgram
    (op : Dst → Src → Src → Instr) (rs2 rs1 rd : regidx) : Program :=
  let old := amoOldVRegFor rd
  let new := amoNewVRegFor rd
  let mask := amoMaskVRegFor rd
  let dword := amoDwordVRegFor rd
  let shift := amoShiftVRegFor rd
  let tmp := amoInlineTmpVRegFor rd
  amoPre64ProgramWithScratch rs1 old dword shift tmp <|
  .instr (op (.vreg new) (.vreg old) (.xreg rs2)) <|
  amoPost64ProgramWithScratch rs1 rd (.vreg new)
    dword shift mask old tmp

def amoWordSelectProgram
    (extend : Dst → Src → Instr) (cmpInstr : Dst → Src → Src → Instr)
    (cmpLhs cmpRhs : Src) (rs2 rs1 rd : regidx) : Program :=
  let old := amoOldVRegFor rd
  let new := amoNewVRegFor rd
  let mask := amoMaskVRegFor rd
  let dword := amoDwordVRegFor rd
  let shift := amoShiftVRegFor rd
  let tmp := amoInlineTmpVRegFor rd
  amoPre64ProgramWithScratch rs1 old dword shift tmp <|
  .instr (extend (.vreg new) (.xreg rs2)) <|
  .instr (extend (.vreg mask) (.vreg old)) <|
  .instr (cmpInstr (.vreg mask) cmpLhs cmpRhs) <|
  .instr (.SUB (.vreg new) (.xreg rs2) (.vreg old)) <|
  .instr (.MUL (.vreg new) (.vreg new) (.vreg mask)) <|
  .instr (.ADD (.vreg new) (.vreg new) (.vreg old)) <|
  amoPost64ProgramWithScratch rs1 rd (.vreg new)
    dword shift mask old tmp

/-- Rust-shaped RV64 word min/max helper.

Rust allocates `v_rd`, `v_dword`, and `v_shift`, runs `amo_pre64`, then reuses
the recursive prelude scratch as `v_rs2` and allocates `v0` for the comparison
flag and later postlude mask. -/
def amoWordSelectRustProgram
    (extend : Dst → Src → Instr) (cmpInstr : Dst → Src → Src → Instr)
    (cmpLhs cmpRhs : Src) (rs2 rs1 rd : regidx) : Program :=
  let old := amoWordSelectOldVRegFor rd
  let dword := amoWordSelectDwordVRegFor rd
  let shift := amoWordSelectShiftVRegFor rd
  let new := amoWordSelectNewVRegFor rd
  let mask := amoWordSelectMaskVRegFor rd
  let tmp := amoWordSelectInlineTmpVRegFor rd
  amoPre64ProgramWithScratch rs1
    old dword shift new <|
  .instr (extend (.vreg new) (.xreg rs2)) <|
  .instr (extend (.vreg mask) (.vreg old)) <|
  .instr (cmpInstr (.vreg mask) cmpLhs cmpRhs) <|
  .instr (.SUB (.vreg new) (.xreg rs2) (.vreg old)) <|
  .instr (.MUL (.vreg new) (.vreg new) (.vreg mask)) <|
  .instr (.ADD (.vreg new) (.vreg new) (.vreg old)) <|
  amoPost64ProgramWithScratch rs1 rd (.vreg new)
    dword shift mask old tmp

end JoltISA
