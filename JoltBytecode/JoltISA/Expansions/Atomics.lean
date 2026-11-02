/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/

import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Expansions.AtomicRegisters
import JoltBytecode.JoltISA.Expansions.LaneWindow
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

def amoWordSwapMaskVRegFor (rd : regidx) : VReg := amoVRegFor rd 0
def amoWordSwapDwordVRegFor (rd : regidx) : VReg := amoVRegFor rd 1
def amoWordSwapShiftVRegFor (rd : regidx) : VReg := amoVRegFor rd 2
def amoWordSwapOldVRegFor (rd : regidx) : VReg := amoVRegFor rd 3
def amoWordSwapInlineTmpVRegFor (rd : regidx) : VReg := amoVRegFor rd 4

/-- Open a word lane and extract its sign-extended value, following
`LaneWindow::open` and `LaneWindow::extract` in
`crates/jolt-program/src/expand/memory/shared.rs`.
For example, an address ending in 4 selects the upper word of `dword`.
The three scratch registers hold the old word, containing doubleword and mask. -/
def amoPre64ProgramWithScratch
    (rs1 : regidx) (old dword lane : VReg) (tail : Program) :
    Program :=
  laneWindowOpen .word (.vreg dword) (.vreg lane) (.xreg rs1) 0 .amo
    (ExceptionType.E_SAMO_Addr_Align ()) <|
  laneWindowExtract (.vreg dword) (.vreg lane) (.vreg old) true tail

/-- Shared word-AMO prelude with explicit scratch registers.
For example, binops and swaps use the same three-row load, mask and extract. -/
def amoPre64Program (rs1 : regidx) (old dword lane : VReg) (tail : Program) :
    Program :=
  amoPre64ProgramWithScratch rs1 old dword lane tail

/-- Containing-doubleword register in `expand_amo_w` and `expand_amo_minmax_w`
in `crates/jolt-program/src/expand/memory/shared.rs`; for a nonzero destination
this is the first temporary. -/
def amoWordDwordVRegFor (rd : regidx) : VReg := amoVRegFor rd 0

/-- Lane-mask register allocated second by the shared word-AMO expansion.
For example, it holds `0xffffffff00000000` for the upper word. -/
def amoWordLaneVRegFor (rd : regidx) : VReg := amoVRegFor rd 1

/-- Old-word register allocated third by the shared word-AMO expansion.
For example, a loaded word of `0xffffffff` is held sign-extended to 64 bits. -/
def amoWordOldVRegFor (rd : regidx) : VReg := amoVRegFor rd 2

/-- Result register allocated fourth by the shared word-AMO expansion.
For example, ADD writes the sum of the old word and `rs2` here. -/
def amoWordNewVRegFor (rd : regidx) : VReg := amoVRegFor rd 3

/-- Comparison flag allocated fifth by the shared word-AMO select expansion.
For example, one means that a min operation selects the new value. -/
def amoWordTakeVRegFor (rd : regidx) : VReg := amoVRegFor rd 4

/-- Merge a new word through `LaneWindow::merge`, then copy the already
sign-extended old word to the destination, as in `expand_amo_w` in
`crates/jolt-program/src/expand/memory/shared.rs`.
For example, a swap passes its architectural source as `newValue`. -/
def amoWordMergeProgram (rs1 rd : regidx) (newValue : Src)
    (dword lane old : VReg) : Program :=
  laneWindowMerge .word (.vreg dword) (.vreg lane) (.xreg rs1) 0 newValue
    (ExceptionType.E_SAMO_Addr_Align ()) <|
  .instr (Encoded.ADDI (amoDstFor rd) (.vreg old) 0) <|
  .done RETIRE_SUCCESS

/-- Shared Rust `amo_post64`: splice `newValue` into the containing doubleword,
store it back, and sign-extend the old word into `rd`.

The final argument is the scratch register allocated by each recursive `SLL`
inline expansion inside the postlude. -/
def amoPost64ProgramWithScratch
    (rs1 rd : regidx) (newValue : Src) (dword shift mask old inlineTmp : VReg) :
    Program :=
  let dst := amoDstFor rd
  .instr (JoltISA.Encoded.ORI (.vreg mask) (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
  .instr (.VirtualSRLI (.vreg mask) (.vreg mask) (srliBitmask (32 : BitVec 6))) <|
  .instr (.VirtualPow2 (.vreg inlineTmp) (.vreg shift) (0 : BitVec 64)) <|
  .instr (.MUL (.vreg mask) (.vreg mask) (.vreg inlineTmp)) <|
  .instr (.VirtualPow2 (.vreg inlineTmp) (.vreg shift) (0 : BitVec 64)) <|
  .instr (.MUL (.vreg shift) newValue (.vreg inlineTmp)) <|
  .instr (.XOR (.vreg shift) (.vreg dword) (.vreg shift)) <|
  .instr (.AND (.vreg shift) (.vreg shift) (.vreg mask)) <|
  .instr (.XOR (.vreg dword) (.vreg dword) (.vreg shift)) <|
  .instr (JoltISA.Encoded.ANDI (.vreg mask) (.xreg rs1) (-8 : BitVec 12)) <|
  .instr (JoltISA.Encoded.SD (.vreg mask) (.vreg dword) (0 : BitVec 12)) <|
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
  .instr (JoltISA.Encoded.LD .amo (.vreg old) (.xreg rs1) (0 : BitVec 12)) <|
  .instr (op (.vreg new) (.vreg old) (.xreg rs2)) <|
  .instr (JoltISA.Encoded.SD (.xreg rs1) (.vreg new) (0 : BitVec 12)) <|
  .instr (JoltISA.Encoded.ADDI dst (.vreg old) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

def amoDoubleSelectProgram
    (cmpInstr : Dst → Src → Src → Instr) (cmpLhs cmpRhs : Src)
    (rs2 rs1 rd : regidx) : Program :=
  let old := amoOldVRegFor rd
  let new := amoNewVRegFor rd
  let tmp := amoTmpVRegFor rd
  let dst := amoDstFor rd
  .instr (JoltISA.Encoded.LD .amo (.vreg old) (.xreg rs1) (0 : BitVec 12)) <|
  .instr (cmpInstr (.vreg new) cmpLhs cmpRhs) <|
  .instr (.SUB (.vreg tmp) (.xreg rs2) (.vreg old)) <|
  .instr (.MUL (.vreg tmp) (.vreg tmp) (.vreg new)) <|
  .instr (.ADD (.vreg new) (.vreg old) (.vreg tmp)) <|
  .instr (JoltISA.Encoded.SD (.xreg rs1) (.vreg new) (0 : BitVec 12)) <|
  .instr (JoltISA.Encoded.ADDI dst (.vreg old) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

/-- Shared `expand_amo_w` shape in `crates/jolt-program/src/expand/memory/shared.rs`.
For example, supplying `Instr.ADD` gives the word-add expansion. -/
def amoWordBinopProgram
    (op : Dst → Src → Src → Instr) (rs2 rs1 rd : regidx) : Program :=
  let old := amoWordOldVRegFor rd
  let new := amoWordNewVRegFor rd
  let dword := amoWordDwordVRegFor rd
  let lane := amoWordLaneVRegFor rd
  amoPre64Program rs1 old dword lane <|
  .instr (op (.vreg new) (.vreg old) (.xreg rs2)) <|
  amoWordMergeProgram rs1 rd (.vreg new) dword lane old

/-- Shared `expand_amo_minmax_w` shape in
`crates/jolt-program/src/expand/memory/shared.rs`, parameterized by the source
extension, comparison and comparison operands.
For example, signed min compares the extended new word against the old word. -/
def amoWordSelectRustProgram
    (extend : Dst → Src → Instr) (cmpInstr : Dst → Src → Src → Instr)
    (cmpLhs cmpRhs : Src) (rs2 rs1 rd : regidx) : Program :=
  let old := amoWordOldVRegFor rd
  let dword := amoWordDwordVRegFor rd
  let lane := amoWordLaneVRegFor rd
  let new := amoWordNewVRegFor rd
  let take := amoWordTakeVRegFor rd
  amoPre64Program rs1 old dword lane <|
  .instr (extend (.vreg new) (.xreg rs2)) <|
  .instr (cmpInstr (.vreg take) cmpLhs cmpRhs) <|
  .instr (.SUB (.vreg new) (.xreg rs2) (.vreg old)) <|
  .instr (.MUL (.vreg new) (.vreg new) (.vreg take)) <|
  .instr (.ADD (.vreg new) (.vreg new) (.vreg old)) <|
  amoWordMergeProgram rs1 rd (.vreg new) dword lane old

end JoltISA
