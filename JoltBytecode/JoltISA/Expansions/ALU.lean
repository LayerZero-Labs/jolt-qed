/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/


import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.VirtualRegisters

/-!
# Jolt ISA ALU expansions Helpers

The full expansions are already present in ExpansionsAutomated.
In this file we often re-define blocks of the expansion to make 
theorem proving more ergonomic.

-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust `v_pow2` for `SLL` and `SLLW`. -/
abbrev aluPow2VReg : VReg := inlineTmp0

/-- Rust `v_bitmask` for `SRL` and `SRA`. -/
abbrev aluBitmaskVReg : VReg := inlineTmp0

/-- Rust `v_bitmask` for `SRLW`. -/
abbrev srlwBitmaskVReg : VReg := inlineTmp0

/-- Rust `v_rs1` for `SRLW`. -/
abbrev srlwRs1VReg : VReg := inlineTmp1

/-- Rust `v_rs1` for `SRAW`. -/
abbrev srawRs1VReg : VReg := inlineTmp0

/-- Rust `v_bitmask` for `SRAW`. -/
abbrev srawBitmaskVReg : VReg := inlineTmp1

/-- Rust `v_rs1` for `SRLIW` and `SRAIW`. -/
abbrev shiftImmediateWordRs1VReg : VReg := inlineTmp0

/-- Bitmask immediate used by RV64 `VirtualSRLI` for `SRLI`.  Its trailing-zero
count is the six-bit shift amount. -/
def srliBitmask (shamt : BitVec 6) : Nat :=
  let shift := shamt.toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

/-- Bitmask immediate used by RV64 `VirtualSRAI` for `SRAI`.  It has the same
encoding as `srliBitmask`; only the consuming virtual instruction differs. -/
def sraiBitmask (shamt : BitVec 6) : Nat :=
  srliBitmask shamt

/-- Bitmask immediate used by RV64 `VirtualSRLI` for `SRLIW`.  The source word
is first shifted left by 32, so the encoded right shift is `shamt + 32`. -/
def srliwBitmask (shamt : BitVec 5) : Nat :=
  let shift := shamt.toNat + 32
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

/-- Bitmask immediate used by RV64 `VirtualSRAI` for `SRAIW`. -/
def sraiwBitmask (shamt : BitVec 5) : Nat :=
  let shift := shamt.toNat
  let ones := (1 <<< (64 - shift)) - 1
  ones <<< shift

/-- Immediate multiplier used by Rust's `SLLI` inline sequence. -/
def slliMultiplier (shamt : BitVec 6) : BitVec 64 :=
  BitVec.ofNat 64 (2 ^ shamt.toNat)

/-- Rust `SLLI::inline_sequence`: multiply by the immediate power of two. -/
def slliBlock (dst : Dst) (src : Src) (shamt : BitVec 6) (tail : Program) : Program :=
  .instr (.VirtualMULI dst src (slliMultiplier shamt)) tail

/-- Rust `SLL::inline_sequence`: compute `2 ^ shift[5:0]` in a scratch
virtual register, then multiply the value by that power of two. -/
def sllBlock (dst : Dst) (value shift : Src) (scratch : VReg)
    (tail : Program) : Program :=
  .instr (.VirtualPow2 (.vreg scratch) shift (0 : BitVec 64)) <|
  .instr (.MUL dst value (.vreg scratch)) tail

/-- Rust `SRAI::inline_sequence`: run `VirtualSRAI` with the encoded bitmask. -/
def sraiBlock (dst : Dst) (src : Src) (shamt : BitVec 6) (tail : Program) : Program :=
  .instr (.VirtualSRAI dst src (sraiBitmask shamt)) tail

/-- Rust `SRLI::inline_sequence`: run `VirtualSRLI` with the encoded bitmask. -/
def srliBlock (dst : Dst) (src : Src) (shamt : BitVec 6) (tail : Program) : Program :=
  .instr (.VirtualSRLI dst src (srliBitmask shamt)) tail

/-- Rust `SRL::inline_sequence`: compute the right-shift bitmask in a scratch
virtual register, then run `VirtualSRL` with that bitmask. -/
def srlBlock (dst : Dst) (value shift : Src) (scratch : VReg)
    (tail : Program) : Program :=
  .instr (.VirtualShiftRightBitmask (.vreg scratch) shift) <|
  .instr (.VirtualSRL dst value (.vreg scratch)) tail

end JoltISA
