/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/


import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.VirtualRegisters


open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust load `v0`: effective address, then byte/halfword/word shift amount. -/
def loadV0 : VReg := inlineTmp0

/-- Rust load `v1`: aligned doubleword address, then loaded/shifted doubleword. -/
def loadV1 : VReg := inlineTmp1

/-- Recursive `SLL`/`SRL` scratch while Rust load `v0,v1` guards are live. -/
def loadInlineTmp : VReg := inlineTmp2

/-- Rust source `rd = x0` rewrite destination for side-effecting load
expansions. -/
def loadDstFor (rd : regidx) : Dst :=
  sideEffectingRdZeroDst rd

/-- Rust load `v0`, shifted when `rd = x0` consumes the first temporary. -/
def loadV0For (rd : regidx) : VReg :=
  if isX0 rd then inlineTmp1 else loadV0

/-- Rust load `v1`, shifted when `rd = x0` consumes the first temporary. -/
def loadV1For (rd : regidx) : VReg :=
  if isX0 rd then inlineTmp2 else loadV1

/-- Recursive load scratch, shifted when `rd = x0` consumes the first
temporary. -/
def loadInlineTmpFor (rd : regidx) : VReg :=
  if isX0 rd then inlineTmp3 else loadInlineTmp

end JoltISA
