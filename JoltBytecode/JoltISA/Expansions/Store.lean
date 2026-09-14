/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/


import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.VirtualRegisters

/-!
# Store-family Jolt expansion support

NOTE: (for Ari) the triangle in examples such as
`.instr i <| .instr j <| .done RETIRE_SUCCESS` is Lean's left-facing pipeline
operator.  Here it lets the bytecode list read top-to-bottom: execute `i`, then
execute `j`, then retire.

-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust store `v0`: effective address. -/
def storeV0 : VReg := inlineTmp0

/-- Rust store `v1`: aligned doubleword base address. -/
def storeV1 : VReg := inlineTmp1

/-- Rust store `v2`: loaded/spliced doubleword. -/
def storeV2 : VReg := inlineTmp2

/-- Rust store `v3`: window mask, then shifted store data. -/
def storeV3 : VReg := inlineTmp3

end JoltISA
