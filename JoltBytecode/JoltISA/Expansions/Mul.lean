/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/


import JoltBytecode.JoltISA.Instruction
import JoltBytecode.JoltISA.VirtualRegisters

/-!
# M-extension Jolt expansion programs


-/

open Sail PreSail LeanRV64D.Functions

namespace JoltISA

/-- Rust's `MULH::inline_sequence` as a reusable block.

The caller supplies the three scratch virtual registers from the active
allocator.  This matters when `MULH` appears inside another source
instruction's inline sequence. -/
def mulhBlock (v_sx v_sy v_tmp : VReg)
    (dst : Dst) (lhs rhs : Src) (tail : Program) : Program :=
  .instr (.VirtualMovsign (.vreg v_sx) lhs) <|
  .instr (.VirtualMovsign (.vreg v_sy) rhs) <|
  .instr (.MUL (.vreg v_sx) (.vreg v_sx) rhs) <|
  .instr (.MUL (.vreg v_sy) (.vreg v_sy) lhs) <|
  .instr (.MULHU (.vreg v_tmp) lhs rhs) <|
  .instr (.ADD (.vreg v_tmp) (.vreg v_tmp) (.vreg v_sx)) <|
  .instr (.ADD dst (.vreg v_tmp) (.vreg v_sy)) <|
  tail

end JoltISA
