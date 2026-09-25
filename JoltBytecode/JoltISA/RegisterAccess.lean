/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/

import JoltBytecode.JoltISA.Core
import JoltBytecode.JoltISA.Instruction

/-!
# Accessing data in registers

Monadic access primitives for the Jolt register file:

* `readVReg` / `writeVReg` — virtual-register access on the per-instruction
  `vregs` table (indices 0–31 are protected, used via `xreg` instead).
* `readSrc` / `writeDst` — dispatch on `Src`/`Dst` to the appropriate
  vreg vs. architectural-register backend.
* `WritableVReg` — predicate for the writable half of the vreg index space.

Proof-side facts about these defs (run-unfolds, `_vreg`/`_xreg` rfl-laws) live
in `InstructionEquivalence/ProofSupport/RegisterAccess.lean`.
-/

set_option linter.unusedVariables true

open Sail PreSail LeanRV64D.Functions

noncomputable section

abbrev VReg := BitVec 7

-- Get the value in vr as a monadic computation
def readVReg (vr : VReg) : JoltMonad (BitVec 64) := do
  let js ← get
  pure (js.vregs vr)

-- The general purpose registers are in the Sail hashmap already
-- so we should never write to vr 0-31
def WritableVReg (vr : VReg) : Prop :=
  ¬ vr.toNat < 32

-- We cannot write the to the first 32 registers, as we use xreg for them.
def writeVReg (vr : VReg) (val : BitVec 64) : JoltMonad Unit :=
  if vr.toNat < 32 then
    throw (Error.Assertion "writeVReg: architectural xreg address")
  else
    modify fun js => { js with vregs := fun r => if r = vr then val else js.vregs r }

namespace JoltISA

/-- Read an operand value directly from a state. Missing architectural registers
default to zero; instruction execution still uses `readSrc` to reject missing operands.
On a successful operand read, this returns exactly the value read by execution. -/
-- WARNING: (ari) maybe put a guard or proof around the range of src
def sourceValue (src : Src) (state : SailJoltState) : BitVec 64 :=
  match src with
  | .vreg vr => state.vregs vr
  | .xreg (.Regidx rs) =>
      match rs.toNat with
      | 0 => 0
      | 1 => (state.sail.regs.get? Register.x1).getD 0
      | 2 => (state.sail.regs.get? Register.x2).getD 0
      | 3 => (state.sail.regs.get? Register.x3).getD 0
      | 4 => (state.sail.regs.get? Register.x4).getD 0
      | 5 => (state.sail.regs.get? Register.x5).getD 0
      | 6 => (state.sail.regs.get? Register.x6).getD 0
      | 7 => (state.sail.regs.get? Register.x7).getD 0
      | 8 => (state.sail.regs.get? Register.x8).getD 0
      | 9 => (state.sail.regs.get? Register.x9).getD 0
      | 10 => (state.sail.regs.get? Register.x10).getD 0
      | 11 => (state.sail.regs.get? Register.x11).getD 0
      | 12 => (state.sail.regs.get? Register.x12).getD 0
      | 13 => (state.sail.regs.get? Register.x13).getD 0
      | 14 => (state.sail.regs.get? Register.x14).getD 0
      | 15 => (state.sail.regs.get? Register.x15).getD 0
      | 16 => (state.sail.regs.get? Register.x16).getD 0
      | 17 => (state.sail.regs.get? Register.x17).getD 0
      | 18 => (state.sail.regs.get? Register.x18).getD 0
      | 19 => (state.sail.regs.get? Register.x19).getD 0
      | 20 => (state.sail.regs.get? Register.x20).getD 0
      | 21 => (state.sail.regs.get? Register.x21).getD 0
      | 22 => (state.sail.regs.get? Register.x22).getD 0
      | 23 => (state.sail.regs.get? Register.x23).getD 0
      | 24 => (state.sail.regs.get? Register.x24).getD 0
      | 25 => (state.sail.regs.get? Register.x25).getD 0
      | 26 => (state.sail.regs.get? Register.x26).getD 0
      | 27 => (state.sail.regs.get? Register.x27).getD 0
      | 28 => (state.sail.regs.get? Register.x28).getD 0
      | 29 => (state.sail.regs.get? Register.x29).getD 0
      | 30 => (state.sail.regs.get? Register.x30).getD 0
      | _ => (state.sail.regs.get? Register.x31).getD 0

def readSrc : Src → JoltMonad (BitVec 64)
  | .vreg vr => readVReg vr
  | .xreg rs => liftSail (rX_bits rs)

def writeDst : Dst → BitVec 64 → JoltMonad Unit
  | .vreg vr, value => writeVReg vr value
  | .xreg rd, value => liftSail (wX_bits rd value)

end JoltISA

end
