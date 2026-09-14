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

def readSrc : Src → JoltMonad (BitVec 64)
  | .vreg vr => readVReg vr
  | .xreg rs => liftSail (rX_bits rs)

def writeDst : Dst → BitVec 64 → JoltMonad Unit
  | .vreg vr, value => writeVReg vr value
  | .xreg rd, value => liftSail (wX_bits rd value)

end JoltISA

end
