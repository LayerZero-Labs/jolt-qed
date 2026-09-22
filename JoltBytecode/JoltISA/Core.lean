/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/

import LeanRV64D

/-!
# Jolt ISA core state

This module defines the Jolt CPU in Lean: the embedded Sail state, the
augmented `SailJoltState` (Sail, virtual registers, I/O and advice), the `JoltMonad`
effect type, and the lifting/projection machinery that bridges between Sail
computations and Jolt computations.
The linking between the control status registers in the virtual and sail reg 
file is described in SystemProjection.lean

Proof-side facts about this embedding live in the instruction-equivalence
support modules that use them.
-/

set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

abbrev SailState := SequentialState RegisterType trivialChoiceSource

structure JoltIOLayout where
  -- Address ranges are [start, end).
  input : BitVec 64 × BitVec 64
  trustedAdvice : BitVec 64 × BitVec 64
  untrustedAdvice : BitVec 64 × BitVec 64
  output : BitVec 64 × BitVec 64
  panic : BitVec 64 × BitVec 64
  termination : BitVec 64 × BitVec 64

structure JoltIOState where
  layout : JoltIOLayout
  inputs : Array (BitVec 8)
  trustedAdvice : Array (BitVec 8)
  untrustedAdvice : Array (BitVec 8)
  outputs : Array (BitVec 8)
  panic : Bool

structure JoltAdviceTape where
  bytes : Array (BitVec 8)
  readPosition : Nat

structure SailJoltState where
  sail : SailState
  vregs : BitVec 7 → BitVec 64 := fun _ => 0
  io : JoltIOState
  adviceTape : JoltAdviceTape

abbrev JoltMonad (α : Type) := EStateM (Error exception) SailJoltState α

-- TODO: (ari) I thought structures had natural projects (so do we need this ?)
@[simp] def project (js : SailJoltState) : SailState := js.sail

-- Replace current Sail state with new Sail State
@[simp] def inject (js : SailJoltState) (ss : SailState) : SailJoltState :=
  { js with sail := ss }

-- Given the output of a step of a Jolt CPU, return the same output as Sail CPU
-- by projecting the JoltState down to Sail State
def projectResult (r : EStateM.Result (Error exception) SailJoltState α) :
    EStateM.Result (Error exception) SailState α :=
  match r with
  | .ok a js' => .ok a (project js')
  | .error e js' => .error e (project js')

-- Have some purely Sail computation i.e computation that a RISC CPU can handle
-- but we wish to run it as a Jolt CPU computation by running the sail field of
-- the joltstate which is just a RISC CPU
def liftSail (m : SailM α) : JoltMonad α := fun js =>
  match m js.sail with
  | .ok a ss' => .ok a { js with sail := ss' }
  | .error e ss' => .error e { js with sail := ss' }

-- TODO: Common has a copy of project and System project. I am not sure if System 
-- project should also be here?

end
