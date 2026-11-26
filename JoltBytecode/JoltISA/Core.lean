/-
Copyright (c) 2026 Ari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ari 
-/

import LeanRV64D
import JoltBytecode.JoltISA.JoltDevice

open LeanRV64D

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

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

abbrev SailState := SequentialState RegisterType trivialChoiceSource

structure JoltAdviceTape where
  bytes : Array (BitVec 8)
  readPosition : Nat

inductive JoltHostIOMode where
  | live
  | replay
  deriving DecidableEq, Repr

structure JoltHostIOConfig where
  mode : JoltHostIOMode := .live

/-- How Jolt's tracer ended a run (`HaltKind`, `tracer/src/emulator/cpu.rs:206`
at Jolt `504dd78a2`).
`success` is a normal end (the program ran `jolt.success`); `panic` is a failure.
For example, EBREAK ends the run with `panic`. -/
inductive JoltHaltKind where
  | success
  | panic
  deriving DecidableEq, Repr

structure CodeGuard where
  region : Nat × Nat
  instructions : List Nat

structure SailJoltState where
  sail : SailState
  vregs : BitVec 7 → BitVec 64 := fun _ => 0
  -- Rust: jolt/tracer/src/emulator/mmu.rs:25 (Mmu.jolt_device)
  jolt_device : JoltDevice
  adviceTape : JoltAdviceTape
  hostIO : JoltHostIOConfig := {}
  code_guard : Option CodeGuard := none
  /-- The halt that ended the run, if any (`Cpu.halted`, `tracer/src/emulator/cpu.rs:340`
  at Jolt `504dd78a2`). `none` while the program runs.
  For example, after EBREAK it is `some .panic`. -/
  halted : Option JoltHaltKind := none

namespace JoltISA

def source_word_intervals (source_extents : List (BitVec 64 × Bool)) (lowest_address : Nat) :
    Option (List (Nat × Nat)) := do
  guard (lowest_address % 8 == 0)
  (source_extents.filter fun (address, _) => address != 0).mapM fun (address, is_compressed) => do
    let stop ← MemoryLayout.checkedAdd address.toNat (if is_compressed then 2 else 4)
    let offset ← MemoryLayout.checkedSub address.toNat lowest_address
    guard (address.toNat % 2 == 0)
    pure (offset / 8, (stop - lowest_address + 7) / 8)

def code_region (source_extents : List (BitVec 64 × Bool)) (lowest_address : Nat) :
    Option (Nat × Nat) := do
  let intervals ← source_word_intervals source_extents lowest_address
  let words := intervals.foldl (fun words (start, stop) =>
    match words with
    | none => some (start, stop)
    | some (left, right) => some (min left start, max right stop)) none
  pure (words.getD (0, 0))

end JoltISA

def CodeGuard.new (sources : List (BitVec 64 × Bool)) (lowest_address : Nat) :
    Option CodeGuard := do
  let region ← JoltISA.code_region sources lowest_address
  let instructions := (sources.map fun (address, _) => address.toNat).mergeSort
  pure { region, instructions }

namespace JoltISA

def protect_code (state : SailJoltState) (sources : List (BitVec 64 × Bool)) :
    Option SailJoltState := do
  let guard ← CodeGuard.new sources state.jolt_device.memory_layout.get_lowest_address.toNat
  pure { state with code_guard := some guard }

end JoltISA

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
