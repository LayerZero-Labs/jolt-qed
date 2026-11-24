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

/-- Jolt `ff6fc6568`, `tracer/src/emulator/cpu.rs` (`HostIo`): replay suppresses
print and cycle-marker effects, but still appends advice writes.
For example, a replayed print performs no memory reads. -/
inductive JoltHostIOMode where
  | live
  | replay
  deriving DecidableEq, Repr

/-- Host execution mode at Jolt `ff6fc6568` (`cpu.rs`, `HostIo`).
For example, `replay` skips print and cycle-marker handlers. -/
structure JoltHostIOConfig where
  mode : JoltHostIOMode := .live

/-- How the tracer ended a run (`HaltKind` in `tracer/src/emulator/cpu.rs`).
For example, EBREAK selects `panic`. -/
inductive JoltHaltKind where
  | success
  | panic
  deriving DecidableEq, Repr

structure SailJoltState where
  sail : SailState
  vregs : BitVec 7 → BitVec 64 := fun _ => 0
  -- Rust: jolt/tracer/src/emulator/mmu.rs:25 (Mmu.jolt_device)
  jolt_device : JoltDevice
  adviceTape : JoltAdviceTape
  hostIO : JoltHostIOConfig := {}
  /-- Code-word indices from the lowest mapped address, as `CodeGuard::region`.
  For example, `(2, 4)` protects exactly domain words two and three. -/
  codeRegion : Nat × Nat := (0, 0)
  /-- A recorded halt; for example, `some .success` makes later ticks no-ops. -/
  halted : Option JoltHaltKind := none

namespace JoltISA

/-- The protected code span from decoded source addresses and compressed flags.
This is `code_region` in `crates/jolt-program/src/preprocess/ram.rs` at `ff6fc6568`.
For example, source words two and four protect the whole interval `[2, 5)`, including data between them.
Zero-address padding is ignored; invalid alignment, underflow or extent overflow fails. -/
def codeRegionOf (layout : MemoryLayout) (sources : List (BitVec 64 × Bool)) :
    Option (Nat × Nat) := do
  let lowest := layout.get_lowest_address.toNat
  guard (lowest % 8 == 0)
  let mut region : Option (Nat × Nat) := none
  for (address, compressed) in sources do
    if address != 0 then
      let start := address.toNat
      let stop ← MemoryLayout.checkedAdd start (if compressed then 2 else 4)
      guard (lowest ≤ start && start % 2 == 0)
      let first := (start - lowest) / 8
      let last := (stop - lowest + 7) / 8
      region := some (match region with
        | none => (first, last)
        | some (left, right) => (min left first, max right last))
  pure (region.getD (0, 0))

/-- Install input/advice memory and the code guard for a new run.
The supplied state contains the program image and starting register values.
For example, input byte zero is written at `memory_layout.input_start`.
The device retains only layout and the initially false panic claim. -/
def initialState (state : SailJoltState) (sources : List (BitVec 64 × Bool))
    (inputs trusted untrusted : Array (BitVec 8)) : Option SailJoltState := do
  let region ← codeRegionOf state.jolt_device.memory_layout sources
  let mem ← state.jolt_device.initialMem state.sail.mem inputs trusted untrusted
  pure { state with
    sail := { state.sail with mem := mem }
    jolt_device := { state.jolt_device with panic := false }
    codeRegion := region
    halted := none }

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
