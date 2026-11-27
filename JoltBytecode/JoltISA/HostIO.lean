import JoltBytecode.JoltISA.RegisterAccess
import JoltBytecode.JoltISA.DeviceMemory

open LeanRV64D

set_option autoImplicit false

namespace JoltISA

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

-- Rust: jolt-platform/src/{advice,cycle_tracking,print}.rs.
def hostAdviceWriteCall : BitVec 32 := 0xADBABE
def hostCycleTrackCall : BitVec 32 := 0xC7C1E
def hostPrintCall : BitVec 32 := 0x505249

-- We use the name `readHostBytes` because Jolt does (`read_host_bytes`), but it is a
-- bad name: the bytes belong to the guest, and the host is the one reading them.
-- The guest is the program being proven; the host is the computer running Jolt.
-- Sometimes the guest asks the host to do something for it, such as printing some
-- text. The text sits in the guest's memory, so before the host can print it, it
-- has to copy those bytes out of the guest's memory. This function does that copying.

/-- Jolt's `read_host_bytes` (`tracer/src/emulator/host_io.rs:54` at Jolt `504dd78a2`):
append the guest bytes `[pointer, pointer + count)` to `bytes`, or return `none`.
`none` when the end overflows a u64 or passes `addressLimit`, or when any byte in
a nonempty range is unreadable. `loadByte a` is `some b` exactly when a guest
load at `a` succeeds (`HostMemory for Mmu`, `tracer/src/emulator/mmu.rs:1076`).
Allocation is assumed to succeed.
For example, a print message ending at `2^32` is allowed (`addressLimit = 2^32`). -/
def readHostBytes (loadByte : Nat → Option (BitVec 8))
    (pointer count addressLimit : Nat) (bytes : Array (BitVec 8)) :
    Option (Array (BitVec 8)) :=
  if pointer + count ≤ 2 ^ 64 - 1 ∧ pointer + count ≤ addressLimit then
    if count = 0 then some bytes
    else if (List.range count).all (fun offset => (loadByte (pointer + offset)).isSome) then do
      let loaded ← (List.range count).mapM (fun offset => loadByte (pointer + offset))
      pure (bytes ++ loaded.toArray)
    else none
  else none

/-- Jolt's `VirtualHostIO::exec` (`tracer/src/instruction/virtual_host_io.rs:20`) and
the three handlers it calls (`tracer/src/emulator/cpu.rs:1118–1197`), at Jolt `504dd78a2`.
A rejected call is ignored, so every call retires.
An accepted advice write appends its bytes to the advice tape, also in replay
(`handle_advice_write` has no replay check). Print and cycle-marker calls skip
replay, ignore unknown events, and only read memory, so they change no guest state.
x10..x13 supply the arguments.
For example, an advice write whose range has an unreadable byte appends nothing. -/
noncomputable def execHostIOWith
    (loadByte : SailJoltState → Nat → Option (BitVec 8)) :
    JoltMonad ExecutionResult := do
  let state ← get
  let callId := (sourceValue (.xreg (.Regidx 10)) state).setWidth 32
  if callId = hostAdviceWriteCall then
    let pointer := sourceValue (.xreg (.Regidx 11)) state
    let count := sourceValue (.xreg (.Regidx 12)) state
    match readHostBytes (loadByte state) pointer.toNat count.toNat (2 ^ 64 - 1) #[] with
    | none => pure ()
    | some bytes => modify fun current =>
        { current with adviceTape :=
            { current.adviceTape with bytes := current.adviceTape.bytes ++ bytes } }
  else if state.hostIO.mode != .replay then
    let pointer := (sourceValue (.xreg (.Regidx 11)) state).setWidth 32
    let count := (sourceValue (.xreg (.Regidx 12)) state).setWidth 32
    let event := (sourceValue (.xreg (.Regidx 13)) state).setWidth 32
    -- Both handlers reject unknown events before reading. Their accepted events
    -- are 1 and 2; their output and marker effects are outside the guest state.
    if (callId = hostCycleTrackCall || callId = hostPrintCall) && (event = 1 || event = 2) then
      let _ := readHostBytes (loadByte state) pointer.toNat count.toNat (2 ^ 32) #[]
      pure ()
  pure RETIRE_SUCCESS

noncomputable def execHostIO : JoltMonad ExecutionResult :=
  execHostIOWith Mmu.load?

end JoltISA
