import JoltBytecode.JoltISA.RegisterAccess
import JoltBytecode.JoltISA.DeviceMemory

set_option autoImplicit false

namespace JoltISA

open Sail PreSail LeanRV64D.Functions

-- Rust: jolt-platform/src/{advice,cycle_tracking,print}.rs.
def hostAdviceWriteCall : BitVec 32 := 0xADBABE
def hostCycleTrackCall : BitVec 32 := 0xC7C1E
def hostPrintCall : BitVec 32 := 0x505249

/-- Collect bytes before appending anything. A returned memory trap stops the
handler; a monadic error (representing a fatal failure) propagates. Rust's
read_string increments its u32 pointer even after the last byte; advice writes
compute ptr+i and do not increment after the last byte. The load operation is
explicit so the handler's behavior can be checked independently of the shared
MMU abstraction. -/
def readHostBytes (loadByte : BitVec 64 → JoltMonad (Result (BitVec 8) ExecutionResult))
    (overflowChecks incrementAfterLast : Bool) {width : Nat}
    (pointer : BitVec width) : Nat → Array (BitVec 8) →
      JoltMonad (Option (Array (BitVec 8)))
  | 0, bytes => pure (some bytes)
  | remaining + 1, bytes => do
      match ← loadByte (pointer.setWidth 64) with
      | .Err _ => pure none
      | .Ok byte =>
          if overflowChecks && (incrementAfterLast || remaining != 0) &&
              pointer.toNat + 1 ≥ 2 ^ width then
            throw (Error.Assertion "VirtualHostIO: pointer overflow")
          readHostBytes loadByte overflowChecks incrementAfterLast
            (pointer + 1) remaining (bytes.push byte)

/-- Rust VirtualHostIO::exec and Cpu's three host-call handlers, projected onto
guest state. Host stdout and cycle-marker logs are not stored in Sail state.
Their memory reads and invalid-event failures are retained. Encoded instruction
operands are deliberately unused: the ABI reads architectural x10..x13.
Rust: tracer/src/instruction/virtual_host_io.rs; emulator/cpu.rs:1244-1333. -/
noncomputable def execHostIOWith
    (loadByte : BitVec 64 → JoltMonad (Result (BitVec 8) ExecutionResult)) :
    JoltMonad ExecutionResult := do
  let config := (← get).hostIO
  if config.mode = .replay then
    return RETIRE_SUCCESS
  let callId := (← readSrc (.xreg (.Regidx 10))).setWidth 32
  if callId = hostAdviceWriteCall then
    let pointer ← readSrc (.xreg (.Regidx 11))
    let count ← readSrc (.xreg (.Regidx 12))
    match ← readHostBytes loadByte config.overflowChecks false pointer count.toNat #[] with
    | none => pure () -- Rust deliberately ignores the handler's returned trap.
    | some bytes => modify fun state =>
        { state with adviceTape :=
            { state.adviceTape with bytes := state.adviceTape.bytes ++ bytes } }
  else if callId = hostCycleTrackCall || callId = hostPrintCall then
    let pointer := (← readSrc (.xreg (.Regidx 11))).setWidth 32
    let count := (← readSrc (.xreg (.Regidx 12))).setWidth 32
    let event := (← readSrc (.xreg (.Regidx 13))).setWidth 32
    if callId = hostCycleTrackCall then
      if event = 1 then
        let _ ← readHostBytes loadByte config.overflowChecks true pointer count.toNat #[]
        pure ()
      else if event != 2 then
        throw (Error.Assertion "VirtualHostIO: invalid cycle-marker event")
    else
      match ← readHostBytes loadByte config.overflowChecks true pointer count.toNat #[] with
      | none => pure ()
      | some _ =>
          if event != 1 && event != 2 then
            throw (Error.Assertion "VirtualHostIO: invalid print event")
  pure RETIRE_SUCCESS

noncomputable def execHostIO : JoltMonad ExecutionResult :=
  execHostIOWith Mmu.load

end JoltISA
