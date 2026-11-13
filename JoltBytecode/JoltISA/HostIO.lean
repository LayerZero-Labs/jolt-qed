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

/-- The exclusive end of the addresses a print or cycle-marker string can
occupy: the guest passes those pointers and lengths as 32-bit values.
See : jolt/tracer/src/emulator/host_io.rs:14-16 (`HOST_STRING_ADDRESS_LIMIT`)
at 3cc6e7bd1. -/
def hostStringAddressLimit : Nat := 2 ^ 32

/-- The largest end of an advice-write range, `u64::MAX`.
See : jolt/tracer/src/emulator/cpu.rs:1148-1160 (`Cpu::handle_advice_write`)
at 3cc6e7bd1. -/
def hostAdviceAddressLimit : Nat := 2 ^ 64 - 1

/-- Collect `count` bytes upward from `pointer` with `loadByte`, which returns
`none` at a byte the guest could not load. The result is `none` as soon as one
byte is unreadable, and otherwise holds every byte. For example, with
`loadByte := Mmu.hostLoad`, a two-byte read whose second byte is in the stack
canary returns `none`. The load operation is a parameter, so the frame
lemmas can be stated for any loader. -/
def readHostBytes (loadByte : BitVec 64 → JoltMonad (Option (BitVec 8))) {width : Nat}
    (pointer : BitVec width) : Nat → Array (BitVec 8) →
      JoltMonad (Option (Array (BitVec 8)))
  | 0, bytes => pure (some bytes)
  | remaining + 1, bytes => do
      match ← loadByte (pointer.setWidth 64) with
      | none => pure none
      | some byte => readHostBytes loadByte (pointer + 1) remaining (bytes.push byte)

/-- Jolt's tracer's host-call read (`read_host_bytes`): the `count` bytes from
`pointer`, or `none` when the range ends past `limit` or holds a byte the guest
could not load. Such a call is logged and ignored and loads nothing. Within the
limit the pointer does not wrap. For example, a print of 4 bytes at
`2^32 - 2` ends past `hostStringAddressLimit` and reads nothing.
Allocation failures are also ignored by Jolt's tracer; the model has no host
allocator, so it never fails there.
See : jolt/tracer/src/emulator/host_io.rs:50-85 (`read_host_bytes`) at 3cc6e7bd1. -/
def readHostRange (loadByte : BitVec 64 → JoltMonad (Option (BitVec 8))) {width : Nat}
    (pointer : BitVec width) (count limit : Nat) : JoltMonad (Option (Array (BitVec 8))) :=
  if pointer.toNat + count ≤ limit then readHostBytes loadByte pointer count #[]
  else pure none

/-- Jolt's tracer's `VirtualHostIO::exec` and its three host-call handlers,
projected onto guest state. Since a16z/jolt#2410 a host call never fails:
an unknown call, an unknown event, or an unreadable range is logged and ignored.
An advice write appends its bytes to the advice tape in both host-I/O modes;
prints and cycle markers have no effect on guest state, and replay mode skips
them. Host stdout and cycle-marker logs are not stored in Sail state. Encoded
instruction operands are deliberately unused: the ABI reads architectural
x10..x13. For example, a print with event 7 is ignored, and an advice write of
3 bytes at a readable address appends those 3 bytes.
See : jolt/tracer/src/instruction/virtual_host_io.rs:19-38 (`VirtualHostIO::exec`)
and jolt/tracer/src/emulator/cpu.rs:1079-1192 (`handle_jolt_cycle_marker`,
`handle_jolt_print`, `handle_advice_write`, `read_host_message`) at 3cc6e7bd1. -/
noncomputable def execHostIOWith
    (loadByte : BitVec 64 → JoltMonad (Option (BitVec 8))) :
    JoltMonad ExecutionResult := do
  -- Every branch ends in its own `pure RETIRE_SUCCESS`, so the definition has
  -- no join points for the frame tactics to see through.
  let callId ← readSrc (.xreg (.Regidx 10))
  if callId.setWidth 32 = hostAdviceWriteCall then
    let pointer ← readSrc (.xreg (.Regidx 11))
    let count ← readSrc (.xreg (.Regidx 12))
    match ← readHostRange loadByte pointer count.toNat hostAdviceAddressLimit with
    | none => pure RETIRE_SUCCESS
    | some bytes => do
        modify fun state =>
          { state with adviceTape :=
              { state.adviceTape with bytes := state.adviceTape.bytes ++ bytes } }
        pure RETIRE_SUCCESS
  else if callId.setWidth 32 = hostCycleTrackCall || callId.setWidth 32 = hostPrintCall then
    let pointer ← readSrc (.xreg (.Regidx 11))
    let count ← readSrc (.xreg (.Regidx 12))
    let event ← readSrc (.xreg (.Regidx 13))
    -- Both handlers ignore replay mode and an unknown event before reading.
    -- The events are the marker start and end (1, 2) and the print string and
    -- line (1, 2). Pointers and lengths are 32-bit. The bytes read only reach
    -- the host's logs.
    if (← get).hostIO.mode = .live &&
        (event.setWidth 32 = (1 : BitVec 32) || event.setWidth 32 = (2 : BitVec 32)) then
      let _ ← readHostRange loadByte (pointer.setWidth 32) (count.setWidth 32).toNat
        hostStringAddressLimit
      pure RETIRE_SUCCESS
    else pure RETIRE_SUCCESS
  else pure RETIRE_SUCCESS

noncomputable def execHostIO : JoltMonad ExecutionResult :=
  execHostIOWith Mmu.hostLoad

end JoltISA
