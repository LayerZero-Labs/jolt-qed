import JoltBytecode.JoltISA.Core
import JoltBytecode.JoltISA.MemoryAccess

set_option autoImplicit false

namespace JoltISA

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

-- Rust: [RAM_START_ADDRESS](/Users/ari.biswas/Work-with-A16z/jolt/common/src/constants.rs:21).
def ramStartAddress : Nat := 0x80000000

private def inRange (address : Nat) (range : BitVec 64 × BitVec 64) : Bool :=
  range.1.toNat ≤ address && address < range.2.toNat

-- Rust: [JoltDevice::load](/Users/ari.biswas/Work-with-A16z/jolt/common/src/jolt_device.rs:121).
-- Device buffers are zero-padded by Rust. This is distinct from a missing Sail
-- RAM byte, which memoryWord? below leaves absent.
def deviceByte? (io : JoltIOState) (address : Nat) : Option (BitVec 8) :=
  if inRange address io.layout.panic then some (if io.panic then 1 else 0)
  else if inRange address io.layout.termination then some 0
  else if inRange address io.layout.input then
    some (io.inputs[address - io.layout.input.1.toNat]?.getD 0)
  else if inRange address io.layout.trustedAdvice then
    some (io.trustedAdvice[address - io.layout.trustedAdvice.1.toNat]?.getD 0)
  else if inRange address io.layout.untrustedAdvice then
    some (io.untrustedAdvice[address - io.layout.untrustedAdvice.1.toNat]?.getD 0)
  else if inRange address io.layout.output then
    some (io.outputs[address - io.layout.output.1.toNat]?.getD 0)
  else if address ≤ ramStartAddress - 8 then some 0
  else none

-- Rust: [Memory::read_doubleword](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/memory.rs:251)
-- and [device_doubleword](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mmu.rs:539).
-- Assemble eight little-endian bytes. Missing bytes remain missing.
def wordFromBytes? (byte : Nat → Option (BitVec 8)) (address : Nat) : Option (BitVec 64) :=
  match byte address, byte (address + 1), byte (address + 2), byte (address + 3),
      byte (address + 4), byte (address + 5), byte (address + 6), byte (address + 7) with
  | some b0, some b1, some b2, some b3, some b4, some b5, some b6, some b7 =>
      some (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)
  | _, _, _, _, _, _, _, _ => none

-- Rust: [Mmu::trace_store](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mmu.rs:609).
-- Observe the old word in the recorded full state. This does not execute a load
-- or perform address translation; Rust captures the effective-address word here.
noncomputable def memoryWord? (state : SailJoltState) (address : BitVec 64) :
    Option (BitVec 64) :=
  if address.toNat < ramStartAddress then
    wordFromBytes? (deviceByte? state.io) address.toNat
  else wordFromBytes? state.sail.mem.get? address.toNat

-- Rust: [JoltDevice::store](/Users/ari.biswas/Work-with-A16z/jolt/common/src/jolt_device.rs:150).
-- The panic byte sets the flag regardless of the stored value. The rest of the
-- panic/termination regions ignore writes. Output grows with zero-filled gaps.
def storeDeviceByte? (io : JoltIOState) (address : Nat) (value : BitVec 8) :
    Option JoltIOState :=
  if address = io.layout.panic.1.toNat then some { io with panic := true }
  else if inRange address io.layout.panic || inRange address io.layout.termination then some io
  else if inRange address io.layout.output then
    let offset := address - io.layout.output.1.toNat
    let outputs := io.outputs ++ Array.replicate (offset + 1 - io.outputs.size) 0
    some { io with outputs := outputs.set! offset value }
  else none

-- Rust: [Mmu::store_bytes](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mmu.rs).
-- A device dword store visits bytes in increasing address order.
def storeDeviceWord? (io : JoltIOState) (address : BitVec 64) (value : BitVec 64) :
    Option JoltIOState :=
  (List.range 8).foldl (fun current k =>
    current.bind fun device =>
      storeDeviceByte? device (address.toNat + k) (value.extractLsb' (8 * k) 8)) (some io)

-- Rust: [Mmu::load_doubleword](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mmu.rs).
-- Ordinary RAM retains Sail's access checks. Device reads use the same pure byte
-- reader as memoryWord?, so trace extraction and execution agree on device data.
noncomputable def readMemoryWord (address : BitVec 64) :
    JoltMonad (Result (BitVec 64) ExecutionResult) := fun state =>
  if address.toNat < ramStartAddress then
    match wordFromBytes? (deviceByte? state.io) address.toNat with
    | some value => .ok (.Ok value) state
    | none => .ok (.Err (.Memory_Exception
        (Virtaddr address, .E_Load_Access_Fault ()))) state
  else liftSail (vmem_read_addr (Virtaddr address) 0 8 (Load Data) false false false) state

-- Rust: [Mmu::store_doubleword](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mmu.rs:473).
-- Device stores update the device in the full ISA state. Their stored word may
-- differ from a subsequent read (for example, termination ignores writes).
noncomputable def writeMemoryWord (address value : BitVec 64) :
    JoltMonad (Result Bool ExecutionResult) := fun state =>
  if address.toNat < ramStartAddress then
    match storeDeviceWord? state.io address value with
    | some io => .ok (.Ok true) { state with io := io }
    | none => .ok (.Err (.Memory_Exception
        (Virtaddr address, .E_SAMO_Access_Fault ()))) state
  else liftSail (vmem_write_addr (Virtaddr address) 8 value (Store Data) false false false) state

@[simp] theorem readMemoryWord_ram (address : BitVec 64)
    (h : ramStartAddress ≤ address.toNat) :
    readMemoryWord address =
      liftSail (vmem_read_addr (Virtaddr address) 0 8 (Load Data) false false false) := by
  funext state
  simp [readMemoryWord, Nat.not_lt.mpr h]

@[simp] theorem writeMemoryWord_ram (address value : BitVec 64)
    (h : ramStartAddress ≤ address.toNat) :
    writeMemoryWord address value =
      liftSail (vmem_write_addr (Virtaddr address) 8 value (Store Data) false false false) := by
  funext state
  simp [writeMemoryWord, Nat.not_lt.mpr h]

end JoltISA
