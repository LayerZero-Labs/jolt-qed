import JoltBytecode.JoltISA.Core
import JoltBytecode.JoltISA.MemoryAccess

set_option autoImplicit false

namespace JoltISA

-- Rust: jolt/common/src/constants.rs:21 (RAM_START_ADDRESS)
def RAM_START_ADDRESS : Nat := 0x80000000

-- Rust: jolt/common/src/constants.rs:26 (STACK_CANARY_SIZE)
def STACK_CANARY_SIZE : Nat := 128

end JoltISA

namespace JoltDevice

-- Rust: jolt/common/src/jolt_device.rs:183-207 (JoltDevice::is_*)
def is_input (device : JoltDevice) (address : Nat) : Bool :=
  device.memory_layout.input_start.toNat ≤ address &&
    address < device.memory_layout.input_end.toNat

def is_trusted_advice (device : JoltDevice) (address : Nat) : Bool :=
  device.memory_layout.trusted_advice_start.toNat ≤ address &&
    address < device.memory_layout.trusted_advice_end.toNat

def is_untrusted_advice (device : JoltDevice) (address : Nat) : Bool :=
  device.memory_layout.untrusted_advice_start.toNat ≤ address &&
    address < device.memory_layout.untrusted_advice_end.toNat

def is_output (device : JoltDevice) (address : Nat) : Bool :=
  device.memory_layout.output_start.toNat ≤ address &&
    address < device.memory_layout.termination.toNat

def is_panic (device : JoltDevice) (address : Nat) : Bool :=
  device.memory_layout.panic.toNat ≤ address &&
    address < device.memory_layout.termination.toNat

def is_termination (device : JoltDevice) (address : Nat) : Bool :=
  device.memory_layout.termination.toNat ≤ address &&
    address < device.memory_layout.io_end.toNat

-- Rust: jolt/common/src/jolt_device.rs:121-148 (JoltDevice::load).
-- Device buffers are zero-padded by Rust. This is distinct from a missing Sail
-- RAM byte, which memoryWord? below leaves absent.
def load? (device : JoltDevice) (address : Nat) : Option (BitVec 8) :=
  let layout := device.memory_layout
  if device.is_panic address then some (if device.panic then 1 else 0)
  else if device.is_termination address then some 0
  else if device.is_input address then
    some (device.inputs[address - layout.input_start.toNat]?.getD 0)
  else if device.is_trusted_advice address then
    some (device.trusted_advice[address - layout.trusted_advice_start.toNat]?.getD 0)
  else if device.is_untrusted_advice address then
    some (device.untrusted_advice[address - layout.untrusted_advice_start.toNat]?.getD 0)
  else if device.is_output address then
    some (device.outputs[address - layout.output_start.toNat]?.getD 0)
  else if address ≤ JoltISA.RAM_START_ADDRESS - 8 then some 0
  else none

-- Rust: jolt/common/src/jolt_device.rs:150-176 (JoltDevice::store).
-- The panic byte sets the flag regardless of the stored value. The rest of the
-- panic/termination regions ignore writes. Output grows with zero-filled gaps.
def store? (device : JoltDevice) (address : Nat) (value : BitVec 8) :
    Option JoltDevice :=
  if address = device.memory_layout.panic.toNat then some { device with panic := true }
  else if device.is_panic address || device.is_termination address then some device
  else if device.is_output address then
    let offset := address - device.memory_layout.output_start.toNat
    let outputs := device.outputs ++ Array.replicate (offset + 1 - device.outputs.size) 0
    some { device with outputs := outputs.set! offset value }
  else none

end JoltDevice

namespace JoltISA

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

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
  if address.toNat < RAM_START_ADDRESS then
    wordFromBytes? (JoltDevice.load? state.jolt_device) address.toNat
  else wordFromBytes? state.sail.mem.get? address.toNat

-- Rust: [Mmu::store_bytes](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mmu.rs).
-- A device dword store visits bytes in increasing address order.
def storeDeviceWord? (io : JoltDevice) (address : BitVec 64) (value : BitVec 64) :
    Option JoltDevice :=
  (List.range 8).foldl (fun current k =>
    current.bind fun device =>
      JoltDevice.store? device (address.toNat + k) (value.extractLsb' (8 * k) 8)) (some io)

-- Rust: [Mmu::load_doubleword](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mmu.rs).
-- Ordinary RAM retains Sail's access checks. Device reads use the same pure byte
-- reader as memoryWord?, so trace extraction and execution agree on device data.
noncomputable def readMemoryWord (address : BitVec 64) :
    JoltMonad (Result (BitVec 64) ExecutionResult) := fun state =>
  if address.toNat < RAM_START_ADDRESS then
    match wordFromBytes? (JoltDevice.load? state.jolt_device) address.toNat with
    | some value => .ok (.Ok value) state
    | none => .ok (.Err (.Memory_Exception
        (Virtaddr address, .E_Load_Access_Fault ()))) state
  else liftSail (vmem_read_addr (Virtaddr address) 0 8 (Load Data) false false false) state

/-- Byte access for host calls. Like `readMemoryWord`, RAM uses the existing
Sail memory interface and device bytes use `JoltDevice.load?`. Rust's byte-load
path rejects the unsupported peripheral mappings below with a panic, not a
returned translation trap. Heap bounds and full MMU/capture correspondence
remain the shared memory-model obligations (model-review #15).
Rust: tracer/src/emulator/mmu.rs::load and load_raw. -/
noncomputable def readMemoryByte (address : BitVec 64) :
    JoltMonad (Result (BitVec 8) ExecutionResult) := fun state =>
  let a := address.toNat
  if (0x1020 ≤ a && a ≤ 0x1fff) || (0x02000000 ≤ a && a ≤ 0x0200ffff) ||
      (0x0c000000 ≤ a && a ≤ 0x0fffffff) ||
      (0x10000000 ≤ a && a ≤ 0x100000ff) ||
      (0x10001000 ≤ a && a ≤ 0x10001fff) then
    .error (Error.Assertion "VirtualHostIO: unsupported peripheral read") state
  else if a < RAM_START_ADDRESS then
    match JoltDevice.load? state.jolt_device a with
    | some value => .ok (.Ok value) state
    | none => .error (Error.Assertion "VirtualHostIO: unknown memory mapping") state
  else liftSail (vmem_read_addr (Virtaddr address) 0 1 (Load Data) false false false) state

-- Rust: [Mmu::store_doubleword](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mmu.rs:473).
-- Device stores update the device in the full ISA state. Their stored word may
-- differ from a subsequent read (for example, termination ignores writes).
noncomputable def writeMemoryWord (address value : BitVec 64) :
    JoltMonad (Result Bool ExecutionResult) := fun state =>
  if address.toNat < RAM_START_ADDRESS then
    match storeDeviceWord? state.jolt_device address value with
    | some io => .ok (.Ok true) { state with jolt_device := io }
    | none => .ok (.Err (.Memory_Exception
        (Virtaddr address, .E_SAMO_Access_Fault ()))) state
  else liftSail (vmem_write_addr (Virtaddr address) 8 value (Store Data) false false false) state

@[simp] theorem readMemoryWord_ram (address : BitVec 64)
    (h : RAM_START_ADDRESS ≤ address.toNat) :
    readMemoryWord address =
      liftSail (vmem_read_addr (Virtaddr address) 0 8 (Load Data) false false false) := by
  funext state
  simp [readMemoryWord, Nat.not_lt.mpr h]

@[simp] theorem writeMemoryWord_ram (address value : BitVec 64)
    (h : RAM_START_ADDRESS ≤ address.toNat) :
    writeMemoryWord address value =
      liftSail (vmem_write_addr (Virtaddr address) 8 value (Store Data) false false false) := by
  funext state
  simp [writeMemoryWord, Nat.not_lt.mpr h]

end JoltISA
