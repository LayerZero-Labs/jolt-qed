import JoltBytecode.JoltISA.Core
import JoltBytecode.JoltISA.MemoryAccess

set_option autoImplicit false

namespace JoltISA

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

-- Reads 64 bits from the 8 addresses starting at `address`, using `byte` to read
-- each one; none if any of them is missing. Needed because the Jolt device is not
-- in Sail, so device reads cannot use Sail's own read.
-- See : jolt/tracer/src/emulator/mmu.rs:497 (device_doubleword)
def read_doubleword? (byte : Nat → Option (BitVec 8)) (address : Nat) : Option (BitVec 64) :=
  match byte address, byte (address + 1), byte (address + 2), byte (address + 3),
      byte (address + 4), byte (address + 5), byte (address + 6), byte (address + 7) with
  | some b0, some b1, some b2, some b3, some b4, some b5, some b6, some b7 =>
      some (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)
  | _, _, _, _, _, _, _, _ => none

-- The 64 bits at `address` in `state`, looked up without running a load (no
-- checks, no state change). The trace uses it to record the value a load reads
-- and the old value a store overwrites, as Rust does for the witness.
-- See : jolt/tracer/src/emulator/mmu.rs:480 (trace_load), :556 (trace_store)
noncomputable def trace_doubleword? (state : SailJoltState) (address : BitVec 64) :
    Option (BitVec 64) :=
  if address.toNat < RAM_START_ADDRESS then
    read_doubleword? (JoltDevice.load? state.jolt_device) address.toNat
  else read_doubleword? state.sail.mem.get? address.toNat

-- Writes 64 bits to the 8 device addresses starting at `address`, lowest 8 bits
-- first, each through JoltDevice.store?; none if any of them is not writable.
-- Needed because the Jolt device is not in Sail, so device writes cannot use
-- Sail's own write.
-- See : jolt/tracer/src/emulator/mmu.rs:739-745 (store_doubleword_raw, device branch)
def _root_.JoltDevice.store_doubleword? (io : JoltDevice) (address : BitVec 64) (value : BitVec 64) :
    Option JoltDevice :=
  (List.range 8).foldl (fun current k =>
    current.bind fun device =>
      JoltDevice.store? device (address.toNat + k) (value.extractLsb' (8 * k) 8)) (some io)

-- Rust: [Mmu::load_doubleword](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/emulator/mmu.rs).
-- Ordinary RAM retains Sail's access checks. Device reads use the same pure byte
-- reader as trace_doubleword?, so trace extraction and execution agree on device data.
noncomputable def readMemoryWord (address : BitVec 64) :
    JoltMonad (Result (BitVec 64) ExecutionResult) := fun state =>
  if address.toNat < RAM_START_ADDRESS then
    match read_doubleword? (JoltDevice.load? state.jolt_device) address.toNat with
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

-- Executes a 64-bit store. Below RAM_START_ADDRESS it writes the Jolt device;
-- at or above, it runs Sail's store, with Sail's checks. A device store may
-- differ from what a later read returns (termination ignores writes).
-- See : jolt/tracer/src/emulator/mmu.rs:437 (store_doubleword)
noncomputable def store_doubleword (address value : BitVec 64) :
    JoltMonad (Result Bool ExecutionResult) := fun state =>
  if address.toNat < RAM_START_ADDRESS then
    match JoltDevice.store_doubleword? state.jolt_device address value with
    | some io => .ok (.Ok true) { state with jolt_device := io }
    | none => .ok (.Err (.Memory_Exception
        (Virtaddr address, .E_SAMO_Access_Fault ()))) state
  else liftSail (vmem_write_addr (Virtaddr address) 8 value (Store Data) false false false) state

/-
DRAFT (S1): Jolt's own memory access, following Rust's Mmu directly. Nothing
uses these yet; they sit beside the Sail-based functions above until the switch.
Every Rust panic is an error. Address translation is the identity: Jolt never
leaves AddressingMode::None (mmu.rs:105, 750-757).
-/
namespace Mmu

-- true exactly when Rust's assertions pass for an access at `ea`.
-- See : jolt/tracer/src/emulator/mmu.rs:120-184 (assert_effective_address)
def effective_address_ok (device : JoltDevice) (ea : Nat) (is_write : Bool) : Bool :=
  let layout := device.memory_layout
  if ea < RAM_START_ADDRESS then
    ea ≤ layout.io_end.toNat &&
    (layout.get_lowest_address.toNat ≤ ea || ea ≤ RAM_START_ADDRESS - 8) &&
    (if is_write then
      device.is_output ea || device.is_panic ea || device.is_termination ea
    else
      device.is_input ea || device.is_trusted_advice ea || device.is_untrusted_advice ea ||
        device.is_output ea || device.is_panic ea || device.is_termination ea ||
        ea ≤ RAM_START_ADDRESS - 8)
  else if is_write then
    (ea < layout.stack_end.toNat || layout.stack_end.toNat + STACK_CANARY_SIZE ≤ ea) &&
      ea < layout.heap_end.toNat
  else
    ea < layout.heap_end.toNat

-- Rust RAM is zero-filled, so an address with no byte in the hash map reads 0.
-- See : jolt/tracer/src/emulator/memory.rs:49-51, 197-201
def ram_byte (mem : Std.ExtHashMap Nat (BitVec 8)) (ea : Nat) : BitVec 8 :=
  (mem.get? ea).getD 0

-- The 64 bits at RAM address `ea`, lowest 8 bits at `ea`.
def ram_doubleword (mem : Std.ExtHashMap Nat (BitVec 8)) (ea : Nat) : BitVec 64 :=
  ram_byte mem (ea + 7) ++ ram_byte mem (ea + 6) ++ ram_byte mem (ea + 5) ++
    ram_byte mem (ea + 4) ++ ram_byte mem (ea + 3) ++ ram_byte mem (ea + 2) ++
    ram_byte mem (ea + 1) ++ ram_byte mem ea

def write_ram_doubleword (mem : Std.ExtHashMap Nat (BitVec 8)) (ea : Nat) (value : BitVec 64) :
    Std.ExtHashMap Nat (BitVec 8) :=
  (List.range 8).foldl (fun mem k => mem.insert (ea + k) (value.extractLsb' (8 * k) 8)) mem

-- One byte; none where Rust panics.
-- See : jolt/tracer/src/emulator/mmu.rs:450-478 (load_raw)
def load_raw? (state : SailJoltState) (ea : Nat) : Option (BitVec 8) :=
  let device := state.jolt_device
  if !effective_address_ok device ea false then none
  else if RAM_START_ADDRESS ≤ ea then some (ram_byte state.sail.mem ea)
  else if (0x1020 ≤ ea && ea ≤ 0x1fff) || (0x02000000 ≤ ea && ea ≤ 0x0200ffff) ||
      (0x0c000000 ≤ ea && ea ≤ 0x0fffffff) || (0x10000000 ≤ ea && ea ≤ 0x100000ff) ||
      (0x10001000 ≤ ea && ea ≤ 0x10001fff) then none
  else if device.is_input ea || device.is_trusted_advice ea || device.is_untrusted_advice ea ||
      device.is_output ea || device.is_panic ea || device.is_termination ea ||
      ea ≤ RAM_START_ADDRESS - 8 then
    device.load? ea
  else none

-- One byte; none where Rust panics.
-- See : jolt/tracer/src/emulator/mmu.rs:644-667 (store_raw)
def store_raw? (state : SailJoltState) (ea : Nat) (value : BitVec 8) : Option SailJoltState :=
  if RAM_START_ADDRESS ≤ ea then
    if effective_address_ok state.jolt_device ea true then
      some { state with sail := { state.sail with mem := state.sail.mem.insert ea value } }
    else none
  else if (0x02000000 ≤ ea && ea ≤ 0x0200ffff) || (0x0c000000 ≤ ea && ea ≤ 0x0fffffff) ||
      (0x10000000 ≤ ea && ea ≤ 0x100000ff) || (0x10001000 ≤ ea && ea ≤ 0x10001fff) then none
  else if !effective_address_ok state.jolt_device ea true then none
  else (state.jolt_device.store? ea value).map fun device => { state with jolt_device := device }

-- RAM: Rust checks only the start address, then reads 64 bits.
-- Device: Rust reads 8 addresses one at a time through load_raw.
-- See : jolt/tracer/src/emulator/mmu.rs:329-337 (load_doubleword)
--       jolt/tracer/src/emulator/mmu.rs:619-635 (load_doubleword_raw)
noncomputable def load_doubleword (address : BitVec 64) :
    JoltMonad (Result (BitVec 64) ExecutionResult) := fun state =>
  let ea := address.toNat
  if ea % 8 ≠ 0 then .error (Error.Assertion "Unaligned load_doubleword") state
  else if RAM_START_ADDRESS ≤ ea then
    if effective_address_ok state.jolt_device ea false then
      .ok (.Ok (ram_doubleword state.sail.mem ea)) state
    else .error (Error.Assertion "Illegal Memory Access") state
  else
    match read_doubleword? (load_raw? state) ea with
    | some value => .ok (.Ok value) state
    | none => .error (Error.Assertion "Load Failed") state

-- RAM: Rust checks only the start address, then writes 64 bits.
-- Device: Rust writes 8 addresses one at a time through store_raw.
-- See : jolt/tracer/src/emulator/mmu.rs:437-443 (store_doubleword)
--       jolt/tracer/src/emulator/mmu.rs:729-748 (store_doubleword_raw)
noncomputable def store_doubleword (address value : BitVec 64) :
    JoltMonad (Result Bool ExecutionResult) := fun state =>
  let ea := address.toNat
  if ea % 8 ≠ 0 then .error (Error.Assertion "Unaligned store_doubleword") state
  else if RAM_START_ADDRESS ≤ ea then
    if effective_address_ok state.jolt_device ea true then
      .ok (.Ok true)
        { state with sail := { state.sail with mem := write_ram_doubleword state.sail.mem ea value } }
    else .error (Error.Assertion "Illegal Memory Access") state
  else
    let stored := (List.range 8).foldl
      (fun current k => current.bind fun s => store_raw? s (ea + k) (value.extractLsb' (8 * k) 8))
      (some state)
    match stored with
    | some state' => .ok (.Ok true) state'
    | none => .error (Error.Assertion "Store Failed") state

end Mmu

@[simp] theorem readMemoryWord_ram (address : BitVec 64)
    (h : RAM_START_ADDRESS ≤ address.toNat) :
    readMemoryWord address =
      liftSail (vmem_read_addr (Virtaddr address) 0 8 (Load Data) false false false) := by
  funext state
  simp [readMemoryWord, Nat.not_lt.mpr h]

@[simp] theorem store_doubleword_ram (address value : BitVec 64)
    (h : RAM_START_ADDRESS ≤ address.toNat) :
    store_doubleword address value =
      liftSail (vmem_write_addr (Virtaddr address) 8 value (Store Data) false false false) := by
  funext state
  simp [store_doubleword, Nat.not_lt.mpr h]

end JoltISA
