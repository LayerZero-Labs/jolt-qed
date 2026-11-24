import JoltBytecode.JoltISA.Core
import JoltBytecode.JoltISA.MemoryAccess

open LeanRV64D

set_option autoImplicit false

namespace JoltISA

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

-- Reads 64 bits from the 8 addresses starting at `address`, using `byte` to read
-- each one; none if any address is unmapped. The callback selects the same shared
-- byte map for RAM and I/O.
-- See: jolt/tracer/src/emulator/mmu.rs:619 (device_doubleword) at ff6fc6568.
def read_doubleword? (byte : Nat → Option (BitVec 8)) (address : Nat) : Option (BitVec 64) :=
  match byte address, byte (address + 1), byte (address + 2), byte (address + 3),
      byte (address + 4), byte (address + 5), byte (address + 6), byte (address + 7) with
  | some b0, some b1, some b2, some b3, some b4, some b5, some b6, some b7 =>
      some (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)
  | _, _, _, _, _, _, _, _ => none

/-!
Memory accesses at Jolt `ff6fc6568` follow `tracer/src/emulator/mmu.rs`.
All bytes, including inputs, advice, outputs and the I/O gap, use `sail.mem`.
The code interval is `SailJoltState.codeRegion`, in RAM word indices as in
`CodeGuard::region`; the other protected intervals derive from `memory_layout`.
For example, storing the existing value in a canary byte succeeds, while changing
it fails. Heap padding is writable through the end of the admitted RAM domain.
-/
namespace Mmu

/-- End of RAM backing (`MemoryLayout::ram_size` at `ff6fc6568`).
For example, heap padding extends the backing past `heap_end`. -/
def ram_backing_end (device : JoltDevice) : Nat :=
  RAM_START_ADDRESS + device.memory_layout.ram_size

/-- The tracer's address-only check (`assert_effective_address`).
For example, code stores pass this check and are checked for value preservation separately. -/
def effective_address_ok (device : JoltDevice) (ea : Nat) (_is_write : Bool) : Bool :=
  if ea < RAM_START_ADDRESS then device.readable ea
  else ea < ram_backing_end device

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

/-- Whether the doubleword containing `address` is protected.
This transcribes `assert_write_protected_store`; for example, a word overlapping
an unaligned canary start is protected in full. -/
def protected_byte (state : SailJoltState) (address : Nat) : Bool :=
  let word := address / 8 * 8
  let device := state.jolt_device
  let layout := device.memory_layout
  let index := (word - layout.get_lowest_address.toNat) / 8
  (state.codeRegion.1 ≤ index && index < state.codeRegion.2) ||
    device.is_input word || device.is_trusted_advice word || device.is_untrusted_advice word ||
    (layout.stack_end.toNat ≤ word + 7 && word < layout.stack_end.toNat + STACK_CANARY_SIZE)

/-- Value-preserving protected-store check for `width` bytes of a little-endian value.
For example, writing zero to a protected zero byte succeeds.
This is `assert_write_protected_store`, without its panic diagnostics. -/
def protected_store_ok (state : SailJoltState) (address : Nat)
    (value : BitVec 64) (width : Nat) : Bool :=
  (List.range width).all fun k =>
    !protected_byte state (address + k) ||
      ram_byte state.sail.mem (address + k) == value.extractLsb' (8 * k) 8

/-- Unsupported peripheral dispatch in the tracer's `load_raw`.
For example, a UART load faults. -/
def unsupported_load (ea : Nat) : Bool :=
  (0x1020 ≤ ea && ea ≤ 0x1fff) || (0x02000000 ≤ ea && ea ≤ 0x0200ffff) ||
    (0x0c000000 ≤ ea && ea ≤ 0x0fffffff) || (0x10000000 ≤ ea && ea ≤ 0x100000ff) ||
    (0x10001000 ≤ ea && ea ≤ 0x10001fff)

/-- Unsupported peripheral dispatch in `store_raw`; for example, a CLINT store faults. -/
def unsupported_store (ea : Nat) : Bool :=
  (0x02000000 ≤ ea && ea ≤ 0x0200ffff) ||
    (0x0c000000 ≤ ea && ea ≤ 0x0fffffff) || (0x10000000 ≤ ea && ea ≤ 0x100000ff) ||
    (0x10001000 ≤ ea && ea ≤ 0x10001fff)

/-- Read one byte from shared memory, or fail where the tracer's `load_raw` faults.
For example, an untouched byte in the I/O gap reads zero. -/
def load_raw? (state : SailJoltState) (ea : Nat) : Option (BitVec 8) :=
  if !effective_address_ok state.jolt_device ea false then none
  else if RAM_START_ADDRESS ≤ ea then some (ram_byte state.sail.mem ea)
  else if unsupported_load ea then none
  else state.jolt_device.load? state.sail.mem ea

/-- Store one byte with the tracer's address and protection checks (`store_raw`).
For example, a same-value input store succeeds and keeps the device unchanged. -/
def store_raw? (state : SailJoltState) (ea : Nat) (value : BitVec 8) : Option SailJoltState :=
  if !effective_address_ok state.jolt_device ea true then none
  else if !protected_store_ok state ea (value.zeroExtend 64) 1 then none
  else if RAM_START_ADDRESS ≤ ea then
    some { state with sail := { state.sail with mem := state.sail.mem.insert ea value } }
  else if unsupported_store ea then none
  else (state.jolt_device.store? state.sail.mem ea value).map
    fun mem => { state with sail := { state.sail with mem := mem } }

/-- Whether `trace_load` can record the containing doubleword (`ea & !7`).
For example, address 12 records the word at 8, rather than an eight-byte window at 12. -/
def trace_load_ok (device : JoltDevice) (ea : Nat) : Bool :=
  effective_address_ok device ea false &&
    (if ea < RAM_START_ADDRESS then
      (List.range 8).all fun k => device.readable (ea / 8 * 8 + k)
    else ea / 8 * 8 + 8 ≤ ram_backing_end device)

/-- One-byte traced load (`Mmu::load`); for example, address zero fails before reading. -/
def load? (state : SailJoltState) (ea : Nat) : Option (BitVec 8) :=
  if trace_load_ok state.jolt_device ea then load_raw? state ea else none

def load (address : BitVec 64) : JoltMonad (Result (BitVec 8) ExecutionResult) := fun state =>
  match load? state address.toNat with
  | some value => .ok (.Ok value) state
  | none => .error (Error.Assertion "Load Failed") state

-- RAM: Rust checks only the start address, then reads 64 bits.
-- Device: Rust reads 8 addresses one at a time through load_raw.
-- See : jolt/tracer/src/emulator/mmu.rs (Mmu::load_doubleword) at ff6fc6568
--       jolt/tracer/src/emulator/mmu.rs (Mmu::load_doubleword_raw) at ff6fc6568
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
-- See : jolt/tracer/src/emulator/mmu.rs (Mmu::store_doubleword) at ff6fc6568
--       jolt/tracer/src/emulator/mmu.rs (Mmu::store_doubleword_raw) at ff6fc6568
noncomputable def store_doubleword (address value : BitVec 64) :
    JoltMonad (Result Bool ExecutionResult) := fun state =>
  let ea := address.toNat
  if ea % 8 ≠ 0 then .error (Error.Assertion "Unaligned store_doubleword") state
  else if RAM_START_ADDRESS ≤ ea then
    if effective_address_ok state.jolt_device ea true && protected_store_ok state ea value 8 then
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

/-- The doubleword recorded by the tracer, from shared memory with zero defaults.
For example, an untouched but mapped I/O-gap word records zero. -/
noncomputable def trace_doubleword? (state : SailJoltState) (address : BitVec 64) :
    Option (BitVec 64) :=
  let ea := address.toNat
  if ea < RAM_START_ADDRESS then
    read_doubleword? (state.jolt_device.load? state.sail.mem) ea
  else if ea + 8 ≤ Mmu.ram_backing_end state.jolt_device then
    some (Mmu.ram_doubleword state.sail.mem ea)
  else none

end JoltISA
