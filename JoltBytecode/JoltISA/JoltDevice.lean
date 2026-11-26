import Std.Data.ExtHashMap

-- Rust layout source: common/src/jolt_device.rs at public pin 8bbb2357.
-- https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/common/src/jolt_device.rs#L381-L533
-- Constants: common/src/constants.rs at public pin 8bbb2357.
-- https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/common/src/constants.rs#L21-L30

set_option autoImplicit false

namespace JoltISA

-- Rust: jolt/common/src/constants.rs:21 (RAM_START_ADDRESS)
def RAM_START_ADDRESS : Nat := 0x80000000

-- Rust: jolt/common/src/constants.rs:26 (STACK_CANARY_SIZE)
def STACK_CANARY_SIZE : Nat := 128

end JoltISA

-- Rust: jolt/common/src/jolt_device.rs:273-281 (MemoryConfig)
structure MemoryConfig where
  max_input_size : BitVec 64
  max_trusted_advice_size : BitVec 64
  max_untrusted_advice_size : BitVec 64
  max_output_size : BitVec 64
  stack_size : BitVec 64
  heap_size : BitVec 64
  program_size : Option (BitVec 64)

-- Rust: jolt/common/src/jolt_device.rs:302-326 (MemoryLayout)
structure MemoryLayout where
  program_size : BitVec 64
  max_trusted_advice_size : BitVec 64
  trusted_advice_start : BitVec 64
  trusted_advice_end : BitVec 64
  max_untrusted_advice_size : BitVec 64
  untrusted_advice_start : BitVec 64
  untrusted_advice_end : BitVec 64
  max_input_size : BitVec 64
  max_output_size : BitVec 64
  input_start : BitVec 64
  input_end : BitVec 64
  output_start : BitVec 64
  output_end : BitVec 64
  stack_size : BitVec 64
  stack_end : BitVec 64
  heap_size : BitVec 64
  heap_end : BitVec 64
  io_end : BitVec 64
  deriving DecidableEq

namespace MemoryLayout

-- Arithmetic is on Nat. `new` models `MemoryLayout::try_new`, erasing error
-- variants: `Ok layout` becomes `some layout`, and every `Err` becomes `none`.
-- Rust's `MemoryLayout::new` unwraps that result, panicking on the same failures.

def checkedAdd (a b : Nat) : Option Nat :=
  if a + b < 2 ^ 64 then some (a + b) else none

def checkedSub (a b : Nat) : Option Nat :=
  if b ≤ a then some (a - b) else none

def checkedMul (a b : Nat) : Option Nat :=
  if a * b < 2 ^ 64 then some (a * b) else none

-- Rust: align_up(val, region), local to MemoryLayout::try_new (387-394)
def alignUp8 (val : Nat) : Option Nat :=
  if val % 8 = 0 then some val else checkedAdd val (8 - val % 8)

def powerOfTwoOrZero (n : Nat) : Bool :=
  n == 0 || n.nextPowerOfTwo == n

-- The larger advice region (trusted on a tie) starts io_bytes below RAM; the other
-- starts where it ends. Gives (trusted start, trusted end, untrusted start, untrusted end).
-- Rust: jolt/common/src/jolt_device.rs:435-477 (inside MemoryLayout::try_new)
def adviceRegions (trusted_size untrusted_size io_bytes : Nat) : Option (Nat × Nat × Nat × Nat) := do
  let io_start ← checkedSub JoltISA.RAM_START_ADDRESS io_bytes
  -- Zero is the no-access sentinel, so the padded region must start above it.
  if io_start = 0 then none else
  if untrusted_size ≤ trusted_size then do
    let trusted_start := io_start
    let trusted_end ← checkedAdd trusted_start trusted_size
    let untrusted_end ← checkedAdd trusted_end untrusted_size
    pure (trusted_start, trusted_end, trusted_end, untrusted_end)
  else do
    let untrusted_start := io_start
    let untrusted_end ← checkedAdd untrusted_start untrusted_size
    let trusted_end ← checkedAdd untrusted_end trusted_size
    pure (untrusted_end, trusted_end, untrusted_start, untrusted_end)

-- Rust: jolt/common/src/jolt_device.rs:535-537
def get_lowest_address (layout : MemoryLayout) : BitVec 64 :=
  if layout.trusted_advice_start.toNat ≤ layout.untrusted_advice_start.toNat
  then layout.trusted_advice_start
  else layout.untrusted_advice_start

def io_segments_ok (l : MemoryLayout) : Bool := Id.run do
  let t := (l.trusted_advice_start.toNat, l.trusted_advice_end.toNat,
    l.max_trusted_advice_size.toNat)
  let u := (l.untrusted_advice_start.toNat, l.untrusted_advice_end.toNat,
    l.max_untrusted_advice_size.toNat)
  let advice := if t.1 < u.1 || (t.1 == u.1 && t.2.1 ≤ u.2.1) then [t, u] else [u, t]
  let mut previous := l.get_lowest_address.toNat
  for (start, stop, size) in advice ++
      [(l.input_start.toNat, l.input_end.toNat, l.max_input_size.toNat),
       (l.output_start.toNat, l.output_end.toNat, l.max_output_size.toNat)] do
    if start != previous || start % 8 != 0 || size % 8 != 0 || stop != start + size then
      return false
    previous := stop
  return powerOfTwoOrZero t.2.2 && powerOfTwoOrZero u.2.2 &&
    l.io_end.toNat == previous && l.io_end.toNat ≤ JoltISA.RAM_START_ADDRESS &&
    (t.2.2 == 0 || (t.1 - l.get_lowest_address.toNat) % t.2.2 == 0) &&
    (u.2.2 == 0 || (u.1 - l.get_lowest_address.toNat) % u.2.2 == 0)

def max_ram_k? (layout : MemoryLayout) : Option Nat := do
  guard (layout.heap_end.toNat ≤ 2^64 - 8 && layout.heap_end.toNat % 8 == 0)
  guard layout.io_segments_ok
  let total ← checkedSub layout.heap_end.toNat layout.get_lowest_address.toNat
  let words := (total / 8).nextPowerOfTwo
  guard (words < 2^64 && layout.get_lowest_address.toNat + 8 * words ≤ 2^64)
  pure words

def ram_size (layout : MemoryLayout) : Nat :=
  (layout.max_ram_k?.map fun k => layout.get_lowest_address.toNat + 8 * k -
    JoltISA.RAM_START_ADDRESS).getD 0

-- Rust: jolt/common/src/jolt_device.rs:381-533 (MemoryLayout::try_new)
def new (config : MemoryConfig) : Option MemoryLayout := do
  let program_size ← config.program_size
  let max_trusted_advice_size ← alignUp8 config.max_trusted_advice_size.toNat
  let max_untrusted_advice_size ← alignUp8 config.max_untrusted_advice_size.toNat
  let max_input_size ← alignUp8 config.max_input_size.toNat
  let max_output_size ← alignUp8 config.max_output_size.toNat
  let stack_size ← alignUp8 config.stack_size.toNat
  let heap_size ← alignUp8 config.heap_size.toNat
  guard (powerOfTwoOrZero max_trusted_advice_size)
  guard (powerOfTwoOrZero max_untrusted_advice_size)

  let io_region_bytes ← (checkedAdd max_input_size max_trusted_advice_size)
    >>= (checkedAdd · max_untrusted_advice_size)
    >>= (checkedAdd · max_output_size)
    >>= (checkedAdd · 8)
  -- The checked sum is below 2^64, so its quotient by eight is below 2^61.
  -- Its next power of two is at most 2^61 and cannot overflow Rust's u64.
  -- Multiplication by eight can still overflow; checkedMul rejects that case.
  let io_region_words := (io_region_bytes / 8).nextPowerOfTwo
  let io_bytes ← checkedMul io_region_words 8

  let (trusted_advice_start, trusted_advice_end, untrusted_advice_start, untrusted_advice_end) ←
    adviceRegions max_trusted_advice_size max_untrusted_advice_size io_bytes

  let input_start := max untrusted_advice_end trusted_advice_end
  let input_end ← checkedAdd input_start max_input_size
  let output_start := input_end
  let output_end ← checkedAdd output_start max_output_size
  let io_end := output_end

  let stack_end ← checkedAdd JoltISA.RAM_START_ADDRESS program_size.toNat
  let stack_start ← (checkedAdd stack_end JoltISA.STACK_CANARY_SIZE) >>= (checkedAdd · stack_size)
  let heap_end ← (checkedAdd stack_start heap_size) >>= alignUp8

  let layout : MemoryLayout :=
    { program_size := program_size
      max_trusted_advice_size := BitVec.ofNat 64 max_trusted_advice_size
      trusted_advice_start := BitVec.ofNat 64 trusted_advice_start
      trusted_advice_end := BitVec.ofNat 64 trusted_advice_end
      max_untrusted_advice_size := BitVec.ofNat 64 max_untrusted_advice_size
      untrusted_advice_start := BitVec.ofNat 64 untrusted_advice_start
      untrusted_advice_end := BitVec.ofNat 64 untrusted_advice_end
      max_input_size := BitVec.ofNat 64 max_input_size
      max_output_size := BitVec.ofNat 64 max_output_size
      input_start := BitVec.ofNat 64 input_start
      input_end := BitVec.ofNat 64 input_end
      output_start := BitVec.ofNat 64 output_start
      output_end := BitVec.ofNat 64 output_end
      stack_size := BitVec.ofNat 64 stack_size
      stack_end := BitVec.ofNat 64 stack_end
      heap_size := BitVec.ofNat 64 heap_size
      heap_end := BitVec.ofNat 64 heap_end
      io_end := BitVec.ofNat 64 io_end }

  let _ ← layout.max_ram_k?
  pure layout

def get_total_memory_size (layout : MemoryLayout) : BitVec 64 :=
  BitVec.ofNat 64 layout.ram_size

end MemoryLayout

structure JoltDevice where
  panic : Bool
  memory_layout : MemoryLayout

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
    address < device.memory_layout.output_end.toNat

def is_io_gap (device : JoltDevice) (address : Nat) : Bool :=
  device.memory_layout.io_end.toNat ≤ address && address < JoltISA.RAM_START_ADDRESS

def readable (device : JoltDevice) (address : Nat) : Bool :=
  device.is_input address || device.is_trusted_advice address ||
    device.is_untrusted_advice address || device.is_output address || device.is_io_gap address

def load? (device : JoltDevice) (mem : Std.ExtHashMap Nat (BitVec 8))
    (address : Nat) : Option (BitVec 8) :=
  if device.readable address then some ((mem.get? address).getD 0) else none

def store? (device : JoltDevice) (mem : Std.ExtHashMap Nat (BitVec 8))
    (address : Nat) (value : BitVec 8) : Option (Std.ExtHashMap Nat (BitVec 8)) :=
  if device.readable address then some (mem.insert address value) else none

def try_with_io (memory_config : MemoryConfig)
    (inputs trusted_advice untrusted_advice : Array (BitVec 8)) : Option JoltDevice := do
  let memory_layout ← MemoryLayout.new memory_config
  guard (trusted_advice.size ≤ memory_layout.max_trusted_advice_size.toNat)
  guard (untrusted_advice.size ≤ memory_layout.max_untrusted_advice_size.toNat)
  guard (inputs.size ≤ memory_layout.max_input_size.toNat)
  pure { panic := false, memory_layout }

def initial_ram_state (device : JoltDevice) (mem : Std.ExtHashMap Nat (BitVec 8))
    (inputs trusted_advice untrusted_advice : Array (BitVec 8)) : Std.ExtHashMap Nat (BitVec 8) :=
  let l := device.memory_layout
  let zeroed := (List.range (JoltISA.RAM_START_ADDRESS - l.get_lowest_address.toNat)).foldl
    (fun m k => m.insert (l.get_lowest_address.toNat + k) 0) mem
  let populate := fun (m : Std.ExtHashMap Nat (BitVec 8)) (start : Nat) (bytes : Array (BitVec 8)) =>
    bytes.toList.zipIdx.foldl (fun m (byte, k) => m.insert (start + k) byte) m
  let m := populate zeroed l.trusted_advice_start.toNat trusted_advice
  let m := populate m l.untrusted_advice_start.toNat untrusted_advice
  populate m l.input_start.toNat inputs

end JoltDevice
