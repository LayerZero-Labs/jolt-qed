-- Rust: jolt/common/src/jolt_device.rs and jolt/common/src/constants.rs

set_option autoImplicit false

namespace JoltISA

-- Rust: jolt/common/src/constants.rs:21 (RAM_START_ADDRESS)
def RAM_START_ADDRESS : Nat := 0x80000000

-- Rust: jolt/common/src/constants.rs:26 (STACK_CANARY_SIZE)
def STACK_CANARY_SIZE : Nat := 128

end JoltISA

-- Rust: jolt/common/src/jolt_device.rs:248-256 (MemoryConfig)
structure MemoryConfig where
  max_input_size : BitVec 64
  max_trusted_advice_size : BitVec 64
  max_untrusted_advice_size : BitVec 64
  max_output_size : BitVec 64
  stack_size : BitVec 64
  heap_size : BitVec 64
  program_size : Option (BitVec 64)

-- Rust: jolt/common/src/jolt_device.rs:277-301 (MemoryLayout)
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
  panic : BitVec 64
  termination : BitVec 64
  io_end : BitVec 64

namespace MemoryLayout

-- Arithmetic is on Nat. Every Rust `checked_*(..).expect(..)` and `assert!`
-- becomes `none`, so `new` returns `none` exactly where Rust panics.

def checkedAdd (a b : Nat) : Option Nat :=
  if a + b < 2 ^ 64 then some (a + b) else none

def checkedSub (a b : Nat) : Option Nat :=
  if b ≤ a then some (a - b) else none

def checkedMul (a b : Nat) : Option Nat :=
  if a * b < 2 ^ 64 then some (a * b) else none

-- Rust: align_up(val, 8), local to MemoryLayout::new
def alignUp8 (val : Nat) : Option Nat :=
  if val % 8 = 0 then some val else checkedAdd val (8 - val % 8)

def powerOfTwoOrZero (n : Nat) : Bool :=
  n == 0 || n.nextPowerOfTwo == n

-- The larger advice region (trusted on a tie) starts io_bytes below RAM; the other
-- starts where it ends. Gives (trusted start, trusted end, untrusted start, untrusted end).
-- Rust: jolt/common/src/jolt_device.rs:402-429 (inside MemoryLayout::new)
def adviceRegions (trusted_size untrusted_size io_bytes : Nat) : Option (Nat × Nat × Nat × Nat) :=
  if untrusted_size ≤ trusted_size then do
    let trusted_start ← checkedSub JoltISA.RAM_START_ADDRESS io_bytes
    let trusted_end ← checkedAdd trusted_start trusted_size
    let untrusted_end ← checkedAdd trusted_end untrusted_size
    pure (trusted_start, trusted_end, trusted_end, untrusted_end)
  else do
    let untrusted_start ← checkedSub JoltISA.RAM_START_ADDRESS io_bytes
    let untrusted_end ← checkedAdd untrusted_start untrusted_size
    let trusted_end ← checkedAdd untrusted_end trusted_size
    pure (untrusted_end, trusted_end, untrusted_start, untrusted_end)

-- Rust: jolt/common/src/jolt_device.rs:348-484 (MemoryLayout::new)
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

  -- 16 bytes for the panic word and the termination word.
  let io_region_bytes ← (checkedAdd max_input_size max_trusted_advice_size)
    >>= (checkedAdd · max_untrusted_advice_size)
    >>= (checkedAdd · max_output_size)
    >>= (checkedAdd · 16)
  let io_region_words := (io_region_bytes / 8).nextPowerOfTwo
  let io_bytes ← checkedMul io_region_words 8

  let (trusted_advice_start, trusted_advice_end, untrusted_advice_start, untrusted_advice_end) ←
    adviceRegions max_trusted_advice_size max_untrusted_advice_size io_bytes

  let input_start := max untrusted_advice_end trusted_advice_end
  let input_end ← checkedAdd input_start max_input_size
  let output_start := input_end
  let output_end ← checkedAdd output_start max_output_size
  let panic := output_end
  let termination ← checkedAdd panic 8
  let io_end ← checkedAdd termination 8

  let stack_end ← checkedAdd JoltISA.RAM_START_ADDRESS program_size.toNat
  let stack_start ← (checkedAdd stack_end JoltISA.STACK_CANARY_SIZE) >>= (checkedAdd · stack_size)
  let heap_end ← checkedAdd stack_start heap_size

  some
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
      panic := BitVec.ofNat 64 panic
      termination := BitVec.ofNat 64 termination
      io_end := BitVec.ofNat 64 io_end }

-- Rust: jolt/common/src/jolt_device.rs:486-488
def get_lowest_address (layout : MemoryLayout) : BitVec 64 :=
  if layout.trusted_advice_start.toNat ≤ layout.untrusted_advice_start.toNat
  then layout.trusted_advice_start
  else layout.untrusted_advice_start

-- Rust: jolt/common/src/jolt_device.rs:512-514
def get_total_memory_size (layout : MemoryLayout) : BitVec 64 :=
  layout.heap_end - BitVec.ofNat 64 JoltISA.RAM_START_ADDRESS

end MemoryLayout

-- Rust: jolt/common/src/jolt_device.rs:57-68 (JoltDevice)
structure JoltDevice where
  inputs : Array (BitVec 8)
  trusted_advice : Array (BitVec 8)
  untrusted_advice : Array (BitVec 8)
  outputs : Array (BitVec 8)
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
    address < device.memory_layout.termination.toNat

def is_panic (device : JoltDevice) (address : Nat) : Bool :=
  device.memory_layout.panic.toNat ≤ address &&
    address < device.memory_layout.termination.toNat

def is_termination (device : JoltDevice) (address : Nat) : Bool :=
  device.memory_layout.termination.toNat ≤ address &&
    address < device.memory_layout.io_end.toNat

-- Rust: jolt/common/src/jolt_device.rs:121-148 (JoltDevice::load).
-- Device buffers are zero-padded by Rust. This is distinct from a missing Sail
-- RAM byte, which trace_doubleword? below leaves absent.
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
