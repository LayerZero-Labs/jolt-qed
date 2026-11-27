import JoltConstraints.translation.witness_helpers.ram_state

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Lowest byte address of the RAM witness domain, including both advice regions.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/common/src/jolt_device.rs -/
def ramLowestAddress (layout : MemoryLayout) : Nat :=
  min layout.trusted_advice_start.toNat layout.untrusted_advice_start.toNat

/-- The initial RAM image, including public inputs and both advice buffers.
Advice words are execution inputs, not additional public constants. Reuse the
existing image encoding; this function does not execute instructions.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-witness/src/backend/trace/ram.rs#L81-L130 -/
noncomputable def ramInitialValue {F : Type} [Field F]
    (initialRam : Nat → BitVec 64) (address : Nat) : F :=
  ((initialRam address).toNat : F)

/-- Public I/O mask: remapped words from input_start up to output_end,
excluding output_end.
The checked layout and protected input bytes supply the completeness proof.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-program/src/preprocess/public_io.rs#L22-L29 -/
def ramPublicIoMask {F : Type} [Field F] (io : JoltPublicIo) (address : Nat) : F :=
  let lowest := ramLowestAddress io.memory_layout
  let first := (io.memory_layout.input_start.toNat - lowest) / 8
  let last := (io.memory_layout.output_end.toNat - lowest) / 8
  if first ≤ address ∧ address < last then 1 else 0

/-- Public I/O words only: inputs and outputs, with zero elsewhere. Byte buffers are packed little-endian and the
last partial word is zero-padded. Advice buffers do not enter this array.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-program/src/preprocess/public_io.rs#L31-L65 -/
def ramPublicIoWord (io : JoltPublicIo) (address : Nat) : BitVec 64 :=
  let input := TraceWitness.overlayRamBytes io.memory_layout io.memory_layout.input_start io.inputs address 0
  let output := TraceWitness.overlayRamBytes io.memory_layout io.memory_layout.output_start io.outputs address input
  output

end JoltConstraints
