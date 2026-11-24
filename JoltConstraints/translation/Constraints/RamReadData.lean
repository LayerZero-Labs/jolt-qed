import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.witness
import JoltConstraints.translation.witness_helpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Lowest byte address of the RAM witness domain, including both advice regions.
Rust: https://github.com/abiswas3/jolt/tree/main/common/src/jolt_device.rs#L491-L493 -/
def ramLowestAddress (layout : MemoryLayout) : Nat :=
  min layout.trusted_advice_start.toNat layout.untrusted_advice_start.toNat

/-- The initial RAM image, including public inputs and both advice buffers.
Advice words are execution inputs, not additional public constants. Reuse the
existing image encoding; this function does not execute instructions.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-witness/src/backend/trace/ram.rs#L81-L130 -/
noncomputable def ramInitialValue {F : Type} [Field F]
    (initialRam : Nat → BitVec 64) (address : Nat) : F :=
  ((initialRam address).toNat : F)

/-- Public I/O mask: remapped words from input_start up to output_end,
excluding output_end. As in Rust preprocessing, the layout must be valid;
completeness theorems assume the relevant part as `JoltDevice.AdviceBelowInput`.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-trace/src/preprocess/public_io.rs#L20-L25 -/
def ramPublicIoMask {F : Type} [Field F] (io : JoltPublicIo) (address : Nat) : F :=
  let lowest := ramLowestAddress io.memory_layout
  let first := (io.memory_layout.input_start.toNat - lowest) / 8
  let last := (io.memory_layout.output_end.toNat - lowest) / 8
  if first ≤ address ∧ address < last then 1 else 0

/-- Public I/O words only: inputs and outputs, with zero elsewhere. Byte buffers are packed little-endian and the
last partial word is zero-padded. Advice buffers do not enter this array.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-trace/src/preprocess/public_io.rs#L27-L55 -/
def ramPublicIoWord (io : JoltPublicIo) (address : Nat) : BitVec 64 :=
  let input := TraceWitness.overlayRamBytes io.memory_layout io.memory_layout.input_start io.inputs address 0
  let output := TraceWitness.overlayRamBytes io.memory_layout io.memory_layout.output_start io.outputs address input
  output

end JoltConstraints
