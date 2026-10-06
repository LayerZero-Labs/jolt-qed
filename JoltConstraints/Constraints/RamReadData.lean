import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Lowest byte address of the RAM witness domain, including both advice regions.
Rust: https://github.com/abiswas3/jolt/tree/main/common/src/jolt_device.rs#L491-L493 -/
def ramLowestAddress (layout : MemoryLayout) : Nat :=
  min layout.trusted_advice_start.toNat layout.untrusted_advice_start.toNat

/-- Both advice buffers of a device lie below `input_start`, and `input_start`
is a whole number of words above the lowest RAM address. These are the only
layout facts the public-output constraint (26) needs: together they keep every
advice byte out of the public I/O interval.

Rust establishes them before execution starts:
`JoltDevice.AdviceBelowInput.of_memoryLayout` derives them from Rust's
`MemoryLayout::new` and the advice-length checks in `create_emulator`. -/
structure _root_.JoltDevice.AdviceBelowInput (io : JoltDevice) : Prop where
  inputWordAligned : (io.memory_layout.input_start.toNat - ramLowestAddress io.memory_layout) % 8 = 0
  trustedAdviceBelowInput :
    io.memory_layout.trusted_advice_start.toNat + io.trusted_advice.size ≤ io.memory_layout.input_start.toNat
  untrustedAdviceBelowInput :
    io.memory_layout.untrusted_advice_start.toNat + io.untrusted_advice.size ≤ io.memory_layout.input_start.toNat

/-- The initial RAM image, including public inputs and both advice buffers.
Advice words are execution inputs, not additional public constants. Reuse the
existing image encoding; this function does not execute instructions.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-witness/src/backend/trace/ram.rs#L81-L130 -/
noncomputable def ramInitialValue {F : Type} [Field F]
    (program : JoltProgram) (address : Nat) : F :=
  ((HonestWitness.initialRamWord program address).toNat : F)

/-- Public I/O mask: remapped words from input_start up to RAM_START_ADDRESS,
excluding RAM_START_ADDRESS. As in Rust preprocessing, the layout must be valid;
completeness theorems assume the relevant part as `JoltDevice.AdviceBelowInput`.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-program/src/preprocess/public_io.rs#L20-L25 -/
def ramPublicIoMask {F : Type} [Field F] (io : JoltDevice) (address : Nat) : F :=
  let lowest := ramLowestAddress io.memory_layout
  let first := (io.memory_layout.input_start.toNat - lowest) / 8
  let last := (JoltISA.RAM_START_ADDRESS - lowest) / 8
  if first ≤ address ∧ address < last then 1 else 0

/-- Public I/O words only: input, output, panic, and termination (1 unless
panicking), with zero elsewhere. Byte buffers are packed little-endian and the
last partial word is zero-padded. Advice buffers do not enter this array.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-program/src/preprocess/public_io.rs#L27-L55 -/
def ramPublicIoWord (io : JoltDevice) (address : Nat) : BitVec 64 :=
  let input := HonestWitness.overlayRamBytes io.memory_layout io.memory_layout.input_start io.inputs address 0
  let output := HonestWitness.overlayRamBytes io.memory_layout io.memory_layout.output_start io.outputs address input
  let panic := if HonestWitness.remapRamAddress io.memory_layout io.memory_layout.panic = some address then
      (if io.panic then 1 else 0)
    else output
  if !io.panic && HonestWitness.remapRamAddress io.memory_layout io.memory_layout.termination == some address then
    1
  else panic

/-- Actual RAM accesses are nonzero and word-aligned relative to the layout.
RamFits separately supplies successful remapping and the RAM-domain bound.
This is a condition on the recorded accesses, not an ISA execution rule. -/
def ramAccessesValid {program : JoltProgram} (trace : JoltTrace program) : Prop :=
  ∀ i : Fin trace.rows.size,
    let row := getElem trace.rows i.val i.isLt
    let instruction := program.expandedBytecode[row.rowIndex].expandedInstruction
    match HonestWitness.ramAccessAddress instruction row.preState with
    | none => True
    | some address => address.toNat ≠ 0 ∧
        (address.toNat - ramLowestAddress program.initialState.jolt_device.memory_layout) % 8 = 0

end JoltConstraints
