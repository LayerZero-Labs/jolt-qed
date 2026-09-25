import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Lowest byte address of the RAM witness domain, including both advice regions.
Rust: https://github.com/abiswas3/jolt/tree/main/common/src/jolt_device.rs#L491-L493 -/
def ramLowestAddress (layout : JoltIOLayout) : Nat :=
  min layout.trustedAdvice.1.toNat layout.untrustedAdvice.1.toNat

/-- The initial RAM image, including public inputs and both advice buffers.
Advice words are execution inputs, not additional public constants. Reuse the
existing image encoding; this function does not execute instructions.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-witness/src/backend/trace/ram.rs#L81-L130 -/
noncomputable def ramInitialValue {F : Type} [Field F]
    (program : JoltProgram) (address : Nat) : F :=
  ((HonestWitness.initialRamWord program address).toNat : F)

/-- Public I/O mask: remapped words from input_start up to RAM_START_ADDRESS,
excluding RAM_START_ADDRESS. As in Rust preprocessing, the layout must be valid;
layout admissibility is a separate completeness obligation.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-program/src/preprocess/public_io.rs#L20-L25 -/
def ramPublicIoMask {F : Type} [Field F] (io : JoltIOState) (address : Nat) : F :=
  let lowest := ramLowestAddress io.layout
  let first := (io.layout.input.1.toNat - lowest) / 8
  let last := (JoltISA.ramStartAddress - lowest) / 8
  if first ≤ address ∧ address < last then 1 else 0

/-- Public I/O words only: input, output, panic, and termination (1 unless
panicking), with zero elsewhere. Byte buffers are packed little-endian and the
last partial word is zero-padded. Advice buffers do not enter this array.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-program/src/preprocess/public_io.rs#L27-L55 -/
def ramPublicIoWord (io : JoltIOState) (address : Nat) : BitVec 64 :=
  let input := HonestWitness.overlayRamBytes io.layout io.layout.input.1 io.inputs address 0
  let output := HonestWitness.overlayRamBytes io.layout io.layout.output.1 io.outputs address input
  let panic := if HonestWitness.remapRamAddress io.layout io.layout.panic.1 = some address then
      (if io.panic then 1 else 0)
    else output
  if !io.panic && HonestWitness.remapRamAddress io.layout io.layout.termination.1 == some address then
    1
  else panic

/-- Actual RAM accesses are nonzero and word-aligned relative to the layout.
RamFits separately supplies successful remapping and the RAM-domain bound.
This is a condition on the recorded accesses, not an ISA execution rule. -/
def ramAccessesValid {program : JoltProgram} (trace : JoltTrace program) : Prop :=
  ∀ i : Fin trace.rows.size,
    let row := getElem trace.rows i.val i.isLt
    let instruction := program.expandedBytecode[row.rowIndex].instruction
    match HonestWitness.ramAccessAddress instruction row.preState with
    | none => True
    | some address => address.toNat ≠ 0 ∧
        (address.toNat - ramLowestAddress program.initialState.io.layout) % 8 = 0

end JoltConstraints
