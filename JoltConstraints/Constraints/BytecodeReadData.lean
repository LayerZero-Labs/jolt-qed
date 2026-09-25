import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.metadata

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- A bytecode address digit, most significant first, with leading zero bits.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-witness/src/witnesses/one_hot.rs#L19-L58 -/
def bytecodeAddressChunk (params : WitnessParams) (address : Fin (2 ^ params.logBytecodeK))
    (chunk : Fin params.bytecodeChunks) : Fin (2 ^ params.chunkBits) :=
  ⟨(address.val / 2 ^ ((params.bytecodeChunks - 1 - chunk.val) * params.chunkBits)) %
      2 ^ params.chunkBits,
    Nat.mod_lt _ (pow_pos (by decide : 0 < (2 : Nat)) _)⟩

/-- The full bytecode selector, defined from the witness's committed chunks.
This is an abbreviation, not an additional witness column.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L724-L733 -/
noncomputable def bytecodeRa {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) (address : Fin (2 ^ params.logBytecodeK))
    (t : Fin params.traceLength) : F :=
  ∏ chunk : Fin params.bytecodeChunks,
    witness.BytecodeRaChunk chunk (bytecodeAddressChunk params address chunk) t

/-- The fixed expanded program at its padded bytecode slot. Slot 0 and slots
beyond the program are no-ops, represented by `none`; array index i occupies
slot i + 1. These tables depend only on the program, not on the execution trace.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-program/src/preprocess/bytecode.rs#L47-L51 -/
def bytecodeRow (program : JoltProgram) (address : Nat) : Option JoltProgramRow :=
  match address with
  | 0 => none
  | index + 1 => program.expandedBytecode[index]?

/-- The fixed row's raw instruction address, encoded in the field; zero for no-ops.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L545-L552 -/
def bytecodeAddress {F : Type} [Field F] (program : JoltProgram) (address : Nat) : F :=
  match bytecodeRow program address with
  | some row => (row.address.toNat : F)
  | none => 0

/-- The normalized row immediate, encoded by an integer-to-field cast.
Use the shared metadata normalization, including signed load/store offsets.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L551-L574 -/
def bytecodeImmediate {F : Type} [Field F] (program : JoltProgram) (address : Nat) : F :=
  match bytecodeRow program address with
  | some row => (JoltMetadata.immediate row.instruction : F)
  | none => 0

/-- Fixed circuit flags. A padding no-op sets only DoNotUpdateUnexpandedPC.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-riscv/src/instructions/mod.rs#L536-L547 -/
def bytecodeCircuitFlag {F : Type} [Field F] (program : JoltProgram)
    (flag : CircuitFlags) (address : Nat) : F :=
  match bytecodeRow program address with
  | some row => if JoltMetadata.circuitFlag row flag then 1 else 0
  | none => if flag = .DoNotUpdateUnexpandedPC then 1 else 0

/-- Fixed instruction flags. A padding no-op sets only IsNoop.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-riscv/src/instructions/mod.rs#L550-L560 -/
def bytecodeInstructionFlag {F : Type} [Field F] (program : JoltProgram)
    (flag : InstructionFlags) (address : Nat) : F :=
  match bytecodeRow program address with
  | some row => if JoltMetadata.instructionFlag row.instruction flag then 1 else 0
  | none => if flag = .IsNoop then 1 else 0

end JoltConstraints
