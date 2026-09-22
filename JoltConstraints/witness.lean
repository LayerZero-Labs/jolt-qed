import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false

-- Rust paths below are relative to /Users/ari.biswas/Work-with-A16z/jolt.

-- Rust: crates/jolt-riscv/src/flags.rs::CircuitFlags.
-- TODO: For each constructor write a simple english description
-- of what it means.
inductive CircuitFlags where
  | AddOperands | SubtractOperands | MultiplyOperands
  | Load | Store | Jump | WriteLookupOutputToRD
  | VirtualInstruction | Assert | DoNotUpdateUnexpandedPC | Advice
  | IsCompressed | IsFirstInSequence | IsLastInSequence
  deriving DecidableEq, Fintype

-- Rust: crates/jolt-riscv/src/flags.rs::InstructionFlags.
-- Names are quite self explanatory.
inductive InstructionFlags where
  | LeftOperandIsPC | RightOperandIsImm
  | LeftOperandIsRs1Value | RightOperandIsRs2Value | Branch | IsNoop
  deriving DecidableEq, Fintype

-- Rust: crates/jolt-lookup-tables/src/tables/mod.rs::LookupTableKind<64>.
-- These is the List of names of all the Lookup tables in Jolt.
inductive LookupTableKind where
  | RangeCheck
  | RangeCheckAligned
  | And
  | Andn
  | Or
  | Xor
  | Equal
  | SignedGreaterThanEqual
  | UnsignedGreaterThanEqual
  | NotEqual
  | SignedLessThan
  | UnsignedLessThan
  | SignMask
  | UpperWord
  | UnsignedLessThanEqual
  | ValidUnsignedRemainder
  | ValidDiv0
  | HalfwordAlignment
  | WordAlignment
  | LowerHalfWord
  | SignExtendWord
  | Pow2
  | Pow2W
  | ShiftRightBitmask
  | VirtualRev8W
  | VirtualSRL
  | VirtualSRA
  | VirtualROTR
  | VirtualROTRW
  | VirtualNegateIf
  | MulUNoOverflow
  | VirtualXORROT32
  | VirtualXORROT24
  | VirtualXORROT16
  | VirtualXORROT63
  | VirtualXORROTW16
  | VirtualXORROTW12
  | VirtualXORROTW8
  | VirtualXORROTW7
  | WindowMaskW
  | PextSigned
  | VirtualXORROTW22
  | VirtualXORROTW19
  | VirtualXORROTW6
  | ShiftRightBitmaskW
  | VirtualSRLW
  | VirtualSRAW
  | Pext
  | WindowMaskB
  | WindowMaskH
  | AlignAddr
  | ShiftDataB
  | ShiftDataH
  | ShiftDataW
  deriving DecidableEq, Fintype

-- These are the things God gives before we can begin Jolt. Some are free params, some are derived from the users program.
-- Rust: crates/jolt-claims/src/protocols/jolt/geometry/dimensions.rs::JoltOneHotDimensions.
structure WitnessParams where
  -- Rust: crates/jolt-claims/src/protocols/jolt/geometry/dimensions.rs::TraceDimensions::log_t.
  -- Base-two logarithm of the padded witness length; actual execution may be shorter.
  logT : Nat
  -- Rust: crates/jolt-claims/src/protocols/jolt/geometry/dimensions.rs::ReadWriteDimensions::log_k.
  logRamK : Nat
  -- Rust: crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs::BytecodeReadRafDimensions::log_k.
  logBytecodeK : Nat
  -- Rust: crates/jolt-claims/src/protocols/jolt/geometry/dimensions.rs::JoltOneHotDimensions::committed_chunk_bits.
  chunkBits : Nat
  -- Rust: crates/jolt-claims/src/protocols/jolt/geometry/dimensions.rs::JoltOneHotDimensions::lookup_virtual_chunk_bits.
  virtualChunkBits : Nat
  -- Rust: crates/jolt-claims/src/protocols/jolt/geometry/dimensions.rs::JoltFormulaDimensions::try_from.
  chunkBits_pos : 0 < chunkBits
  virtualChunkBits_pos : 0 < virtualChunkBits
  chunkBits_dvd_virtual : chunkBits ∣ virtualChunkBits
  virtualChunkBits_dvd_lookup : virtualChunkBits ∣ 128

/-- Number of witness positions, including padding, always a power of two.
`trace.rows.size` counts actual execution steps and may be smaller: for example,
six execution steps can occupy an eight-position witness, with two padding positions.
Rust: [walk_cycles](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/cycle.rs:107).
-/
def WitnessParams.traceLength (p : WitnessParams) : Nat := 2 ^ p.logT

-- Rust: crates/jolt-witness/src/backend/trace/mod.rs::ram_log_k.
def WitnessParams.ramSize (p : WitnessParams) : Nat := 2 ^ p.logRamK

-- Rust: crates/jolt-claims/src/protocols/jolt/geometry/dimensions.rs::JoltFormulaDimensions::try_from (instruction_d).
-- Rust: crates/jolt-witness/src/backend/trace/mod.rs::RV64_LOOKUP_ADDRESS_BITS = 128.
def WitnessParams.instructionChunks (p : WitnessParams) : Nat :=
  (128 + p.chunkBits - 1) / p.chunkBits

-- Rust: crates/jolt-claims/src/protocols/jolt/geometry/dimensions.rs::JoltFormulaDimensions::try_from (bytecode_d).
def WitnessParams.bytecodeChunks (p : WitnessParams) : Nat :=
  (p.logBytecodeK + p.chunkBits - 1) / p.chunkBits

-- Rust: crates/jolt-claims/src/protocols/jolt/geometry/dimensions.rs::JoltFormulaDimensions::try_from (ram_d).
def WitnessParams.ramChunks (p : WitnessParams) : Nat :=
  (p.logRamK + p.chunkBits - 1) / p.chunkBits

-- Rust: crates/jolt-claims/src/protocols/jolt/geometry/dimensions.rs::JoltFormulaDimensions::try_from (virtual_instruction_ra_polys).
def WitnessParams.virtualInstructionChunks (p : WitnessParams) : Nat :=
  128 / p.virtualChunkBits

-- TODO: constraints.md variable families; this aggregate is a Lean representation.
-- Rust: crates/jolt-witness/src/backend/trace/oracle.rs::shape_of and oracle_table.
-- TODO: Value representation remains a parameter; constraints and the honest construction are separate.
-- Every `Fin p.traceLength` index ranges over the padded witness positions.
-- Positions beyond the execution trace use the padding value for that column.
structure WitnessType (Value : Type) (p : WitnessParams) where
  -- Rust: crates/jolt-witness/src/witnesses/pc.rs::Pc.
  PC : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/pc.rs::UnexpandedPc.
  UnexpandedPC : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/operands.rs::Imm.
  Imm : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/registers.rs::Rs1Value.
  Rs1Value : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/registers.rs::Rs2Value.
  Rs2Value : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/registers.rs::RdWriteValue.
  RdWriteValue : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/ram.rs::RamAddress.
  RamAddress : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/ram.rs::RamReadValue.
  RamReadValue : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/ram.rs::RamWriteValue.
  RamWriteValue : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/operands.rs::LeftInstructionInput.
  LeftInstructionInput : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/operands.rs::RightInstructionInput.
  RightInstructionInput : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/operands.rs::LeftLookupOperand.
  LeftLookupOperand : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/operands.rs::RightLookupOperand.
  RightLookupOperand : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/lookups.rs::LookupOutput.
  LookupOutput : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/operands.rs::Product.
  Product : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/flags.rs::ShouldBranch.
  ShouldBranch : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/flags.rs::ShouldJump.
  ShouldJump : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/pc.rs::NextUnexpandedPc.
  NextUnexpandedPC : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/pc.rs::NextPc.
  NextPC : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/flags.rs::NextIsVirtual.
  NextIsVirtual : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/flags.rs::NextIsFirstInSequence.
  NextIsFirstInSequence : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/flags.rs::NextIsNoop.
  NextIsNoop : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/flags.rs::OpFlag.
  OpFlags : CircuitFlags → Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/flags.rs::InstructionFlag.
  InstructionFlags : _root_.InstructionFlags → Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/flags.rs::LookupTableFlag.
  LookupTableFlag : LookupTableKind → Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/flags.rs::InstructionRafFlag.
  InstructionRafFlag : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/increments.rs::RdInc.
  RdInc : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/increments.rs::RamInc.
  RamInc : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/ram.rs::RamHammingWeight.
  RamHammingWeight : Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/backend/trace/registers.rs::materialize_register_read_write_virtual.
  -- Rust: common/src/constants.rs::REGISTER_COUNT = 128.
  Rs1Ra : Fin 128 → Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/backend/trace/registers.rs::materialize_register_read_write_virtual.
  -- Rust: common/src/constants.rs::REGISTER_COUNT = 128.
  Rs2Ra : Fin 128 → Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/backend/trace/registers.rs::materialize_register_read_write_virtual.
  -- Rust: common/src/constants.rs::REGISTER_COUNT = 128.
  RdWa : Fin 128 → Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/backend/trace/registers.rs::materialize_register_read_write_virtual.
  -- Rust: common/src/constants.rs::REGISTER_COUNT = 128.
  RegistersVal : Fin 128 → Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/backend/trace/ram.rs::materialize_ram_ra.
  RamRa : Fin p.ramSize → Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/backend/trace/ram.rs::materialize_ram_val.
  RamVal : Fin p.ramSize → Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/backend/trace/ram.rs::materialize_ram_val_final.
  RamValFinal : Fin p.ramSize → Value
  -- Rust: crates/jolt-witness/src/witnesses/one_hot.rs::InstructionRaChunk.
  -- Rust: crates/jolt-witness/src/backend/trace/cycle.rs::materialize_one_hot.
  InstructionRaChunk : Fin p.instructionChunks → Fin (2 ^ p.chunkBits) → Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/one_hot.rs::BytecodeRaChunk.
  -- Rust: crates/jolt-witness/src/backend/trace/cycle.rs::materialize_one_hot.
  BytecodeRaChunk : Fin p.bytecodeChunks → Fin (2 ^ p.chunkBits) → Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/witnesses/one_hot.rs::RamRaChunk.
  -- Rust: crates/jolt-witness/src/backend/trace/cycle.rs::materialize_one_hot.
  RamRaChunk : Fin p.ramChunks → Fin (2 ^ p.chunkBits) → Fin p.traceLength → Value
  -- Rust: crates/jolt-witness/src/backend/trace/oracle.rs::oracle_table (InstructionRa).
  InstructionRa : Fin p.virtualInstructionChunks → Fin (2 ^ p.virtualChunkBits) → Fin p.traceLength → Value

-- TODO: Honest filling must use JoltBytecode/JoltISA/Semantics.lean::execInstr.
-- TODO: Reuse JoltBytecode/JoltISA/Instruction.lean and Core.lean; do not invent Program or State.
-- Rust extraction: crates/jolt-witness/src/witnesses/ and crates/jolt-witness/src/backend/trace/.
