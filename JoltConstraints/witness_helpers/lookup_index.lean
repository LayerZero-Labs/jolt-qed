import JoltConstraints.trace
import JoltBytecode.JoltISA.semantic_helpers

set_option autoImplicit false

namespace HonestWitness

-- Rust: [interleave_bits](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/interleave.rs:17).
-- Counting from the least significant bit, left occupies odd positions and
-- right occupies even positions: interleaveLookupOperands 1 2 = 6.
def interleaveLookupOperands (left right : BitVec 64) : BitVec 128 :=
  BitVec.ofNat 128 <|
    (List.range 64).foldl (fun address bit =>
      address + (if left.getLsbD bit then 2 ^ (2 * bit + 1) else 0) +
        (if right.getLsbD bit then 2 ^ (2 * bit) else 0)) 0

-- Rust: [LookupQuery](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/traits.rs:93).
-- Rust: [instruction implementations](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/instructions).
-- Extract the exact 128-bit lookup address before any field conversion.
-- Two-input tables interleave their operands. Arithmetic tables use the full
-- shared ISA calculation, even for W instructions whose output keeps 32 bits.
-- Advice uses the captured post-state destination. Loads/stores have index 0:
-- their memory address belongs to RamRaChunk, not InstructionRaChunk.
noncomputable def instructionLookupIndex (instruction : JoltISA.Instr)
    (address : BitVec 64) (preState postState : SailJoltState) : BitVec 128 :=
  let source := fun src => JoltISA.sourceValue src preState
  match instruction with
  -- Rust masks these immediates to 64 bits before widening to 128. In
  -- particular, -1 contributes 2^64 - 1; a carry into bit 64 is retained.
  -- Rust: [ADDI](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/instructions/riscv/addi.rs:18).
  | .ADDI _ src imm | .ADDIW _ src imm | .JALR _ src imm
  | .VirtualAlignAddr _ src imm | .VirtualWindowMaskB _ src imm
  | .VirtualWindowMaskH _ src imm | .VirtualWindowMaskW _ src imm =>
      BitVec.ofNat 128 (JoltISA.addWide (source src) imm)
  | .ADD _ lhs rhs | .ADDW _ lhs rhs =>
      BitVec.ofNat 128 (JoltISA.addWide (source lhs) (source rhs))
  | .SUB _ lhs rhs | .SUBW _ lhs rhs =>
      BitVec.ofNat 128 (JoltISA.subWide (source lhs) (source rhs))
  | .MUL _ lhs rhs | .MULW _ lhs rhs | .MULHU _ lhs rhs
  | .VirtualAssertMulUNoOverflow lhs rhs _ =>
      BitVec.ofNat 128 (JoltISA.mulWide (source lhs) (source rhs))
  | .VirtualMULI _ src imm | .VirtualMULIW _ src imm =>
      BitVec.ofNat 128 (JoltISA.mulWide (source src) imm)
  | .LUI _ imm => imm.setWidth 128
  -- Rust's FormatU decoder stores the sign-extended offset as u64 widened to
  -- i128, so AUIPC retains the unsigned 64-bit offset, including any carry.
  -- Rust: [FormatU decoding](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/image/decode.rs:471).
  | .AUIPC _ imm =>
      BitVec.ofNat 128 (JoltISA.addWide address imm)
  -- Rust: [JAL](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/instructions/riscv/jal.rs:18).
  | .JAL _ imm => BitVec.ofNat 128 (JoltISA.addWide address imm)
  -- Rust: [FormatAssert normalization](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction/format/format_assert_align.rs:107).
  | .VirtualAssertHalfwordAlignment base imm _ | .VirtualAssertWordAlignment base imm _ =>
      BitVec.ofNat 128 (JoltISA.addWide (source base) imm)
  | .ANDI _ src imm | .ORI _ src imm | .XORI _ src imm | .SLTI _ src imm | .SLTIU _ src imm =>
      interleaveLookupOperands (source src) imm
  | .BEQ lhs rhs _ | .BNE lhs rhs _ | .BLT lhs rhs _ | .BGE lhs rhs _
  | .BLTU lhs rhs _ | .BGEU lhs rhs _ | .ANDN _ lhs rhs | .OR _ lhs rhs
  | .XOR _ lhs rhs | .AND _ lhs rhs | .SLT _ lhs rhs | .SLTU _ lhs rhs
  | .VirtualSRL _ lhs rhs | .VirtualSRA _ lhs rhs | .VirtualSRLW _ lhs rhs
  | .VirtualSRAW _ lhs rhs | .VirtualPext _ lhs rhs | .VirtualPextSigned _ lhs rhs
  | .VirtualShiftDataB _ lhs rhs | .VirtualShiftDataH _ lhs rhs | .VirtualShiftDataW _ lhs rhs
  | .VirtualXORROT32 _ lhs rhs | .VirtualXORROT24 _ lhs rhs | .VirtualXORROT16 _ lhs rhs
  | .VirtualXORROT63 _ lhs rhs
  | .VirtualXORROTL1 _ lhs rhs | .VirtualXORROTW16 _ lhs rhs | .VirtualXORROTW12 _ lhs rhs
  | .VirtualXORROTW8 _ lhs rhs | .VirtualXORROTW7 _ lhs rhs | .VirtualXORROTW22 _ lhs rhs
  | .VirtualXORROTW19 _ lhs rhs | .VirtualXORROTW6 _ lhs rhs | .VirtualAssertEQ lhs rhs _
  | .VirtualAssertValidDiv0 lhs rhs _ | .VirtualNegateIf _ lhs rhs
  | .VirtualAssertValidUnsignedRemainder lhs rhs _ | .VirtualAssertLTE lhs rhs _ =>
      interleaveLookupOperands (source lhs) (source rhs)
  | .VirtualSRLI _ src mask | .VirtualSRAI _ src mask
  | .VirtualSRLIW _ src mask | .VirtualSRAIW _ src mask
  | .VirtualROTRI _ src mask | .VirtualROTRIW _ src mask =>
      interleaveLookupOperands (source src) (BitVec.ofNat 64 mask)
  | .VirtualPow2 _ src _ | .VirtualPow2W _ src _ | .VirtualShiftRightBitmask _ src _
  | .VirtualShiftRightBitmaskW _ src _ | .VirtualRev8W _ src _
  | .VirtualSignExtendWord _ src _ | .VirtualZeroExtendWord _ src _ =>
      (source src).setWidth 128
  | .VirtualPow2I _ imm | .VirtualPow2IW _ imm | .VirtualShiftRightBitmaskI _ imm =>
      (BitVec.ofNat 64 imm).setWidth 128
  | .VirtualMovsign _ src imm => interleaveLookupOperands (source src) imm
  | .VirtualAdvice dst _ _ | .VirtualAdviceLoad dst _ | .VirtualAdviceLen dst _ _ =>
      let src : JoltISA.Src := match dst with
        | .xreg r => .xreg r
        | .vreg r => .vreg r
      (JoltISA.sourceValue src postState).setWidth 128
  | .FENCE | .LD _ _ _ _ | .SD _ _ _ | .VirtualHostIO _ _ _ => 0

-- Rust: [LookupIndex](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/lookups.rs:45).
-- Both committed and virtual instruction address chunks use this same index.
-- Padding is the no-op lookup at address 0.
noncomputable def lookupIndex {program : JoltProgram}
    (trace : JoltTrace program) (t : Nat) : BitVec 128 :=
  if inBounds : t < trace.rows.size then
    let row := getElem trace.rows t inBounds
    let bytecodeRow := getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt
    instructionLookupIndex bytecodeRow.instruction bytecodeRow.address row.preState row.postState
  else 0

end HonestWitness
