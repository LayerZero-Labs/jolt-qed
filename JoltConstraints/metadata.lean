import JoltConstraints.witness
import JoltConstraints.trace

set_option autoImplicit false

namespace JoltMetadata

-- Rust: [format normalization](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction/format).
-- Rust: [decoded operands](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-program/src/image/decode.rs:399).
-- Preserve the normalized row immediate, including fields ignored by execution.
-- I/U/J and alignment formats widen a u64 to i128. Loads/stores and branches
-- retain a signed offset. AdviceLoad carries its byte count, not its loaded value.
def immediate (instruction : JoltISA.Instr) : Int :=
  match instruction with
  | .ADDI _ _ imm | .ADDIW _ _ imm | .ANDI _ _ imm | .ORI _ _ imm | .XORI _ _ imm
  | .SLTI _ _ imm | .SLTIU _ _ imm | .JALR _ _ imm | .VirtualAlignAddr _ _ imm
  | .VirtualWindowMaskB _ _ imm | .VirtualWindowMaskH _ _ imm | .VirtualWindowMaskW _ _ imm
  | .VirtualAssertHalfwordAlignment _ imm _ | .VirtualAssertWordAlignment _ imm _ =>
      imm.toNat
  | .JAL _ imm => imm.toNat
  | .AUIPC _ imm => imm.toNat
  | .LUI _ imm | .VirtualMULI _ _ imm | .VirtualMULIW _ _ imm
  | .VirtualPow2 _ _ imm | .VirtualPow2W _ _ imm | .VirtualShiftRightBitmask _ _ imm
  | .VirtualShiftRightBitmaskW _ _ imm | .VirtualRev8W _ _ imm
  | .VirtualSignExtendWord _ _ imm | .VirtualZeroExtendWord _ _ imm
  | .VirtualMovsign _ _ imm | .VirtualAdvice _ _ imm | .VirtualAdviceLoad _ imm
  | .VirtualAdviceLen _ _ imm | .VirtualHostIO _ _ imm => imm.toNat
  | .VirtualPow2I _ imm | .VirtualPow2IW _ imm | .VirtualShiftRightBitmaskI _ imm
  | .VirtualSRLI _ _ imm | .VirtualSRAI _ _ imm | .VirtualSRLIW _ _ imm
  | .VirtualSRAIW _ _ imm | .VirtualROTRI _ _ imm | .VirtualROTRIW _ _ imm =>
      (BitVec.ofNat 64 imm).toNat
  | .LD _ _ _ imm | .SD _ _ imm => imm.toInt
  | .BEQ _ _ imm | .BNE _ _ imm | .BLT _ _ imm | .BGE _ _ imm
  | .BLTU _ _ imm | .BGEU _ _ imm | .VirtualAssertEQ _ _ imm => imm.toInt
  | .VirtualAssertValidDiv0 _ _ imm | .VirtualAssertValidUnsignedRemainder _ _ imm
  | .VirtualAssertMulUNoOverflow _ _ imm | .VirtualAssertLTE _ _ imm => imm.toInt
  | .FENCE | .ADD .. | .ADDW .. | .SUB .. | .SUBW .. | .MUL .. | .MULW ..
  | .MULHU .. | .ANDN .. | .VirtualSRL .. | .VirtualSRA .. | .VirtualSRLW .. | .VirtualSRAW ..
  | .VirtualXORROT32 .. | .VirtualXORROT24 .. | .VirtualXORROT16 .. | .VirtualXORROT63 ..
  | .VirtualXORROTL1 ..
  | .VirtualXORROTW16 .. | .VirtualXORROTW12 .. | .VirtualXORROTW8 .. | .VirtualXORROTW7 ..
  | .VirtualXORROTW22 .. | .VirtualXORROTW19 .. | .VirtualXORROTW6 ..
  | .OR .. | .XOR .. | .AND .. | .SLT .. | .SLTU .. | .VirtualPext .. | .VirtualPextSigned ..
  | .VirtualShiftDataB .. | .VirtualShiftDataH .. | .VirtualShiftDataW ..
  | .VirtualNegateIf .. => 0

-- Rust: crates/jolt-riscv/src/instructions/{i,m,virt,assert}/*.rs (instruction flags).
-- Rust: crates/jolt-riscv/src/lib.rs::jolt_instruction.
-- We want to know if the Jolt Instruction flips a particular flag on.
def instructionFlag (instruction : JoltISA.Instr) (flag : InstructionFlags) : Bool :=
  match flag with
  -- All the instructions for which the left operand (first source) is the program counter
  | .LeftOperandIsPC =>
      match instruction with
      | .AUIPC .. | .JAL .. => true
      | _ => false
  -- The right operand (second source) is an immediate value (large class of instructions)
  | .RightOperandIsImm =>
      match instruction with
      | .ADDI .. | .ADDIW .. | .ANDI .. | .ORI .. | .XORI .. | .SLTI .. | .SLTIU ..
      | .LUI .. | .AUIPC .. | .JAL .. | .JALR .. | .VirtualMULI .. | .VirtualMULIW ..
      | .VirtualPow2I .. | .VirtualPow2IW .. | .VirtualShiftRightBitmaskI ..
      | .VirtualSRLI .. | .VirtualSRAI .. | .VirtualSRLIW .. | .VirtualSRAIW ..
      | .VirtualROTRI .. | .VirtualROTRIW .. | .VirtualAlignAddr .. | .VirtualWindowMaskB ..
      | .VirtualWindowMaskH .. | .VirtualWindowMaskW .. | .VirtualMovsign ..
      | .VirtualAssertHalfwordAlignment .. | .VirtualAssertWordAlignment .. => true
      | _ => false
  -- The left operand (first source) is a general purpose xreg
  | .LeftOperandIsRs1Value =>
      match instruction with
      | .ADDI .. | .ADDIW .. | .ANDI .. | .ORI .. | .XORI .. | .SLTI .. | .SLTIU ..
      | .JALR .. | .BEQ .. | .BNE .. | .BLT .. | .BGE .. | .BLTU .. | .BGEU .. | .ADD ..
      | .ADDW .. | .SUB .. | .SUBW .. | .MUL .. | .MULW .. | .MULHU .. | .ANDN ..
      | .VirtualMULI .. | .VirtualMULIW .. | .VirtualPow2 .. | .VirtualPow2W ..
      | .VirtualShiftRightBitmask .. | .VirtualShiftRightBitmaskW .. | .VirtualSRLI ..
      | .VirtualSRAI .. | .VirtualSRLIW .. | .VirtualSRAIW .. | .VirtualSRL ..
      | .VirtualSRA .. | .VirtualSRLW .. | .VirtualSRAW .. | .VirtualROTRI ..
      | .VirtualROTRIW .. | .VirtualRev8W .. | .VirtualXORROT32 .. | .VirtualXORROT24 ..
      | .VirtualXORROT16 .. | .VirtualXORROT63 .. | .VirtualXORROTL1 .. | .VirtualXORROTW16 ..
      | .VirtualXORROTW12 .. | .VirtualXORROTW8 .. | .VirtualXORROTW7 ..
      | .VirtualXORROTW22 .. | .VirtualXORROTW19 .. | .VirtualXORROTW6 .. | .OR .. | .XOR ..
      | .AND .. | .SLT .. | .SLTU .. | .VirtualAlignAddr .. | .VirtualWindowMaskB ..
      | .VirtualWindowMaskH .. | .VirtualWindowMaskW .. | .VirtualPext ..
      | .VirtualPextSigned .. | .VirtualShiftDataB .. | .VirtualShiftDataH ..
      | .VirtualShiftDataW .. | .VirtualSignExtendWord .. | .VirtualZeroExtendWord ..
      | .VirtualMovsign .. | .VirtualAssertHalfwordAlignment ..
      | .VirtualAssertWordAlignment .. | .VirtualAssertEQ .. | .VirtualAssertValidDiv0 ..
      | .VirtualNegateIf .. | .VirtualAssertValidUnsignedRemainder ..
      | .VirtualAssertMulUNoOverflow .. | .VirtualAssertLTE .. => true
      | _ => false
  --  The right operand (second source) is a general purpose xreg
  | .RightOperandIsRs2Value =>
      match instruction with
      | .BEQ .. | .BNE .. | .BLT .. | .BGE .. | .BLTU .. | .BGEU .. | .ADD .. | .ADDW ..
      | .SUB .. | .SUBW .. | .MUL .. | .MULW .. | .MULHU .. | .ANDN .. | .VirtualSRL ..
      | .VirtualSRA .. | .VirtualSRLW .. | .VirtualSRAW .. | .VirtualXORROT32 ..
      | .VirtualXORROT24 .. | .VirtualXORROT16 .. | .VirtualXORROT63 .. | .VirtualXORROTL1 ..
      | .VirtualXORROTW16 .. | .VirtualXORROTW12 .. | .VirtualXORROTW8 ..
      | .VirtualXORROTW7 .. | .VirtualXORROTW22 .. | .VirtualXORROTW19 ..
      | .VirtualXORROTW6 .. | .OR .. | .XOR .. | .AND .. | .SLT .. | .SLTU ..
      | .VirtualPext .. | .VirtualPextSigned .. | .VirtualShiftDataB ..
      | .VirtualShiftDataH .. | .VirtualShiftDataW .. | .VirtualAssertEQ ..
      | .VirtualAssertValidDiv0 .. | .VirtualNegateIf ..
      | .VirtualAssertValidUnsignedRemainder .. | .VirtualAssertMulUNoOverflow ..
      | .VirtualAssertLTE .. => true
      | _ => false
  -- All instructions the branch
  | .Branch =>
      match instruction with
      | .BEQ .. | .BNE .. | .BLT .. | .BGE .. | .BLTU .. | .BGEU .. => true
      | _ => false
  -- No instruction is a No op flag (TODO: double check this)
  | .IsNoop => false

-- Rust: crates/jolt-riscv/src/instructions/{i,m,virt,assert}/*.rs (circuit flags).
-- Rust: crates/jolt-riscv/src/lib.rs::jolt_instruction.
-- Same business as above, but instead with circuit flags
def opcodeFlag (instruction : JoltISA.Instr) (flag : CircuitFlags) : Bool :=
  match flag with
  -- TODO: Why is this virtual shit flipping off Add operands? Double check with rust code
  | .AddOperands =>
      match instruction with
      | .ADDI .. | .ADDIW .. | .LUI .. | .AUIPC .. | .JAL .. | .JALR .. | .ADD .. | .ADDW ..
      | .VirtualPow2 .. | .VirtualPow2W .. | .VirtualPow2I .. | .VirtualPow2IW ..
      | .VirtualShiftRightBitmask .. | .VirtualShiftRightBitmaskI ..
      | .VirtualShiftRightBitmaskW .. | .VirtualRev8W .. | .VirtualAlignAddr ..
      | .VirtualWindowMaskB .. | .VirtualWindowMaskH .. | .VirtualWindowMaskW ..
      | .VirtualSignExtendWord .. | .VirtualZeroExtendWord ..
      | .VirtualAssertHalfwordAlignment .. | .VirtualAssertWordAlignment .. => true
      | _ => false
  | .SubtractOperands =>
      match instruction with
      | .SUB .. | .SUBW .. => true
      | _ => false
  | .MultiplyOperands =>
      match instruction with
      | .MUL .. | .MULW .. | .MULHU .. | .VirtualMULI .. | .VirtualMULIW ..
      | .VirtualAssertMulUNoOverflow .. => true
      | _ => false
  | .Load =>
      match instruction with
      | .LD .. => true
      | _ => false
  | .Store =>
      match instruction with
      | .SD .. => true
      | _ => false
  | .Jump =>
      match instruction with
      | .JAL .. | .JALR .. => true
      | _ => false
  | .WriteLookupOutputToRD =>
      match instruction with
      | .ADDI .. | .ADDIW .. | .ANDI .. | .ORI .. | .XORI .. | .SLTI .. | .SLTIU ..
      | .LUI .. | .AUIPC .. | .ADD .. | .ADDW .. | .SUB .. | .SUBW .. | .MUL .. | .MULW ..
      | .MULHU .. | .ANDN .. | .VirtualMULI .. | .VirtualMULIW .. | .VirtualPow2 ..
      | .VirtualPow2W .. | .VirtualPow2I .. | .VirtualPow2IW ..
      | .VirtualShiftRightBitmask .. | .VirtualShiftRightBitmaskI ..
      | .VirtualShiftRightBitmaskW .. | .VirtualSRLI .. | .VirtualSRAI .. | .VirtualSRLIW ..
      | .VirtualSRAIW .. | .VirtualSRL .. | .VirtualSRA .. | .VirtualSRLW ..
      | .VirtualSRAW .. | .VirtualROTRI .. | .VirtualROTRIW .. | .VirtualRev8W ..
      | .VirtualXORROT32 .. | .VirtualXORROT24 .. | .VirtualXORROT16 ..
      | .VirtualXORROT63 .. | .VirtualXORROTL1 .. | .VirtualXORROTW16 .. | .VirtualXORROTW12 ..
      | .VirtualXORROTW8 .. | .VirtualXORROTW7 .. | .VirtualXORROTW22 ..
      | .VirtualXORROTW19 .. | .VirtualXORROTW6 .. | .OR .. | .XOR .. | .AND .. | .SLT ..
      | .SLTU .. | .VirtualAlignAddr .. | .VirtualWindowMaskB .. | .VirtualWindowMaskH ..
      | .VirtualWindowMaskW .. | .VirtualPext .. | .VirtualPextSigned ..
      | .VirtualShiftDataB .. | .VirtualShiftDataH .. | .VirtualShiftDataW ..
      | .VirtualSignExtendWord .. | .VirtualZeroExtendWord .. | .VirtualMovsign ..
      | .VirtualAdvice .. | .VirtualAdviceLoad .. | .VirtualAdviceLen ..
      | .VirtualNegateIf .. => true
      | _ => false
  -- TODO: There is no Virtual Instruction?
  | .VirtualInstruction => false
  -- Instructions that panic the verifier.
  | .Assert =>
      match instruction with
      | .VirtualAssertHalfwordAlignment .. | .VirtualAssertWordAlignment ..
      | .VirtualAssertEQ .. | .VirtualAssertValidDiv0 ..
      | .VirtualAssertValidUnsignedRemainder .. | .VirtualAssertMulUNoOverflow ..
      | .VirtualAssertLTE .. => true
      | _ => false
  -- TODO: Check this
  | .DoNotUpdateUnexpandedPC => false
  | .Advice =>
      match instruction with
      | .VirtualAdvice .. | .VirtualAdviceLoad .. | .VirtualAdviceLen .. => true
      | _ => false
  | .IsCompressed => false
  | .IsFirstInSequence => false
  | .IsLastInSequence => false

-- Rust: [LookupQuery operand packing](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-lookup-tables/src/traits.rs:93).
-- These flags select a single combined lookup operand: (0, lookup index).
-- All remaining instructions pass their two instruction inputs through.
def hasCombinedLookupOperands (instruction : JoltISA.Instr) : Bool :=
  opcodeFlag instruction .AddOperands || opcodeFlag instruction .SubtractOperands ||
    opcodeFlag instruction .MultiplyOperands || opcodeFlag instruction .Advice

-- Rust: crates/jolt-riscv/src/lib.rs::jolt_instruction (row-dependent circuit flags).
-- TODO: Bit confusing why we have done it twice
-- This maps JoltProgramRow instead of JoltInstruction like the rest of the project (not sure if needed yet)
def circuitFlag (row : JoltProgramRow) (flag : CircuitFlags) : Bool :=
  match flag with
  | .VirtualInstruction => row.virtualSequenceRemaining.isSome
  | .IsLastInSequence => row.virtualSequenceRemaining == some 0
  | .DoNotUpdateUnexpandedPC => row.virtualSequenceRemaining.getD 0 != 0
  | .IsCompressed => row.isCompressed
  | .IsFirstInSequence => row.isFirstInSequence
  | _ => opcodeFlag row.instruction flag

theorem opcodeFlag_load_requiresLD (instruction : JoltISA.Instr)
    (h : opcodeFlag instruction .Load = true) :
    ∃ faultClass dst base imm, instruction = .LD faultClass dst base imm := by
  cases instruction <;> simp_all [opcodeFlag]

theorem opcodeFlag_store_requiresSD (instruction : JoltISA.Instr)
    (h : opcodeFlag instruction .Store = true) :
    ∃ base value imm, instruction = .SD base value imm := by
  cases instruction <;> simp_all [opcodeFlag]

-- Rust: crates/jolt-lookup-tables/src/instructions/{riscv,virt}/::impl_lookup_table.
-- Map from instruction to Lookup tables (TODO: double check this connection)
def lookupTable (instruction : JoltISA.Instr) : Option LookupTableKind :=
  match instruction with
  | .ADDI .. | .LUI .. | .AUIPC .. | .JAL .. | .ADD .. | .SUB .. | .MUL ..
  | .VirtualMULI .. | .VirtualAdvice .. | .VirtualAdviceLoad ..
  | .VirtualAdviceLen .. => some .RangeCheck
  | .ADDIW .. | .ADDW .. | .SUBW .. | .MULW .. | .VirtualMULIW ..
  | .VirtualSignExtendWord .. => some .SignExtendWord
  | .ANDI .. | .AND .. => some .And
  | .ORI .. | .OR .. => some .Or
  | .XORI .. | .XOR .. => some .Xor
  | .SLTI .. | .BLT .. | .SLT .. => some .SignedLessThan
  | .SLTIU .. | .BLTU .. | .SLTU .. => some .UnsignedLessThan
  | .JALR .. => some .RangeCheckAligned
  | .BEQ .. | .VirtualAssertEQ .. => some .Equal
  | .BNE .. => some .NotEqual
  | .BGE .. => some .SignedGreaterThanEqual
  | .BGEU .. => some .UnsignedGreaterThanEqual
  | .FENCE .. | .LD .. | .SD .. | .VirtualHostIO .. => none
  | .MULHU .. => some .UpperWord
  | .ANDN .. => some .Andn
  | .VirtualPow2 .. | .VirtualPow2I .. => some .Pow2
  | .VirtualPow2W .. | .VirtualPow2IW .. => some .Pow2W
  | .VirtualShiftRightBitmask .. | .VirtualShiftRightBitmaskI .. => some .ShiftRightBitmask
  | .VirtualShiftRightBitmaskW .. => some .ShiftRightBitmaskW
  | .VirtualSRLI .. | .VirtualSRL .. => some .VirtualSRL
  | .VirtualSRAI .. | .VirtualSRA .. => some .VirtualSRA
  | .VirtualSRLIW .. | .VirtualSRLW .. => some .VirtualSRLW
  | .VirtualSRAIW .. | .VirtualSRAW .. => some .VirtualSRAW
  | .VirtualROTRI .. => some .VirtualROTR
  | .VirtualROTRIW .. => some .VirtualROTRW
  | .VirtualRev8W .. => some .VirtualRev8W
  | .VirtualXORROT32 .. => some .VirtualXORROT32
  | .VirtualXORROT24 .. => some .VirtualXORROT24
  | .VirtualXORROT16 .. => some .VirtualXORROT16
  | .VirtualXORROT63 .. => some .VirtualXORROT63
  | .VirtualXORROTL1 .. => some .VirtualXORROTL1
  | .VirtualXORROTW16 .. => some .VirtualXORROTW16
  | .VirtualXORROTW12 .. => some .VirtualXORROTW12
  | .VirtualXORROTW8 .. => some .VirtualXORROTW8
  | .VirtualXORROTW7 .. => some .VirtualXORROTW7
  | .VirtualXORROTW22 .. => some .VirtualXORROTW22
  | .VirtualXORROTW19 .. => some .VirtualXORROTW19
  | .VirtualXORROTW6 .. => some .VirtualXORROTW6
  | .VirtualAlignAddr .. => some .AlignAddr
  | .VirtualWindowMaskB .. => some .WindowMaskB
  | .VirtualWindowMaskH .. => some .WindowMaskH
  | .VirtualWindowMaskW .. => some .WindowMaskW
  | .VirtualPext .. => some .Pext
  | .VirtualPextSigned .. => some .PextSigned
  | .VirtualShiftDataB .. => some .ShiftDataB
  | .VirtualShiftDataH .. => some .ShiftDataH
  | .VirtualShiftDataW .. => some .ShiftDataW
  | .VirtualZeroExtendWord .. => some .LowerHalfWord
  | .VirtualMovsign .. => some .SignMask
  | .VirtualAssertHalfwordAlignment .. => some .HalfwordAlignment
  | .VirtualAssertWordAlignment .. => some .WordAlignment
  | .VirtualAssertValidDiv0 .. => some .ValidDiv0
  | .VirtualNegateIf .. => some .VirtualNegateIf
  | .VirtualAssertValidUnsignedRemainder .. => some .ValidUnsignedRemainder
  | .VirtualAssertMulUNoOverflow .. => some .MulUNoOverflow
  | .VirtualAssertLTE .. => some .UnsignedLessThanEqual

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::LookupTableFlag::extract_indexed.
def lookupTableFlag (instruction : JoltISA.Instr) (table : LookupTableKind) : Bool :=
  lookupTable instruction == some table

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::InstructionRafFlag::extract.
def instructionRafFlag (instruction : JoltISA.Instr) : Bool :=
  opcodeFlag instruction .AddOperands || opcodeFlag instruction .SubtractOperands ||
    opcodeFlag instruction .MultiplyOperands || opcodeFlag instruction .Advice

end JoltMetadata
