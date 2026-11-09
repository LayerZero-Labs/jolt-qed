import JoltConstraints.witness
import JoltConstraints.trace

open LeanRV64D

set_option autoImplicit false

namespace JoltMetadata

/-- The normalized immediate, retaining signed offsets for memory rows,
branches and ShiftData and unsigned 64-bit encodings for I/U/J rows.
For example, a floor load or ShiftData with offset -2 contributes -2.
Jolt's tracer: `tracer/src/instruction/format/format_{load,s,shift_data}.rs`
(`NormalizedOperands::from`); Jolt's expander:
`crates/jolt-program/src/expand/memory/shared.rs` (`LaneWindow::open`, `merge`)
at `c6703570`. -/
def immediate (instruction : JoltISA.Instr) : Int :=
  match instruction with
  | .ADDI _ _ imm | .ADDIW _ _ imm | .ANDI _ _ imm | .ORI _ _ imm | .XORI _ _ imm
  | .SLTI _ _ imm | .SLTIU _ _ imm | .JALR _ _ imm
  | .VirtualWindowMaskB _ _ imm | .VirtualWindowMaskH _ _ imm | .VirtualWindowMaskW _ _ imm =>
      imm.toNat
  | .JAL _ imm => imm.toNat
  | .AUIPC _ imm => imm.toNat
  | .LUI _ imm | .VirtualMULI _ _ imm | .VirtualMULIW _ _ imm
  | .VirtualPow2 _ _ imm | .VirtualPow2W _ _ imm | .VirtualShiftRightBitmask _ _ imm
  | .VirtualShiftRightBitmaskW _ _ imm | .VirtualRev8W _ _ imm
  | .VirtualSignExtendWord _ _ imm | .VirtualZeroExtendWord _ _ imm
  | .VirtualMovsign _ _ imm | .VirtualAdvice _ _ imm | .VirtualAdviceLoad _ imm => imm.toNat
  | .VirtualPow2I _ imm | .VirtualPow2IW _ imm | .VirtualShiftRightBitmaskI _ imm
  | .VirtualSRLI _ _ imm | .VirtualSRAI _ _ imm | .VirtualSRLIW _ _ imm
  | .VirtualSRAIW _ _ imm | .VirtualROTRI _ _ imm | .VirtualROTRIW _ _ imm =>
      (BitVec.ofNat 64 imm).toNat
  | .LD _ _ _ imm | .SD _ _ imm
  | .VirtualLoadB _ _ _ imm _ | .VirtualLoadH _ _ _ imm _ | .VirtualLoadW _ _ _ imm _
  | .VirtualStoreB _ _ imm _ | .VirtualStoreH _ _ imm _ | .VirtualStoreW _ _ imm _
  | .VirtualShiftDataB _ _ _ imm | .VirtualShiftDataH _ _ _ imm
  | .VirtualShiftDataW _ _ _ imm => imm.toInt
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
  | .VirtualNegateIf .. | .VirtualHostIO => 0

/-- Whether a row selects an instruction-input source or a branch/no-op flag.
For example, LD selects its captured destination and ShiftData selects both
its second source and its immediate.
Jolt's prover: `crates/jolt-riscv/src/instructions/i/ld.rs` and
`instructions/virt/{load,store,shift_data}_{b,h,w}.rs` (`jolt_instruction!`)
at `c6703570`. -/
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
      | .VirtualROTRI .. | .VirtualROTRIW .. | .VirtualWindowMaskB ..
      | .VirtualWindowMaskH .. | .VirtualWindowMaskW .. | .VirtualMovsign ..
      | .VirtualLoadB .. | .VirtualLoadH .. | .VirtualLoadW ..
      | .VirtualStoreB .. | .VirtualStoreH .. | .VirtualStoreW ..
      | .VirtualShiftDataB .. | .VirtualShiftDataH .. | .VirtualShiftDataW .. => true
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
      | .AND .. | .SLT .. | .SLTU .. | .VirtualWindowMaskB ..
      | .VirtualWindowMaskH .. | .VirtualWindowMaskW .. | .VirtualPext ..
      | .VirtualPextSigned .. | .VirtualShiftDataB .. | .VirtualShiftDataH ..
      | .VirtualShiftDataW .. | .VirtualSignExtendWord .. | .VirtualZeroExtendWord ..
      | .VirtualMovsign ..
      | .VirtualAssertEQ .. | .VirtualAssertValidDiv0 ..
      | .VirtualNegateIf .. | .VirtualAssertValidUnsignedRemainder ..
      | .VirtualAssertMulUNoOverflow .. | .VirtualAssertLTE ..
      | .VirtualLoadB .. | .VirtualLoadH .. | .VirtualLoadW ..
      | .VirtualStoreB .. | .VirtualStoreH .. | .VirtualStoreW .. => true
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
  -- Jolt's pseudo Noop has IsNoop, but is not a modeled Instr constructor.
  -- At 8bbb2357, jolt-program/src/image/decode.rs never returns NoOp; its
  -- NoOp match arm only defines operands for that already-supplied kind.
  -- expand/operands.rs::noop_for emits ADDI x0, x0, 0, whose IsNoop is false.
  -- Padding flags are supplied separately by bytecodeInstructionFlag.
  | .IsNoop => false
  | .RightOperandIsRdWriteValue =>
      match instruction with
      | .LD .. => true
      | _ => false

/-- The circuit flags fixed by an instruction, before sequence stamping.
For example, a floor load sets `Load` and `AddOperands`; LD sets only `Load`.
Jolt's prover: `crates/jolt-riscv/src/instructions/i/ld.rs` and
`instructions/virt/{load,store,shift_data}_{b,h,w}.rs` (`jolt_instruction!`)
at `c6703570`. -/
def opcodeFlag (instruction : JoltISA.Instr) (flag : CircuitFlags) : Bool :=
  match flag with
  -- TODO: Why is this virtual shit flipping off Add operands? Double check with rust code
  | .AddOperands =>
      match instruction with
      | .ADDI .. | .ADDIW .. | .LUI .. | .AUIPC .. | .JAL .. | .JALR .. | .ADD .. | .ADDW ..
      | .VirtualPow2 .. | .VirtualPow2W .. | .VirtualPow2I .. | .VirtualPow2IW ..
      | .VirtualShiftRightBitmask .. | .VirtualShiftRightBitmaskI ..
      | .VirtualShiftRightBitmaskW .. | .VirtualRev8W ..
      | .VirtualWindowMaskB .. | .VirtualWindowMaskH .. | .VirtualWindowMaskW ..
      | .VirtualSignExtendWord .. | .VirtualZeroExtendWord ..
      | .VirtualLoadB .. | .VirtualLoadH .. | .VirtualLoadW ..
      | .VirtualStoreB .. | .VirtualStoreH .. | .VirtualStoreW .. => true
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
      | .LD .. | .VirtualLoadB .. | .VirtualLoadH .. | .VirtualLoadW .. => true
      | _ => false
  | .Store =>
      match instruction with
      | .SD .. | .VirtualStoreB .. | .VirtualStoreH .. | .VirtualStoreW .. => true
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
      | .SLTU .. | .VirtualWindowMaskB .. | .VirtualWindowMaskH ..
      | .VirtualWindowMaskW .. | .VirtualPext .. | .VirtualPextSigned ..
      | .VirtualShiftDataB .. | .VirtualShiftDataH .. | .VirtualShiftDataW ..
      | .VirtualSignExtendWord .. | .VirtualZeroExtendWord .. | .VirtualMovsign ..
      | .VirtualAdvice .. | .VirtualAdviceLoad ..
      | .VirtualNegateIf .. => true
      | _ => false
  -- TODO: There is no Virtual Instruction?
  | .VirtualInstruction => false
  -- Instructions that panic the verifier.
  | .Assert =>
      match instruction with
      | .VirtualAssertEQ .. | .VirtualAssertValidDiv0 ..
      | .VirtualAssertValidUnsignedRemainder .. | .VirtualAssertMulUNoOverflow ..
      | .VirtualAssertLTE .. => true
      | _ => false
  -- TODO: Check this
  | .DoNotUpdateUnexpandedPC => false
  | .Advice =>
      match instruction with
      | .VirtualAdvice .. | .VirtualAdviceLoad .. => true
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

-- A bytecode row's circuit flags: the row-dependent ones come from its sequence
-- stamp, the rest from its instruction (opcodeFlag).
-- Rust: jolt/crates/jolt-riscv/src/lib.rs:399-421 (circuit_flags), checked 2026-10-07
def circuitFlag (row : JoltInstructionRow) (flag : CircuitFlags) : Bool :=
  match flag with
  | .VirtualInstruction => row.virtual_sequence_remaining.isSome
  | .IsLastInSequence => row.virtual_sequence_remaining == some 0
  | .DoNotUpdateUnexpandedPC => row.virtual_sequence_remaining.getD 0 != 0
  | .IsCompressed => row.is_compressed
  | .IsFirstInSequence => row.is_first_in_sequence
  | _ => opcodeFlag row.instruction flag

/-- A load-flagged row is LD or a floor load of class B, H or W.
For example, a `VirtualLoadH` satisfies the second alternative with its fault code.
Jolt's prover: `crates/jolt-riscv/src/instructions/i/ld.rs` and
`instructions/virt/load_{b,h,w}.rs` (`jolt_instruction!`) at `c6703570`. -/
theorem opcodeFlag_load_cases (instruction : JoltISA.Instr)
    (h : opcodeFlag instruction .Load = true) :
    ∃ faultClass dst base imm,
      instruction = .LD faultClass dst base imm ∨
      ∃ fault, instruction = .VirtualLoadB faultClass dst base imm fault ∨
        instruction = .VirtualLoadH faultClass dst base imm fault ∨
        instruction = .VirtualLoadW faultClass dst base imm fault := by
  simp only [opcodeFlag] at h
  split at h <;> simp_all

/-- A store-flagged row is SD or a floor store of class B, H or W.
For example, a `VirtualStoreW` satisfies the last alternative with its fault code.
Jolt's prover: `crates/jolt-riscv/src/instructions/i/sd.rs` and
`instructions/virt/store_{b,h,w}.rs` (`jolt_instruction!`) at `c6703570`. -/
theorem opcodeFlag_store_cases (instruction : JoltISA.Instr)
    (h : opcodeFlag instruction .Store = true) :
    ∃ base value imm,
      instruction = .SD base value imm ∨
      ∃ fault, instruction = .VirtualStoreB base value imm fault ∨
        instruction = .VirtualStoreH base value imm fault ∨
        instruction = .VirtualStoreW base value imm fault := by
  simp only [opcodeFlag] at h
  split at h <;> simp_all

/-- The table selected by an instruction, or `none` when it has no table.
For example, a halfword floor load or store selects `AddressOffsetH`,
while LD and SD select no table.
Jolt's prover: `crates/jolt-lookup-tables/src/instructions/virt/floor_access.rs`
(`floor_access!`) and `instructions/riscv/{ld,sd}.rs` (`impl_lookup_table!`)
at `c6703570`. -/
def lookupTable (instruction : JoltISA.Instr) : Option LookupTableKind :=
  match instruction with
  | .ADDI .. | .LUI .. | .AUIPC .. | .JAL .. | .ADD .. | .SUB .. | .MUL ..
  | .VirtualMULI .. | .VirtualAdvice .. | .VirtualAdviceLoad .. => some .RangeCheck
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
  | .VirtualLoadB .. | .VirtualStoreB .. => some .AddressOffsetB
  | .VirtualLoadH .. | .VirtualStoreH .. => some .AddressOffsetH
  | .VirtualLoadW .. | .VirtualStoreW .. => some .AddressOffsetW
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
