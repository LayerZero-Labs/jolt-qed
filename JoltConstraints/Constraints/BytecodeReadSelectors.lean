import JoltConstraints.Constraints.BytecodeReadData
import JoltConstraints.witness_helpers.register_address

set_option autoImplicit false

namespace JoltConstraints

/-- Fixed normalized register operand, with no operand represented by none.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L598-L630 -/
def bytecodeRs1Register (instruction : JoltISA.Instr) : Option (Fin 128) :=
  match instruction with
  | .ADDI _ src _ | .ADDIW _ src _ | .ANDI _ src _ | .ORI _ src _ | .XORI _ src _
  | .SLTI _ src _ | .SLTIU _ src _ | .JALR _ src _ | .BEQ src _ _ | .BNE src _ _
  | .BLT src _ _ | .BGE src _ _ | .BLTU src _ _ | .BGEU src _ _ | .ADD _ src _
  | .ADDW _ src _ | .SUB _ src _ | .SUBW _ src _ | .MUL _ src _ | .MULW _ src _
  | .MULHU _ src _ | .ANDN _ src _ | .VirtualMULI _ src _ | .VirtualMULIW _ src _
  | .VirtualPow2 _ src _ | .VirtualPow2W _ src _ | .VirtualShiftRightBitmask _ src _
  | .VirtualShiftRightBitmaskW _ src _ | .VirtualSRLI _ src _ | .VirtualSRAI _ src _
  | .VirtualSRLIW _ src _ | .VirtualSRAIW _ src _ | .VirtualSRL _ src _ | .VirtualSRA _ src _
  | .VirtualSRLW _ src _ | .VirtualSRAW _ src _ | .VirtualROTRI _ src _
  | .VirtualROTRIW _ src _ | .VirtualRev8W _ src _ | .VirtualXORROT32 _ src _
  | .VirtualXORROT24 _ src _ | .VirtualXORROT16 _ src _ | .VirtualXORROT63 _ src _
  | .VirtualXORROTL1 _ src _
  | .VirtualXORROTW16 _ src _ | .VirtualXORROTW12 _ src _ | .VirtualXORROTW8 _ src _
  | .VirtualXORROTW7 _ src _ | .VirtualXORROTW22 _ src _ | .VirtualXORROTW19 _ src _
  | .VirtualXORROTW6 _ src _ | .OR _ src _ | .XOR _ src _ | .AND _ src _ | .SLT _ src _
  | .SLTU _ src _ | .VirtualAlignAddr _ src _ | .VirtualWindowMaskB _ src _
  | .VirtualWindowMaskH _ src _ | .VirtualWindowMaskW _ src _ | .VirtualPext _ src _
  | .VirtualPextSigned _ src _ | .VirtualShiftDataB _ src _ | .VirtualShiftDataH _ src _
  | .VirtualShiftDataW _ src _ | .VirtualSignExtendWord _ src _ | .VirtualZeroExtendWord _ src _
  | .VirtualMovsign _ src _ | .LD _ _ src _ | .SD src _ _ | .VirtualAssertEQ src _ _
  | .VirtualAssertValidDiv0 src _ _ | .VirtualNegateIf _ src _
  | .VirtualAssertValidUnsignedRemainder src _ _ | .VirtualAssertMulUNoOverflow src _ _
  | .VirtualAssertLTE src _ _ | .VirtualAdviceLen _ src _ | .VirtualHostIO _ src _ =>
      some (HonestWitness.sourceRegisterAddress src)
  -- Alignment assertions can read architectural or virtual registers.
  | .VirtualAssertHalfwordAlignment base _ _ | .VirtualAssertWordAlignment base _ _ =>
      some (HonestWitness.sourceRegisterAddress base)
  | .LUI _ _ | .AUIPC _ _ | .JAL _ _ | .FENCE | .VirtualPow2I _ _ | .VirtualPow2IW _ _
  | .VirtualShiftRightBitmaskI _ _ | .VirtualAdvice _ _ _ | .VirtualAdviceLoad _ _ => none

/-- Fixed normalized register operand, with no operand represented by none.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L598-L630 -/
def bytecodeRs2Register (instruction : JoltISA.Instr) : Option (Fin 128) :=
  match instruction with
  | .BEQ _ src _ | .BNE _ src _ | .BLT _ src _ | .BGE _ src _ | .BLTU _ src _ | .BGEU _ src _
  | .ADD _ _ src | .ADDW _ _ src | .SUB _ _ src | .SUBW _ _ src | .MUL _ _ src
  | .MULW _ _ src | .MULHU _ _ src | .ANDN _ _ src | .VirtualSRL _ _ src
  | .VirtualSRA _ _ src | .VirtualSRLW _ _ src | .VirtualSRAW _ _ src
  | .VirtualXORROT32 _ _ src | .VirtualXORROT24 _ _ src | .VirtualXORROT16 _ _ src
  | .VirtualXORROT63 _ _ src
  | .VirtualXORROTL1 _ _ src | .VirtualXORROTW16 _ _ src | .VirtualXORROTW12 _ _ src
  | .VirtualXORROTW8 _ _ src | .VirtualXORROTW7 _ _ src | .VirtualXORROTW22 _ _ src
  | .VirtualXORROTW19 _ _ src | .VirtualXORROTW6 _ _ src | .OR _ _ src | .XOR _ _ src
  | .AND _ _ src | .SLT _ _ src | .SLTU _ _ src | .VirtualPext _ _ src
  | .VirtualPextSigned _ _ src | .VirtualShiftDataB _ _ src | .VirtualShiftDataH _ _ src
  | .VirtualShiftDataW _ _ src | .SD _ src _ | .VirtualAssertEQ _ src _
  | .VirtualAssertValidDiv0 _ src _ | .VirtualNegateIf _ _ src
  | .VirtualAssertValidUnsignedRemainder _ src _ | .VirtualAssertMulUNoOverflow _ src _
  | .VirtualAssertLTE _ src _ =>
      some (HonestWitness.sourceRegisterAddress src)
  | .ADDI _ _ _ | .ADDIW _ _ _ | .ANDI _ _ _ | .ORI _ _ _ | .XORI _ _ _ | .SLTI _ _ _
  | .SLTIU _ _ _ | .LUI _ _ | .AUIPC _ _ | .JAL _ _ | .JALR _ _ _ | .FENCE
  | .VirtualMULI _ _ _ | .VirtualMULIW _ _ _ | .VirtualPow2 _ _ _ | .VirtualPow2W _ _ _
  | .VirtualPow2I _ _ | .VirtualPow2IW _ _ | .VirtualShiftRightBitmask _ _ _
  | .VirtualShiftRightBitmaskI _ _ | .VirtualShiftRightBitmaskW _ _ _ | .VirtualSRLI _ _ _
  | .VirtualSRAI _ _ _ | .VirtualSRLIW _ _ _ | .VirtualSRAIW _ _ _ | .VirtualROTRI _ _ _
  | .VirtualROTRIW _ _ _ | .VirtualRev8W _ _ _ | .VirtualAlignAddr _ _ _
  | .VirtualWindowMaskB _ _ _ | .VirtualWindowMaskH _ _ _ | .VirtualWindowMaskW _ _ _
  | .VirtualSignExtendWord _ _ _ | .VirtualZeroExtendWord _ _ _ | .VirtualMovsign _ _ _
  | .VirtualAssertHalfwordAlignment _ _ _ | .VirtualAssertWordAlignment _ _ _ | .LD _ _ _ _
  | .VirtualAdvice _ _ _ | .VirtualAdviceLoad _ _ | .VirtualAdviceLen _ _ _
  | .VirtualHostIO _ _ _ => none

/-- Fixed normalized register operand, with no operand represented by none.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L598-L630 -/
def bytecodeRdRegister (instruction : JoltISA.Instr) : Option (Fin 128) :=
  match instruction with
  | .ADDI dst _ _ | .ADDIW dst _ _ | .ANDI dst _ _ | .ORI dst _ _ | .XORI dst _ _
  | .SLTI dst _ _ | .SLTIU dst _ _ | .LUI dst _ | .AUIPC dst _ | .JAL dst _ | .JALR dst _ _
  | .ADD dst _ _ | .ADDW dst _ _ | .SUB dst _ _ | .SUBW dst _ _ | .MUL dst _ _
  | .MULW dst _ _ | .MULHU dst _ _ | .ANDN dst _ _ | .VirtualMULI dst _ _
  | .VirtualMULIW dst _ _ | .VirtualPow2 dst _ _ | .VirtualPow2W dst _ _ | .VirtualPow2I dst _
  | .VirtualPow2IW dst _ | .VirtualShiftRightBitmask dst _ _ | .VirtualShiftRightBitmaskI dst _
  | .VirtualShiftRightBitmaskW dst _ _ | .VirtualSRLI dst _ _ | .VirtualSRAI dst _ _
  | .VirtualSRLIW dst _ _ | .VirtualSRAIW dst _ _ | .VirtualSRL dst _ _ | .VirtualSRA dst _ _
  | .VirtualSRLW dst _ _ | .VirtualSRAW dst _ _ | .VirtualROTRI dst _ _
  | .VirtualROTRIW dst _ _ | .VirtualRev8W dst _ _ | .VirtualXORROT32 dst _ _
  | .VirtualXORROT24 dst _ _ | .VirtualXORROT16 dst _ _ | .VirtualXORROT63 dst _ _
  | .VirtualXORROTL1 dst _ _
  | .VirtualXORROTW16 dst _ _ | .VirtualXORROTW12 dst _ _ | .VirtualXORROTW8 dst _ _
  | .VirtualXORROTW7 dst _ _ | .VirtualXORROTW22 dst _ _ | .VirtualXORROTW19 dst _ _
  | .VirtualXORROTW6 dst _ _ | .OR dst _ _ | .XOR dst _ _ | .AND dst _ _ | .SLT dst _ _
  | .SLTU dst _ _ | .VirtualAlignAddr dst _ _ | .VirtualWindowMaskB dst _ _
  | .VirtualWindowMaskH dst _ _ | .VirtualWindowMaskW dst _ _ | .VirtualPext dst _ _
  | .VirtualPextSigned dst _ _ | .VirtualShiftDataB dst _ _ | .VirtualShiftDataH dst _ _
  | .VirtualShiftDataW dst _ _ | .VirtualSignExtendWord dst _ _ | .VirtualZeroExtendWord dst _ _
  | .VirtualMovsign dst _ _ | .VirtualAdvice dst _ _ | .VirtualAdviceLoad dst _
  | .VirtualAdviceLen dst _ _ | .VirtualHostIO dst _ _ | .VirtualNegateIf dst _ _ =>
      some (HonestWitness.destinationRegisterAddress dst)
  -- The fixed table reads the already-normalized destination in the row.
  -- Rust rewrites side-effecting x0 destinations during bytecode expansion.
  | .LD _ dst _ _ =>
      some (HonestWitness.destinationRegisterAddress dst)
  | .BEQ _ _ _ | .BNE _ _ _ | .BLT _ _ _ | .BGE _ _ _ | .BLTU _ _ _ | .BGEU _ _ _ | .FENCE
  | .VirtualAssertHalfwordAlignment _ _ _ | .VirtualAssertWordAlignment _ _ _ | .SD _ _ _
  | .VirtualAssertEQ _ _ _ | .VirtualAssertValidDiv0 _ _ _
  | .VirtualAssertValidUnsignedRemainder _ _ _ | .VirtualAssertMulUNoOverflow _ _ _
  | .VirtualAssertLTE _ _ _ => none

/-- A fixed bytecode register-selector entry. Explicit register zero is distinct
from an absent operand; leading and trailing padding have no operands. -/
def bytecodeRegisterSelector {F : Type} [Field F] (program : JoltProgram)
    (operand : JoltISA.Instr → Option (Fin 128)) (register : Fin 128) (address : Nat) : F :=
  match bytecodeRow program address with
  | some row => if operand row.instruction = some register then 1 else 0
  | none => 0

/-- Fixed lookup-table flags; a padding no-op selects no lookup table.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L607-L609 -/
def bytecodeLookupTableFlag {F : Type} [Field F] (program : JoltProgram)
    (table : LookupTableKind) (address : Nat) : F :=
  match bytecodeRow program address with
  | some row => if JoltMetadata.lookupTableFlag row.instruction table then 1 else 0
  | none => 0

/-- Fixed RAF flag: one for combined lookup operands; padding contributes zero.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs#L603-L609 -/
def bytecodeRafFlag {F : Type} [Field F] (program : JoltProgram) (address : Nat) : F :=
  match bytecodeRow program address with
  | some row => if JoltMetadata.instructionRafFlag row.instruction then 1 else 0
  | none => 0

end JoltConstraints
