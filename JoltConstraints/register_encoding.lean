import JoltBytecode.JoltISA.Instruction

set_option autoImplicit false

namespace JoltRegisterEncoding

/-- Decode a Rust register address using the existing ISA register map.
Rust has one address space: x0..x31 followed by virtual registers 32..127.
Rust: https://github.com/abiswas3/jolt/tree/main/common/src/constants.rs -/
def source (address : JoltISA.VReg) : JoltISA.Src :=
  match JoltISA.joltRegisterSlot address with
  | .xreg index => .xreg index
  | _ => .vreg address

/-- Decode a destination address with the same map as source addresses. -/
def destination (address : JoltISA.VReg) : JoltISA.Dst :=
  match JoltISA.joltRegisterSlot address with
  | .xreg index => .xreg index
  | _ => .vreg address

/-- A source uses the storage selected by the ISA's register-address map.
The raw `.vreg` constructor must not bypass an architectural-register slot. -/
def sourceIsCanonical : JoltISA.Src → Bool
  | .xreg _ => true
  | .vreg address =>
      match JoltISA.joltRegisterSlot address with
      | .xreg _ => false
      | _ => true

/-- Destination storage must agree with the same register-address map.
This checks the register representation, not Rust's separate rd=x0 expansion. -/
def destinationIsCanonical : JoltISA.Dst → Bool
  | .xreg _ => true
  | .vreg address =>
      match JoltISA.joltRegisterSlot address with
      | .xreg _ => false
      | _ => true

/-- Every register operand in a fixed bytecode row uses its canonical ISA
representation. Check captured operands too, even if execution ignores them.
This inspects syntax only; instruction execution remains in `JoltISA.execInstr`.
Rust: https://github.com/abiswas3/jolt/tree/main/tracer/src/instruction/format -/
def instructionIsCanonical (instruction : JoltISA.Instr) : Bool :=
  match instruction with
  -- One source and one destination.
  | .ADDI dst src _ | .ADDIW dst src _ | .ANDI dst src _ | .ORI dst src _
  | .XORI dst src _ | .SLTI dst src _ | .SLTIU dst src _ | .JALR dst src _
  | .VirtualMULI dst src _ | .VirtualMULIW dst src _
  | .VirtualPow2 dst src _ | .VirtualPow2W dst src _
  | .VirtualShiftRightBitmask dst src _ | .VirtualShiftRightBitmaskW dst src _
  | .VirtualSRLI dst src _ | .VirtualSRAI dst src _
  | .VirtualSRLIW dst src _ | .VirtualSRAIW dst src _
  | .VirtualROTRI dst src _ | .VirtualROTRIW dst src _ | .VirtualRev8W dst src _
  | .VirtualAlignAddr dst src _ | .VirtualWindowMaskB dst src _
  | .VirtualWindowMaskH dst src _ | .VirtualWindowMaskW dst src _
  | .VirtualSignExtendWord dst src _ | .VirtualZeroExtendWord dst src _
  | .VirtualMovsign dst src _ | .LD _ dst src _
  | .VirtualAdviceLen dst src _ | .VirtualHostIO dst src _ =>
      destinationIsCanonical dst && sourceIsCanonical src
  -- Two sources and one destination.
  | .ADD dst lhs rhs | .ADDW dst lhs rhs | .SUB dst lhs rhs | .SUBW dst lhs rhs
  | .MUL dst lhs rhs | .MULW dst lhs rhs | .MULHU dst lhs rhs | .ANDN dst lhs rhs
  | .OR dst lhs rhs | .XOR dst lhs rhs | .AND dst lhs rhs
  | .SLT dst lhs rhs | .SLTU dst lhs rhs
  | .VirtualSRL dst lhs rhs | .VirtualSRA dst lhs rhs
  | .VirtualSRLW dst lhs rhs | .VirtualSRAW dst lhs rhs
  | .VirtualXORROT32 dst lhs rhs | .VirtualXORROT24 dst lhs rhs
  | .VirtualXORROT16 dst lhs rhs | .VirtualXORROT63 dst lhs rhs
  | .VirtualXORROTL1 dst lhs rhs | .VirtualXORROTW16 dst lhs rhs
  | .VirtualXORROTW12 dst lhs rhs | .VirtualXORROTW8 dst lhs rhs
  | .VirtualXORROTW7 dst lhs rhs | .VirtualXORROTW22 dst lhs rhs
  | .VirtualXORROTW19 dst lhs rhs | .VirtualXORROTW6 dst lhs rhs
  | .VirtualPext dst lhs rhs | .VirtualPextSigned dst lhs rhs
  | .VirtualShiftDataB dst lhs rhs | .VirtualShiftDataH dst lhs rhs
  | .VirtualShiftDataW dst lhs rhs | .VirtualNegateIf dst lhs rhs =>
      destinationIsCanonical dst && sourceIsCanonical lhs && sourceIsCanonical rhs
  -- Two sources and no destination.
  | .BEQ lhs rhs _ | .BNE lhs rhs _ | .BLT lhs rhs _ | .BGE lhs rhs _
  | .BLTU lhs rhs _ | .BGEU lhs rhs _ | .SD lhs rhs _
  | .VirtualAssertEQ lhs rhs _ | .VirtualAssertValidDiv0 lhs rhs _
  | .VirtualAssertValidUnsignedRemainder lhs rhs _
  | .VirtualAssertMulUNoOverflow lhs rhs _ | .VirtualAssertLTE lhs rhs _ =>
      sourceIsCanonical lhs && sourceIsCanonical rhs
  -- Destination only; runtime advice is a value, not a register operand.
  | .LUI dst _ | .AUIPC dst _ | .JAL dst _
  | .VirtualPow2I dst _ | .VirtualPow2IW dst _ | .VirtualShiftRightBitmaskI dst _
  | .VirtualAdvice dst _ _ | .VirtualAdviceLoad dst _ =>
      destinationIsCanonical dst
  | .VirtualAssertHalfwordAlignment base _ _ | .VirtualAssertWordAlignment base _ _ =>
      sourceIsCanonical base
  | .FENCE => true

end JoltRegisterEncoding
