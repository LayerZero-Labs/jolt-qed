import Mathlib.Algebra.Field.Defs
import JoltBytecode.JoltISA.RegisterAccess

set_option autoImplicit false

namespace HonestWitness

-- Rust: [FormatR register capture](/Users/ari.biswas/Work-with-A16z/jolt/tracer/src/instruction/format/format_r.rs:77).
-- Extract the captured destination register from the supplied state and encode its
-- unsigned 64-bit contents in F. Supplying the pre-state gives the old value;
-- supplying the post-state gives the new value. Instructions without rd give zero.
-- HOST_IO still has a captured rd even though it does not write it.
noncomputable def rdValue {F : Type} [Field F]
    (instruction : JoltISA.Instr) (state : SailJoltState) : F :=
  -- Src and Dst name the same register banks; reuse the pure ISA accessor.
  let destinationValue (dst : JoltISA.Dst) : F :=
    let register : JoltISA.Src :=
      match dst with
      | .xreg r => .xreg r
      | .vreg r => .vreg r
    ((JoltISA.sourceValue register state).toNat : F)
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
      destinationValue dst
  -- Rust captures the destination in the final row without rewriting it.
  | .LD _ dst _ _ => destinationValue dst
  | .BEQ _ _ _ | .BNE _ _ _ | .BLT _ _ _ | .BGE _ _ _ | .BLTU _ _ _ | .BGEU _ _ _ | .FENCE
  | .VirtualAssertHalfwordAlignment _ _ _ | .VirtualAssertWordAlignment _ _ _ | .SD _ _ _
  | .VirtualAssertEQ _ _ _ | .VirtualAssertValidDiv0 _ _ _
  | .VirtualAssertValidUnsignedRemainder _ _ _ | .VirtualAssertMulUNoOverflow _ _ _
  | .VirtualAssertLTE _ _ _ => 0

end HonestWitness
