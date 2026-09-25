import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.witness_helpers.register_address

set_option autoImplicit false

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [materialize_register_read_write_virtual](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/registers.rs:47).
-- Select the instruction's first source register, including an explicit x0.
-- An absent operand and a padding position select no register.
noncomputable def Rs1Ra [Field F] {program : JoltProgram}
    (trace : JoltTrace program) : Fin 128 → Fin p.traceLength → F :=
  fun address t =>
    -- The witness includes padding beyond the actual execution rows.
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
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
          if address = sourceRegisterAddress src then 1 else 0
      -- Alignment assertions can read architectural or virtual registers.
      | .VirtualAssertHalfwordAlignment base _ _ | .VirtualAssertWordAlignment base _ _ =>
          if address = sourceRegisterAddress base then 1 else 0
      | .LUI _ _ | .AUIPC _ _ | .JAL _ _ | .FENCE | .VirtualPow2I _ _ | .VirtualPow2IW _ _
      | .VirtualShiftRightBitmaskI _ _ | .VirtualAdvice _ _ _ | .VirtualAdviceLoad _ _ => 0
    else 0

end HonestWitness
