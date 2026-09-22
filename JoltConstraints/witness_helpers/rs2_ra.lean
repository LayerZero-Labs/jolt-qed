import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.witness_helpers.register_address

set_option autoImplicit false

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [materialize_register_read_write_virtual](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/registers.rs:47).
-- Select the instruction's second source register, including an explicit x0.
-- An absent operand and a padding position select no register.
noncomputable def Rs2Ra [Field F] {program : JoltProgram}
    (trace : JoltTrace program) : Fin 128 → Fin p.traceLength → F :=
  fun address t =>
    -- The witness includes padding beyond the actual execution rows.
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
      match instruction with
      | .BEQ _ src _ | .BNE _ src _ | .BLT _ src _ | .BGE _ src _ | .BLTU _ src _ | .BGEU _ src _
      | .ADD _ _ src | .ADDW _ _ src | .SUB _ _ src | .SUBW _ _ src | .MUL _ _ src
      | .MULW _ _ src | .MULHU _ _ src | .ANDN _ _ src | .VirtualSRL _ _ src
      | .VirtualSRA _ _ src | .VirtualSRLW _ _ src | .VirtualSRAW _ _ src
      | .VirtualXORROT32 _ _ src | .VirtualXORROT24 _ _ src | .VirtualXORROT16 _ _ src
      | .VirtualXORROT63 _ _ src | .VirtualXORROTW16 _ _ src | .VirtualXORROTW12 _ _ src
      | .VirtualXORROTW8 _ _ src | .VirtualXORROTW7 _ _ src | .VirtualXORROTW22 _ _ src
      | .VirtualXORROTW19 _ _ src | .VirtualXORROTW6 _ _ src | .OR _ _ src | .XOR _ _ src
      | .AND _ _ src | .SLT _ _ src | .SLTU _ _ src | .VirtualPext _ _ src
      | .VirtualPextSigned _ _ src | .VirtualShiftDataB _ _ src | .VirtualShiftDataH _ _ src
      | .VirtualShiftDataW _ _ src | .SD _ src _ | .VirtualAssertEQ _ src _
      | .VirtualAssertValidDiv0 _ src _ | .VirtualNegateIf _ _ src
      | .VirtualAssertValidUnsignedRemainder _ src _ | .VirtualAssertMulUNoOverflow _ src _
      | .VirtualAssertLTE _ src _ =>
          if address = sourceRegisterAddress src then 1 else 0
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
      | .VirtualHostIO _ _ _ => 0
    else 0

end HonestWitness
