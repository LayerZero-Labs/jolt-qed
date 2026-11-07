import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.witness_helpers.register_address

open LeanRV64D

set_option autoImplicit false

namespace TraceWitness

variable {F : Type} (p : WitnessParams)

/-- The indicator of the encoded first source register.
Absent operands and padding contribute zero.
For example, a floor load selects its base, including explicit x0.
Jolt's tracer: `tracer/src/instruction/virtual_load_{b,h,w}.rs`
(`RegisterStateLoad`), `virtual_store_{b,h,w}.rs` (`RegisterStateS`) and
`format/format_shift_data.rs` (`FormatShiftData`) at `c6703570`. -/
noncomputable def Rs1Ra [Field F] (trace : Trace) : Fin 128 → Fin p.traceLength → F :=
  fun address t =>
    -- The witness includes padding beyond the actual execution rows.
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
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
      | .SLTU _ src _ | .VirtualWindowMaskB _ src _
      | .VirtualWindowMaskH _ src _ | .VirtualWindowMaskW _ src _ | .VirtualPext _ src _
      | .VirtualPextSigned _ src _ | .VirtualShiftDataB _ src _ _ | .VirtualShiftDataH _ src _ _
      | .VirtualShiftDataW _ src _ _ | .VirtualSignExtendWord _ src _ | .VirtualZeroExtendWord _ src _
      | .VirtualMovsign _ src _ | .LD _ _ src _
      | .VirtualLoadB _ _ src _ _ | .VirtualLoadH _ _ src _ _ | .VirtualLoadW _ _ src _ _ | .SD src _ _
      | .VirtualStoreB src _ _ _ | .VirtualStoreH src _ _ _ | .VirtualStoreW src _ _ _ | .VirtualAssertEQ src _ _
      | .VirtualAssertValidDiv0 src _ _ | .VirtualNegateIf _ src _
      | .VirtualAssertValidUnsignedRemainder src _ _ | .VirtualAssertMulUNoOverflow src _ _
      | .VirtualAssertLTE src _ _ =>
          if address = sourceRegisterAddress src then 1 else 0
      | .LUI _ _ | .AUIPC _ _ | .JAL _ _ | .FENCE | .VirtualHostIO | .VirtualPow2I _ _ | .VirtualPow2IW _ _
      | .VirtualShiftRightBitmaskI _ _ | .VirtualAdvice _ _ _ | .VirtualAdviceLoad _ _ => 0
    else 0

end TraceWitness
