import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness_helpers.destination_capture

open LeanRV64D

set_option autoImplicit false

namespace TraceWitness

/-- The captured destination value from the supplied state, cast to the field.
Absent destinations contribute zero; a pre-state gives the old destination value.
For example, a floor load reads its destination from the post-state to obtain the loaded word.
Jolt's tracer: `tracer/src/instruction/virtual_load_{b,h,w}.rs`
(`RegisterStateLoad`), `virtual_store_{b,h,w}.rs` (`RegisterStateS`) and
`format/format_shift_data.rs` (`FormatShiftData`) at `c6703570`. -/
noncomputable def rdValue {F : Type} [Field F]
    (instruction : JoltISA.Instr) (state : SailJoltState) : F :=
  let destinationValue (dst : JoltISA.Dst) : F :=
    ((capturedDestinationValue dst state).toNat : F)
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
  | .SLTU dst _ _ | .VirtualWindowMaskB dst _ _
  | .VirtualWindowMaskH dst _ _ | .VirtualWindowMaskW dst _ _ | .VirtualPext dst _ _
  | .VirtualPextSigned dst _ _ | .VirtualShiftDataB dst _ _ _ | .VirtualShiftDataH dst _ _ _
  | .VirtualShiftDataW dst _ _ _ | .VirtualSignExtendWord dst _ _ | .VirtualZeroExtendWord dst _ _
  | .VirtualMovsign dst _ _ | .VirtualAdvice dst _ _ | .VirtualAdviceLoad dst _
  | .VirtualNegateIf dst _ _ =>
      destinationValue dst
  | .LD _ dst _ _
  | .VirtualLoadB _ dst _ _ _ | .VirtualLoadH _ dst _ _ _ | .VirtualLoadW _ dst _ _ _ => destinationValue dst
  | .BEQ _ _ _ | .BNE _ _ _ | .BLT _ _ _ | .BGE _ _ _ | .BLTU _ _ _ | .BGEU _ _ _ | .FENCE
  | .SD _ _ _
  | .VirtualStoreB _ _ _ _ | .VirtualStoreH _ _ _ _ | .VirtualStoreW _ _ _ _
  | .VirtualAssertEQ _ _ _ | .VirtualAssertValidDiv0 _ _ _
  | .VirtualAssertValidUnsignedRemainder _ _ _ | .VirtualAssertMulUNoOverflow _ _ _
  | .VirtualAssertLTE _ _ _ | .VirtualHostIO => 0

end TraceWitness
