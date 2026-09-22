import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.witness_helpers.register_address

set_option autoImplicit false

namespace HonestWitness

-- Rust: [materialize_register_read_write_virtual](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/registers.rs:47).
-- Select the captured destination register. HOST_IO has a captured rd even though
-- it does not write it. Absent destinations and padding select no register.
noncomputable def RdWa {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) :
    Fin 128 → Fin p.traceLength → F :=
  fun address t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
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
      | .VirtualXORROTW16 dst _ _ | .VirtualXORROTW12 dst _ _ | .VirtualXORROTW8 dst _ _
      | .VirtualXORROTW7 dst _ _ | .VirtualXORROTW22 dst _ _ | .VirtualXORROTW19 dst _ _
      | .VirtualXORROTW6 dst _ _ | .OR dst _ _ | .XOR dst _ _ | .AND dst _ _ | .SLT dst _ _
      | .SLTU dst _ _ | .VirtualAlignAddr dst _ _ | .VirtualWindowMaskB dst _ _
      | .VirtualWindowMaskH dst _ _ | .VirtualWindowMaskW dst _ _ | .VirtualPext dst _ _
      | .VirtualPextSigned dst _ _ | .VirtualShiftDataB dst _ _ | .VirtualShiftDataH dst _ _
      | .VirtualShiftDataW dst _ _ | .VirtualSignExtendWord dst _ _ | .VirtualZeroExtendWord dst _ _
      | .VirtualMovsign dst _ _ | .VirtualAdvice dst _ _ | .VirtualAdviceLoad dst _
      | .VirtualAdviceLen dst _ _ | .VirtualHostIO dst _ _ | .VirtualNegateIf dst _ _ =>
          if address = destinationRegisterAddress dst then 1 else 0
      -- LD execution uses this same ISA helper to redirect a destination of x0.
      -- Select the effective destination, where execInstr actually wrote the value.
      | .LD _ dst _ _ =>
          if address = destinationRegisterAddress (JoltISA.sideEffectingDst dst) then 1 else 0
      | .BEQ _ _ _ | .BNE _ _ _ | .BLT _ _ _ | .BGE _ _ _ | .BLTU _ _ _ | .BGEU _ _ _ | .FENCE
      | .VirtualAssertHalfwordAlignment _ _ _ | .VirtualAssertWordAlignment _ _ _ | .SD _ _ _
      | .VirtualAssertEQ _ _ _ | .VirtualAssertValidDiv0 _ _ _
      | .VirtualAssertValidUnsignedRemainder _ _ _ | .VirtualAssertMulUNoOverflow _ _ _
      | .VirtualAssertLTE _ _ _ => 0
    else 0

end HonestWitness
