import JoltBytecode.JoltISA.Instruction
import JoltBytecode.InstructionEquivalence.ProofSupport.VirtualRegisters

/-!
# Protected virtual-register write footprints

Some registers like control status registers are present both as virtual registers,
and as keyed registers in the sail hash map.
This makes the final projection lemma a little complicated.
However, most instructions and jolt programs do not write to these registers.
This would simply system project a great deal.
Here we prove which instructions, write and do not write to these protected virtual registers.
-/

namespace JoltISA

/-- A destination writes a protected virtual register when it is a protected
virtual-register destination. -/
def Dst.WritesProtectedVReg : Dst → Prop
  | .vreg vr => IsProtectedJoltRegister vr
  | .xreg _ => False

/-- Determine whether a Jolt instruction can write a protected virtual
register. -/
def Instr.WritesProtectedVReg : Instr → Prop
  | .ADDI dst _ _
  | .ADDIW dst _ _
  | .ANDI dst _ _
  | .ORI dst _ _
  | .XORI dst _ _
  | .SLTI dst _ _
  | .SLTIU dst _ _
  | .LUI dst _
  | .AUIPC dst _
  | .JAL dst _
  | .JALR dst _ _
  | .ADD dst _ _
  | .ADDW dst _ _
  | .SUB dst _ _
  | .SUBW dst _ _
  | .MUL dst _ _
  | .MULW dst _ _
  | .MULHU dst _ _
  | .ANDN dst _ _
  | .VirtualMULI dst _ _
  | .VirtualMULIW dst _ _
  | .VirtualPow2 dst _
  | .VirtualPow2W dst _
  | .VirtualPow2I dst _
  | .VirtualPow2IW dst _
  | .VirtualShiftRightBitmask dst _
  | .VirtualShiftRightBitmaskI dst _
  | .VirtualShiftRightBitmaskW dst _
  | .VirtualSRLI dst _ _
  | .VirtualSRAI dst _ _
  | .VirtualSRLIW dst _ _
  | .VirtualSRAIW dst _ _
  | .VirtualSRL dst _ _
  | .VirtualSRA dst _ _
  | .VirtualSRLW dst _ _
  | .VirtualSRAW dst _ _
  | .VirtualROTRI dst _ _
  | .VirtualROTRIW dst _ _
  | .VirtualRev8W dst _
  | .VirtualXORROT32 dst _ _
  | .VirtualXORROT24 dst _ _
  | .VirtualXORROT16 dst _ _
  | .VirtualXORROT63 dst _ _
  | .VirtualXORROTW16 dst _ _
  | .VirtualXORROTW12 dst _ _
  | .VirtualXORROTW8 dst _ _
  | .VirtualXORROTW7 dst _ _
  | .VirtualXORROTW22 dst _ _
  | .VirtualXORROTW19 dst _ _
  | .VirtualXORROTW6 dst _ _
  | .OR dst _ _
  | .XOR dst _ _
  | .AND dst _ _
  | .SLT dst _ _
  | .SLTU dst _ _
  | .VirtualAlignAddr dst _ _
  | .VirtualWindowMaskB dst _ _
  | .VirtualWindowMaskH dst _ _
  | .VirtualWindowMaskW dst _ _
  | .VirtualPext dst _ _
  | .VirtualPextSigned dst _ _
  | .VirtualShiftDataB dst _ _
  | .VirtualShiftDataH dst _ _
  | .VirtualShiftDataW dst _ _
  | .VirtualSignExtendWord dst _
  | .VirtualZeroExtendWord dst _
  | .VirtualMovsign dst _
  | .VirtualAdvice dst _
  | .VirtualAdviceLoad dst _
  | .VirtualAdviceLen dst _
  | .VirtualNegateIf dst _ _ => dst.WritesProtectedVReg
  | .LD _ dst _ _ => (sideEffectingDst dst).WritesProtectedVReg
  | .BEQ _ _ _
  | .BNE _ _ _
  | .BLT _ _ _
  | .BGE _ _ _
  | .BLTU _ _ _
  | .BGEU _ _ _
  | .FENCE
  | .VirtualAssertHalfwordAlignment _ _ _
  | .VirtualAssertWordAlignment _ _ _
  | .SD _ _ _
  | .VirtualHostIO
  | .VirtualAssertEQ _ _ _
  | .VirtualAssertValidDiv0 _ _
  | .VirtualAssertValidUnsignedRemainder _ _
  | .VirtualAssertMulUNoOverflow _ _
  | .VirtualAssertLTE _ _ => False

/-- A program writes a protected virtual register when one of its instructions
does. -/
def Program.WritesProtectedVReg : Program → Prop
  | .done _ => False
  | .instr instruction rest =>
      instruction.WritesProtectedVReg ∨ rest.WritesProtectedVReg

/-- This destination does not write a protected virtual register. -/
def Dst.DoesNotWriteProtectedVRegs (dst : Dst) : Prop :=
  ¬ dst.WritesProtectedVReg

/-- This instruction does not write a protected virtual register. -/
def Instr.DoesNotWriteProtectedVRegs (instr : Instr) : Prop :=
  ¬ instr.WritesProtectedVReg

/-- This program does not write a protected virtual register. -/
def Program.DoesNotWriteProtectedVRegs (program : Program) : Prop :=
  ¬ program.WritesProtectedVReg

/-- TODO: Docs -/
@[simp] theorem rdZeroRewriteVReg_not_protected :
    ¬ IsProtectedJoltRegister rdZeroRewriteVReg :=
  inlineTmp0_not_protected

end JoltISA
