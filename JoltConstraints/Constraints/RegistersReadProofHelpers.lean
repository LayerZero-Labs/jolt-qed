import JoltConstraints.Constraints.RegistersValHistoryProofHelpers
import JoltConstraints.honest_witness

/-!
Source-register reads for the honest register witness.
Each real row selects at most one first and one second source register.
The selected register's replayed history equals the row's pre-state value.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped BigOperators

namespace JoltConstraints

/-- First source register read by an instruction, matching `HonestWitness.Rs1Ra`.
Alignment assertions read their base register through this operand. -/
def rs1Operand? : JoltISA.Instr → Option JoltISA.Src
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
  | .VirtualAssertLTE src _ _ | .VirtualAdviceLen _ src _ | .VirtualHostIO _ src _
  | .VirtualAssertHalfwordAlignment src _ _ | .VirtualAssertWordAlignment src _ _ => some src
  | .LUI _ _ | .AUIPC _ _ | .JAL _ _ | .FENCE | .VirtualPow2I _ _ | .VirtualPow2IW _ _
  | .VirtualShiftRightBitmaskI _ _ | .VirtualAdvice _ _ _ | .VirtualAdviceLoad _ _ => none

/-- Second source register read by an instruction, matching `HonestWitness.Rs2Ra`. -/
def rs2Operand? : JoltISA.Instr → Option JoltISA.Src
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
  | .VirtualAssertLTE _ src _ => some src
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

theorem rs1Operand_canonical
    (instr : JoltISA.Instr) (src : JoltISA.Src)
    (hcanon : JoltRegisterEncoding.instructionIsCanonical instr = true)
    (hsrc : rs1Operand? instr = some src) :
    JoltRegisterEncoding.sourceIsCanonical src = true := by
  cases instr <;>
    simp_all [rs1Operand?, JoltRegisterEncoding.instructionIsCanonical]

theorem rs2Operand_canonical
    (instr : JoltISA.Instr) (src : JoltISA.Src)
    (hcanon : JoltRegisterEncoding.instructionIsCanonical instr = true)
    (hsrc : rs2Operand? instr = some src) :
    JoltRegisterEncoding.sourceIsCanonical src = true := by
  cases instr <;>
    simp_all [rs2Operand?, JoltRegisterEncoding.instructionIsCanonical]

theorem canonicalSource_vreg_ge32 (vr : JoltISA.VReg)
    (hcanon : JoltRegisterEncoding.sourceIsCanonical (.vreg vr) = true) :
    32 ≤ vr.toNat := by
  by_contra hlt
  have hn : vr.toNat ≤ 31 := by omega
  interval_cases h : vr.toNat <;>
    simp [JoltRegisterEncoding.sourceIsCanonical,
      JoltISA.joltRegisterSlot, h] at hcanon

/-- A canonical source is recovered from its witness address.
Architectural registers use addresses below 32; canonical virtual ones do not. -/
theorem srcOfAddress_sourceRegisterAddress (src : JoltISA.Src)
    (hcanon : JoltRegisterEncoding.sourceIsCanonical src = true) :
    register42_srcOfAddress (HonestWitness.sourceRegisterAddress src) = src := by
  cases src with
  | xreg rs =>
      cases rs with
      | Regidx bits =>
          have hlt : bits.toNat < 32 := bits.isLt
          have haddr :
              (HonestWitness.sourceRegisterAddress
                (.xreg (.Regidx bits))).val = bits.toNat := by
            have hlt128 : bits.toNat < 128 := by omega
            simp [HonestWitness.sourceRegisterAddress,
              BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt128]
            exact hlt128
          simp [register42_srcOfAddress, haddr, hlt]
          exact hlt
  | vreg vr =>
      have hge := canonicalSource_vreg_ge32 vr hcanon
      simp [register42_srcOfAddress,
        HonestWitness.sourceRegisterAddress, hge]

theorem rs1Ra_real
    {F : Type} [Field F] (p : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (t : Fin p.traceLength) (hb : t.val < trace.rows.size)
    (register : Fin 128) :
    HonestWitness.Rs1Ra (F := F) p trace register t =
      match rs1Operand?
          trace.bytecode[(trace.rows[t.val]'hb).rowIndex].instruction with
      | some src =>
          if register = HonestWitness.sourceRegisterAddress src then 1 else 0
      | none => 0 := by
  unfold HonestWitness.Rs1Ra
  simp only [dif_pos hb]
  cases instr :
      trace.bytecode[(trace.rows[t.val]'hb).rowIndex].instruction <;>
    simp [rs1Operand?]

theorem rs1Value_real
    {F : Type} [Field F] (p : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (t : Fin p.traceLength) (hb : t.val < trace.rows.size) :
    HonestWitness.Rs1Value (F := F) p trace t =
      match rs1Operand?
          trace.bytecode[(trace.rows[t.val]'hb).rowIndex].instruction with
      | some src => ((JoltISA.sourceValue src (trace.rows[t.val]'hb).preState).toNat : F)
      | none => 0 := by
  unfold HonestWitness.Rs1Value
  simp only [dif_pos hb]
  cases instr :
      trace.bytecode[(trace.rows[t.val]'hb).rowIndex].instruction <;>
    simp [rs1Operand?]

theorem rs2Ra_real
    {F : Type} [Field F] (p : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (t : Fin p.traceLength) (hb : t.val < trace.rows.size)
    (register : Fin 128) :
    HonestWitness.Rs2Ra (F := F) p trace register t =
      match rs2Operand?
          trace.bytecode[(trace.rows[t.val]'hb).rowIndex].instruction with
      | some src =>
          if register = HonestWitness.sourceRegisterAddress src then 1 else 0
      | none => 0 := by
  unfold HonestWitness.Rs2Ra
  simp only [dif_pos hb]
  cases instr :
      trace.bytecode[(trace.rows[t.val]'hb).rowIndex].instruction <;>
    simp [rs2Operand?]

theorem rs2Value_real
    {F : Type} [Field F] (p : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (t : Fin p.traceLength) (hb : t.val < trace.rows.size) :
    HonestWitness.Rs2Value (F := F) p trace t =
      match rs2Operand?
          trace.bytecode[(trace.rows[t.val]'hb).rowIndex].instruction with
      | some src => ((JoltISA.sourceValue src (trace.rows[t.val]'hb).preState).toNat : F)
      | none => 0 := by
  unfold HonestWitness.Rs2Value
  simp only [dif_pos hb]
  cases instr :
      trace.bytecode[(trace.rows[t.val]'hb).rowIndex].instruction <;>
    simp [rs2Operand?]

/-- On a real row, the replayed history of a canonical source register is the
source value in the row's pre-state. -/
theorem registersVal_source_eq_preState
    {F : Type} [Field F] (p : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (traceFits : p.ProverPaddedFor trace.rows.size)
    (initialRegistersZero : ∀ src : JoltISA.Src,
      JoltISA.sourceValue src trace.initialState = 0)
    (t : Fin p.traceLength) (hb : t.val < trace.rows.size)
    (src : JoltISA.Src) (hcanon : JoltRegisterEncoding.sourceIsCanonical src = true) :
    HonestWitness.RegistersVal (F := F) p trace (HonestWitness.sourceRegisterAddress src) t =
      ((JoltISA.sourceValue src (trace.rows[t.val]'hb).preState).toNat : F) := by
  have h := register42_registersVal_preState (F := F) p trace traceFits
    initialRegistersZero (HonestWitness.sourceRegisterAddress src) t.val hb
  rw [srcOfAddress_sourceRegisterAddress src hcanon] at h
  exact h

end JoltConstraints
