import JoltBytecode.Bundles
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.Mul
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSignExtendWord
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import Mathlib.Data.Nat.Bitwise

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLW: VirtualPow2W + MUL + VSEW = Sail SLLW

Jolt program sequence:
1. `VirtualPow2W v0, rs2` — compute `2 ^ (rs2[4:0])`
2. `MUL rd, rs1, v0` — multiply `rs1` by the power of two
3. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

The local value lemma proves that multiplying by `2 ^ rs2[4:0]` and then
sign-extending the low word agrees with Sail's word left shift.
  -/

abbrev sllw_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (shift_bits_left (Sail.BitVec.extractLsb v1 31 0)
    (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))

abbrev sllw_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb (v1 * jolt_virtual_pow2w_value v2) 31 0)

private lemma sll_32_eq_mul_trunc (x : BitVec 64) (s : Nat) (hs : s < 32) :
    x.setWidth 32 <<< s = (x * BitVec.ofNat 64 (2 ^ s)).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega : s < 64))]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by norm_num : 32 ≤ 64))]
  have hp : 2 ^ s < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) hs
  have hmul := (Nat.mul_mod x.toNat (2 ^ s) (2 ^ 32)).symm
  rw [Nat.mod_eq_of_lt hp] at hmul
  exact hmul

/-- Main program-level equivalence for `SLLW`. -/
def sllwProgramEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.sllwProgramAuto rd rs1 rs2)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SLLW).run js.sail

/-- Main program-level equivalence for `SLLW`. -/
theorem sllwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    sllwProgramEqSailStatement rs2 rs1 rd js h := by
  unfold sllwProgramEqSailStatement
  let v1 := h.rs1_val
  let v2 := h.rs2_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail := h.rs1_read
  have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail := h.rs2_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.sllwProgramAuto
    rw [JoltISA.isX0_regidx_zero]
    simp only [↓reduceIte]
    change System.systemProjectResult
      ((JoltISA.execProgram JoltISA.pureWritebackRdZeroProgram).run js) = _
    rw [JoltISA.pureWritebackRdZeroProgram_run js]
    simp only [System.systemProjectResult]
    rw [h_project_initial]
    simp only [execute_RTYPEW]
    simp only [EStateM.run_bind]
    simp only [EStateM.run]
    simp only [h_read_rs1, h_read_rs2, pure, EStateM.pure, wX_bits_regidx_zero]

  have hrd_not_x0 : JoltISA.isX0 rd = false :=
    JoltISA.isX0_eq_false_of_ne_zero hrd
  have h_value :
      jolt_mulw_value v1 (jolt_virtual_pow2w_value v2) =
        sllw_sail_operation v1 v2 := by
    unfold jolt_mulw_value jolt_virtual_pow2w_value sllw_sail_operation
    unfold sign_extend shift_bits_left
    simp only [Sail.BitVec.signExtend, Sail.BitVec.extractLsb,
      BitVec.extractLsb, Nat.sub_zero, Nat.reduceAdd, BitVec.extractLsb',
      Nat.shiftRight_zero, BitVec.ofNat_toNat]
    rw [BitVec.setWidth_setWidth_of_le v2 (by norm_num : 5 ≤ 32)]
    change
      ((v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 5).toNat)).setWidth 32).signExtend 64 =
        (v1.setWidth 32 <<< (v2.setWidth 5).toNat).signExtend 64
    congr 1
    exact (sll_32_eq_mul_trunc v1 (v2.setWidth 5).toNat (by
      have := (v2.setWidth 5).isLt
      norm_num at this
      exact this)).symm

  let tmp := JoltISA.inlineTmp0
  let pow2 := jolt_virtual_pow2w_value v2
  let js_tmp : SailJoltState :=
    { js with
      vregs := fun r => if r = tmp then pow2 else js.vregs r }
  obtain ⟨s', h_write⟩ := wX_shape rd (sllw_sail_operation v1 v2) js.sail
  let js_final : SailJoltState := { js_tmp with sail := s' }

  simp only [execute_RTYPEW]
  simp only [EStateM.run_bind]
  simp only [EStateM.run]
  simp only [h_read_rs1, h_read_rs2, pure, EStateM.pure, h_write]

  unfold JoltISA.sllwProgramAuto
  rw [hrd_not_x0]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change System.systemProjectResult
    (JoltISA.execProgram
      (.instr (.VirtualPow2W (.vreg tmp) (.xreg rs2))
        (.instr (.MULW (.xreg rd) (.xreg rs1) (.vreg tmp))
          (.done RETIRE_SUCCESS))) js) = _
  have htmp : WritableVReg tmp := by
    unfold tmp WritableVReg
    decide
  have h_read_rs1_tmp : rX_bits rs1 js_tmp.sail = .ok v1 js_tmp.sail := by
    simpa only [js_tmp] using h_read_rs1
  have h_first :
      JoltISA.execInstr (.VirtualPow2W (.vreg tmp) (.xreg rs2)) js =
        .ok RETIRE_SUCCESS js_tmp := by
    unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst liftSail
    simp only [h_read_rs2, bind, EStateM.bind]
    simpa only [js_tmp, pow2] using
      JoltISA.writeVReg_retire_run_of_writable tmp pow2 js htmp
  have h_second :
      JoltISA.execInstr (.MULW (.xreg rd) (.xreg rs1) (.vreg tmp)) js_tmp =
        .ok RETIRE_SUCCESS js_final := by
    unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst liftSail
    simp only [h_read_rs1_tmp, bind, EStateM.bind]
    simp only [readVReg_run]
    simp only [js_tmp, if_pos, pow2]
    rw [h_value]
    rw [h_write]
    rfl
  have h_program :
      JoltISA.execProgram
        (.instr (.VirtualPow2W (.vreg tmp) (.xreg rs2))
          (.instr (.MULW (.xreg rd) (.xreg rs1) (.vreg tmp))
            (.done RETIRE_SUCCESS))) js =
        .ok RETIRE_SUCCESS js_final := by
    simp only [JoltISA.execProgram_instr, bind, EStateM.bind]
    rw [h_first]
    simp only [RETIRE_SUCCESS, pure]
    simp only [EStateM.bind]
    rw [h_second]
    rfl
  rw [h_program]
  simp only [System.systemProjectResult]
  congr 1
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (.instr (.VirtualPow2W (.vreg tmp) (.xreg rs2))
          (.instr (.MULW (.xreg rd) (.xreg rs1) (.vreg tmp))
            (.done RETIRE_SUCCESS))) := by
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      true_and]
    exact ⟨by simpa only [tmp] using JoltISA.inlineTmp0_not_protected, trivial⟩
  have h_projected : Projection.ProjectedVRegsPreserved js js_final :=
    Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
      (js := js) (js' := js_final) (result := RETIRE_SUCCESS) hsafe h_program
  have h_final_sail :
      js_final.sail = stateAfterWrite js.sail rd (sllw_sail_operation v1 v2) := by
    simpa only [js_final] using
      wX_bits_eq_stateAfterWrite rd (sllw_sail_operation v1 v2) js.sail s' h_write
  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_final rd (sllw_sail_operation v1 v2) h_final_sail h_projected]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (sllw_sail_operation v1 v2)
    js.sail s' h_write).symm

end
