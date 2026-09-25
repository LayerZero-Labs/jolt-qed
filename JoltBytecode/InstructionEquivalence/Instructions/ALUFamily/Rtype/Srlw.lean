import JoltBytecode.Bundles
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.ORI
import JoltBytecode.InstructionEquivalence.ProofSupport.ExpansionBlocks.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSRL
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualShiftRightBitmask
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSignExtendWord
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas
import JoltBytecode.JoltISA.Values
import Mathlib.Data.Nat.Bitwise

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRLW: SLLI + ORI + bitmask + VirtualSRL + VSEW = Sail SRLW

Jolt program sequence:
1. `SLLI v0, rs1, 32` — clear upper 32 bits
2. `ORI v1, rs2, 32` — set bit 5 of the shift amount
3. `VirtualShiftRightBitmask v1, v1` — compute bitmask
4. `VirtualSRL rd, v0, v1` — logical right shift via `ctz(bitmask)`
5. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

The local value lemma proves that the `SLLI 32` plus encoded bitmask shift
agrees with Sail's word logical right shift.
  -/

abbrev srlw_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v1 31 0)
    (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))

abbrev srlw_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb
      (jolt_virtual_srl_value (shift_bits_left v1 (32 : BitVec 6))
        (jolt_virtual_shift_right_bitmask_value
          (v2 ||| sign_extend (m := 64) (32 : BitVec 12)))) 31 0)

/-- Main program-level equivalence for `SRLW`. -/
def srlwProgramEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.srlwProgramAuto rd rs1 rs2)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRLW).run js.sail

/-- Main program-level equivalence for `SRLW`. -/
theorem srlwProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    srlwProgramEqSailStatement rs2 rs1 rd js h := by
  unfold srlwProgramEqSailStatement
  let v1 := h.rs1_val
  let v2 := h.rs2_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail := h.rs1_read
  have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail := h.rs2_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.srlwProgramAuto
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
  let tmp := JoltISA.inlineTmp0
  let mask := jolt_virtual_shift_right_bitmaskw_value v2
  have h_mask_ctz : ctz mask.toNat = (v2.setWidth 5).toNat := by
    unfold mask jolt_virtual_shift_right_bitmaskw_value
    rw [BitVec.toNat_ofNat]
    have hlt : 2 ^ 32 - 2 ^ (v2.setWidth 5).toNat < 2 ^ 64 := by
      exact lt_of_le_of_lt (Nat.sub_le _ _) (by norm_num)
    rw [Nat.mod_eq_of_lt hlt]
    simpa only [Nat.shiftLeft_eq, one_mul] using
      ctz_word_shift_bitmask (v2.setWidth 5).toNat (by
      have := (v2.setWidth 5).isLt
      norm_num at this
      exact this)
  have h_value :
      jolt_virtual_srlw_value v1 mask = srlw_sail_operation v1 v2 := by
    unfold jolt_virtual_srlw_value srlw_sail_operation
    rw [h_mask_ctz]
    unfold sign_extend shift_bits_right
    simp [Sail.BitVec.signExtend, Sail.BitVec.extractLsb,
      BitVec.extractLsb, BitVec.extractLsb']

  let js_tmp : SailJoltState :=
    { js with
      vregs := fun r => if r = tmp then mask else js.vregs r }
  obtain ⟨s', h_write⟩ := wX_shape rd (srlw_sail_operation v1 v2) js.sail
  let js_final : SailJoltState := { js_tmp with sail := s' }

  simp only [execute_RTYPEW]
  simp only [EStateM.run_bind]
  simp only [EStateM.run]
  simp only [h_read_rs1, h_read_rs2, pure, EStateM.pure, h_write]

  unfold JoltISA.srlwProgramAuto
  rw [hrd_not_x0]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change System.systemProjectResult
    (JoltISA.execProgram
      (.instr (.VirtualShiftRightBitmaskW (.vreg tmp) (.xreg rs2))
        (.instr (.VirtualSRLW (.xreg rd) (.xreg rs1) (.vreg tmp))
          (.done RETIRE_SUCCESS))) js) = _
  have htmp : WritableVReg tmp := by
    unfold tmp WritableVReg
    decide
  have h_read_rs1_tmp : rX_bits rs1 js_tmp.sail = .ok v1 js_tmp.sail := by
    simpa only [js_tmp] using h_read_rs1
  have h_first :
      JoltISA.execInstr (.VirtualShiftRightBitmaskW (.vreg tmp) (.xreg rs2)) js =
        .ok RETIRE_SUCCESS js_tmp := by
    unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst liftSail
    simp only [h_read_rs2, bind, EStateM.bind]
    simpa only [js_tmp, mask] using
      JoltISA.writeVReg_retire_run_of_writable tmp mask js htmp
  have h_second :
      JoltISA.execInstr (.VirtualSRLW (.xreg rd) (.xreg rs1) (.vreg tmp)) js_tmp =
        .ok RETIRE_SUCCESS js_final := by
    unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst liftSail
    simp only [h_read_rs1_tmp, bind, EStateM.bind]
    simp only [readVReg_run]
    simp only [js_tmp, if_pos]
    rw [h_value]
    rw [h_write]
    rfl
  have h_program :
      JoltISA.execProgram
        (.instr (.VirtualShiftRightBitmaskW (.vreg tmp) (.xreg rs2))
          (.instr (.VirtualSRLW (.xreg rd) (.xreg rs1) (.vreg tmp))
            (.done RETIRE_SUCCESS))) js =
        .ok RETIRE_SUCCESS js_final := by
    simp only [JoltISA.execProgram_instr, bind, EStateM.bind]
    rw [h_first]
    simp only [RETIRE_SUCCESS, pure, EStateM.bind]
    rw [h_second]
    rfl
  rw [h_program]
  simp only [System.systemProjectResult]
  congr 1
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (.instr (.VirtualShiftRightBitmaskW (.vreg tmp) (.xreg rs2))
          (.instr (.VirtualSRLW (.xreg rd) (.xreg rs1) (.vreg tmp))
            (.done RETIRE_SUCCESS))) := by
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      true_and]
    exact ⟨by simpa only [tmp] using JoltISA.inlineTmp0_not_protected, trivial⟩
  have h_projected : Projection.ProjectedVRegsPreserved js js_final :=
    Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
      (js := js) (js' := js_final) (result := RETIRE_SUCCESS) hsafe h_program
  have h_final_sail :
      js_final.sail = stateAfterWrite js.sail rd (srlw_sail_operation v1 v2) := by
    simpa only [js_final] using
      wX_bits_eq_stateAfterWrite rd (srlw_sail_operation v1 v2) js.sail s' h_write
  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_final rd (srlw_sail_operation v1 v2) h_final_sail h_projected]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (srlw_sail_operation v1 v2)
    js.sail s' h_write).symm

end
