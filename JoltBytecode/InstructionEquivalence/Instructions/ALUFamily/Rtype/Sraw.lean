import JoltBytecode.Bundles
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.ANDI
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSRA
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
# SRAW: 5-step bitmask-encoded arithmetic right shift = Sail SRAW

Jolt program sequence:
1. `VirtualSignExtendWord v0, rs1` — sign-extend `rs1[31:0]` to 64 bits
2. `ANDI v1, rs2, 0x1f` — mask shift amount to 5 bits
3. `VirtualShiftRightBitmask v1, v1` — compute bitmask from `v1`
4. `VirtualSRA rd, v0, v1` — arithmetic right shift via `ctz(bitmask)`
5. `VirtualSignExtendWord rd, rd` — sign-extend lower 32 bits of `rd`

The local value lemma proves that sign-extending the source word, masking
the shift amount, and using the virtual arithmetic shift agrees with Sail's
word arithmetic right shift.
  -/

abbrev sraw_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb v1 31 0)
    (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb v2 31 0) 4 0))

abbrev sraw_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    (Sail.BitVec.extractLsb
      (jolt_virtual_sra_value
        (sign_extend (m := 64) (Sail.BitVec.extractLsb v1 31 0))
        (jolt_virtual_shift_right_bitmask_value
          (v2 &&& sign_extend (m := 64) (0x1f : BitVec 12)))) 31 0)

private lemma sail_sraw_eq_riscv (v1 v2 : BitVec 64) :
    sraw_sail_operation v1 v2 = Riscv.sraw v1 v2 := by
  unfold sraw_sail_operation Riscv.sraw sign_extend shift_bits_right_arith
  simp only [Sail.BitVec.signExtend, Sail.BitVec.toNatInt, Sail.BitVec.extractLsb,
    BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_zero,
    BitVec.ofNat_toNat, Nat.sub_zero, Nat.reduceAdd]
  rw [BitVec.setWidth_setWidth_of_le v2 (by norm_num : 5 ≤ 32)]
  congr 2

/-- Main program-level equivalence for `SRAW`. -/
def srawProgramEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.srawProgramAuto rd rs1 rs2)).run js) =
    (execute_RTYPEW rs2 rs1 rd ropw.SRAW).run js.sail

/-- Main program-level equivalence for `SRAW`. -/
theorem srawProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    srawProgramEqSailStatement rs2 rs1 rd js h := by
  unfold srawProgramEqSailStatement
  let v1 := h.rs1_val
  let v2 := h.rs2_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail := h.rs1_read
  have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail := h.rs2_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.srawProgramAuto
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
      jolt_virtual_sraw_value v1 mask = sraw_sail_operation v1 v2 := by
    unfold jolt_virtual_sraw_value
    rw [h_mask_ctz]
    change Riscv.sraw v1 v2 = sraw_sail_operation v1 v2
    exact (sail_sraw_eq_riscv v1 v2).symm

  let js_tmp : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = tmp then mask else js.vregs r }
  obtain ⟨s', h_write⟩ := wX_shape rd (sraw_sail_operation v1 v2) js.sail
  let js_final : SailJoltState := { sail := s', vregs := js_tmp.vregs }

  simp only [execute_RTYPEW]
  simp only [EStateM.run_bind]
  simp only [EStateM.run]
  simp only [h_read_rs1, h_read_rs2, pure, EStateM.pure, h_write]

  unfold JoltISA.srawProgramAuto
  rw [hrd_not_x0]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change System.systemProjectResult
    (JoltISA.execProgram
      (.instr (.VirtualShiftRightBitmaskW (.vreg tmp) (.xreg rs2))
        (.instr (.VirtualSRAW (.xreg rd) (.xreg rs1) (.vreg tmp))
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
      JoltISA.execInstr (.VirtualSRAW (.xreg rd) (.xreg rs1) (.vreg tmp)) js_tmp =
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
          (.instr (.VirtualSRAW (.xreg rd) (.xreg rs1) (.vreg tmp))
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
          (.instr (.VirtualSRAW (.xreg rd) (.xreg rs1) (.vreg tmp))
            (.done RETIRE_SUCCESS))) := by
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      true_and]
    exact ⟨by simpa only [tmp] using JoltISA.inlineTmp0_not_protected, trivial⟩
  have h_projected : Projection.ProjectedVRegsPreserved js js_final :=
    Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
      (js := js) (js' := js_final) (result := RETIRE_SUCCESS) hsafe h_program
  have h_final_sail :
      js_final.sail = stateAfterWrite js.sail rd (sraw_sail_operation v1 v2) := by
    simpa only [js_final] using
      wX_bits_eq_stateAfterWrite rd (sraw_sail_operation v1 v2) js.sail s' h_write
  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_final rd (sraw_sail_operation v1 v2) h_final_sail h_projected]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (sraw_sail_operation v1 v2)
    js.sail s' h_write).symm

end
