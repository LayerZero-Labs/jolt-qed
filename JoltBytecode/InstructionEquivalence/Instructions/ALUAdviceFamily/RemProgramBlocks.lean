import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.DivProgramBlocks
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.RemuProgramBlocks

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

namespace Rem

abbrev v0 : JoltISA.VReg := JoltISA.inlineTmp0
abbrev v1 : JoltISA.VReg := JoltISA.inlineTmp1
abbrev v2 : JoltISA.VReg := JoltISA.inlineTmp2
abbrev v3 : JoltISA.VReg := JoltISA.inlineTmp3

def phase_setup (quotientMagnitude : BitVec 64) : JoltISA.Program :=
  Remu.phase_setup quotientMagnitude

def phase_product : JoltISA.Program :=
  .instr (.VirtualAssertMulUNoOverflow (.vreg v0) (.vreg v2)) <|
  .instr (.MUL (.vreg v3) (.vreg v0) (.vreg v2)) <|
  .instr (.VirtualAssertLTE (.vreg v3) (.vreg v1)) <|
  .done RETIRE_SUCCESS

def phase_remainder : JoltISA.Program :=
  .instr (.SUB (.vreg v3) (.vreg v1) (.vreg v3)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg v3) (.vreg v2)) <|
  .done RETIRE_SUCCESS

def phase_writeback (rs1 rd : regidx) : JoltISA.Program :=
  .instr (.VirtualNegateIf (.xreg rd) (.xreg rs1) (.vreg v3)) <|
  .done RETIRE_SUCCESS

theorem phase_setup_run (q : BitVec 64) (js : SailJoltState) :
    ∃ js',
      (JoltISA.execProgram (phase_setup q)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs v0 = q ∧ js'.sail = js.sail :=
  Remu.phase_setup_run q js

theorem phase_setup_run_sound
    (q : BitVec 64) (js js' : SailJoltState)
    (hrun : (JoltISA.execProgram (phase_setup q)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.vregs v0 = q ∧ js'.sail = js.sail :=
  Remu.phase_setup_run_sound q js js' hrun

theorem phase_product_run
    (js : SailJoltState)
    (q dividendMagnitude divisorMagnitude : BitVec 64)
    (h_v0 : js.vregs v0 = q)
    (h_v1 : js.vregs v1 = dividendMagnitude)
    (h_v2 : js.vregs v2 = divisorMagnitude)
    (hoverflow : q.toNat * divisorMagnitude.toNat < 2^64)
    (hlte : (q * divisorMagnitude).toNat ≤ dividendMagnitude.toNat) :
    ∃ js',
      (JoltISA.execProgram phase_product).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs v0 = q ∧
      js'.vregs v1 = dividendMagnitude ∧
      js'.vregs v2 = divisorMagnitude ∧
      js'.vregs v3 = q * divisorMagnitude ∧
      js'.sail = js.sail := by
  unfold phase_product
  have hguard1 : (js.vregs v0).toNat * (js.vregs v2).toNat < 2^64 := by
    rw [h_v0, h_v2]
    exact hoverflow
  have h1 := JoltISA.virtual_assert_mulu_no_overflow_v_run_ok v0 v2 js hguard1
  obtain ⟨s2, h2, hs2_v3, hs2_pres, hs2_sail⟩ :=
    JoltISA.mul_run_vreg_vreg_vreg_ex v3 v0 v2 js
      (by unfold WritableVReg; decide)
  have hs2_v0 : s2.vregs v0 = q := (hs2_pres v0 (by decide)).trans h_v0
  have hs2_v1 : s2.vregs v1 = dividendMagnitude :=
    (hs2_pres v1 (by decide)).trans h_v1
  have hs2_v2 : s2.vregs v2 = divisorMagnitude :=
    (hs2_pres v2 (by decide)).trans h_v2
  have hs2_v3_value : s2.vregs v3 = q * divisorMagnitude := by
    rw [hs2_v3, h_v0, h_v2]
  have hguard3 : (s2.vregs v3).toNat ≤ (s2.vregs v1).toNat := by
    rw [hs2_v3_value, hs2_v1]
    exact hlte
  have h3 := JoltISA.virtual_assert_lte_run_ok v3 v1 s2 hguard3
  refine ⟨s2, ?_, hs2_v0, hs2_v1, hs2_v2, hs2_v3_value, hs2_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ js s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s2 h3]
  rfl

theorem phase_product_run_sound
    (js js' : SailJoltState)
    (q dividendMagnitude divisorMagnitude : BitVec 64)
    (h_v0 : js.vregs v0 = q)
    (h_v1 : js.vregs v1 = dividendMagnitude)
    (h_v2 : js.vregs v2 = divisorMagnitude)
    (hrun : (JoltISA.execProgram phase_product).run js =
      .ok RETIRE_SUCCESS js') :
    q.toNat * divisorMagnitude.toNat < 2^64 ∧
    (q * divisorMagnitude).toNat ≤ dividendMagnitude.toNat ∧
    js'.vregs v0 = q ∧
    js'.vregs v1 = dividendMagnitude ∧
    js'.vregs v2 = divisorMagnitude ∧
    js'.vregs v3 = q * divisorMagnitude ∧
    js'.sail = js.sail := by
  unfold phase_product at hrun
  obtain ⟨s1, h1, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  have hguard1 : (js.vregs v0).toNat * (js.vregs v2).toNat < 2^64 := by
    by_contra hbad
    have herr := JoltISA.virtual_assert_mulu_no_overflow_v_run_err v0 v2 js hbad
    rw [herr] at h1
    cases h1
  have h1' := JoltISA.virtual_assert_mulu_no_overflow_v_run_ok v0 v2 js hguard1
  rw [h1'] at h1
  cases h1
  obtain ⟨s2, h2, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s2, h2', hs2_v3, hs2_pres, hs2_sail⟩ :=
    JoltISA.mul_run_vreg_vreg_vreg_ex v3 v0 v2 js
      (by unfold WritableVReg; decide)
  rw [h2'] at h2
  cases h2
  obtain ⟨s3, h3, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  have hs2_v0 : s2.vregs v0 = q := (hs2_pres v0 (by decide)).trans h_v0
  have hs2_v1 : s2.vregs v1 = dividendMagnitude :=
    (hs2_pres v1 (by decide)).trans h_v1
  have hs2_v2 : s2.vregs v2 = divisorMagnitude :=
    (hs2_pres v2 (by decide)).trans h_v2
  have hs2_v3_value : s2.vregs v3 = q * divisorMagnitude := by
    rw [hs2_v3, h_v0, h_v2]
  have hguard3 : (s2.vregs v3).toNat ≤ (s2.vregs v1).toNat := by
    by_contra hbad
    have herr := JoltISA.virtual_assert_lte_run_err v3 v1 s2 hbad
    rw [herr] at h3
    cases h3
  have h3' := JoltISA.virtual_assert_lte_run_ok v3 v1 s2 hguard3
  rw [h3'] at h3
  cases h3
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  refine ⟨?_, ?_, hs2_v0, hs2_v1, hs2_v2, hs2_v3_value, hs2_sail⟩
  · simpa only [h_v0, h_v2] using hguard1
  · simpa only [hs2_v3_value, hs2_v1] using hguard3

theorem phase_remainder_run
    (js : SailJoltState) (q dividendMagnitude divisorMagnitude : BitVec 64)
    (h_v0 : js.vregs v0 = q)
    (h_v1 : js.vregs v1 = dividendMagnitude)
    (h_v2 : js.vregs v2 = divisorMagnitude)
    (h_v3 : js.vregs v3 = q * divisorMagnitude)
    (hguard : divisorMagnitude = 0#64 ∨
      (dividendMagnitude - q * divisorMagnitude).toNat < divisorMagnitude.toNat) :
    ∃ js',
      (JoltISA.execProgram phase_remainder).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs v3 = dividendMagnitude - q * divisorMagnitude ∧
      js'.sail = js.sail := by
  unfold phase_remainder
  obtain ⟨s1, h1, hs1_v3, hs1_pres, hs1_sail⟩ :=
    JoltISA.sub_run_vreg_vreg_vreg_ex v3 v1 v3 js
      (by unfold WritableVReg; decide)
  have hs1_v2 : s1.vregs v2 = divisorMagnitude :=
    (hs1_pres v2 (by decide)).trans h_v2
  have hs1_v3_value : s1.vregs v3 = dividendMagnitude - q * divisorMagnitude := by
    rw [hs1_v3, h_v1, h_v3]
  have hguard_s1 :
      s1.vregs v2 = 0#64 ∨ (s1.vregs v3).toNat < (s1.vregs v2).toNat := by
    rw [hs1_v2, hs1_v3_value]
    exact hguard
  have h2 := JoltISA.virtual_assert_valid_unsigned_remainder_run_ok
    v3 v2 s1 hguard_s1
  refine ⟨s1, ?_, hs1_v3_value, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

theorem phase_remainder_run_sound
    (js js' : SailJoltState) (q dividendMagnitude divisorMagnitude : BitVec 64)
    (h_v1 : js.vregs v1 = dividendMagnitude)
    (h_v2 : js.vregs v2 = divisorMagnitude)
    (h_v3 : js.vregs v3 = q * divisorMagnitude)
    (hrun : (JoltISA.execProgram phase_remainder).run js =
      .ok RETIRE_SUCCESS js') :
    (divisorMagnitude = 0#64 ∨
      (dividendMagnitude - q * divisorMagnitude).toNat < divisorMagnitude.toNat) ∧
    js'.vregs v3 = dividendMagnitude - q * divisorMagnitude ∧
    js'.sail = js.sail := by
  unfold phase_remainder at hrun
  obtain ⟨s1, h1, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s1, h1', hs1_v3, hs1_pres, hs1_sail⟩ :=
    JoltISA.sub_run_vreg_vreg_vreg_ex v3 v1 v3 js
      (by unfold WritableVReg; decide)
  rw [h1'] at h1
  cases h1
  obtain ⟨s2, h2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  have hs1_v2 : s1.vregs v2 = divisorMagnitude :=
    (hs1_pres v2 (by decide)).trans h_v2
  have hs1_v3_value : s1.vregs v3 = dividendMagnitude - q * divisorMagnitude := by
    rw [hs1_v3, h_v1, h_v3]
  have hguard :
      s1.vregs v2 = 0#64 ∨ (s1.vregs v3).toNat < (s1.vregs v2).toNat := by
    by_contra hbad
    have herr := JoltISA.virtual_assert_valid_unsigned_remainder_run_err
      v3 v2 s1 hbad
    rw [herr] at h2
    cases h2
  have h2' := JoltISA.virtual_assert_valid_unsigned_remainder_run_ok
    v3 v2 s1 hguard
  rw [h2'] at h2
  cases h2
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hguard_value :
      divisorMagnitude = 0#64 ∨
        (dividendMagnitude - q * divisorMagnitude).toNat < divisorMagnitude.toNat := by
    rw [← hs1_v3_value, ← hs1_v2]
    exact hguard
  exact ⟨hguard_value, hs1_v3_value, hs1_sail⟩

theorem phase_writeback_run
    (rs1 rd : regidx) (js : SailJoltState) (reference : SailState)
    (dividend remainder result : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (h_v3 : js.vregs v3 = remainder)
    (hresult : jolt_virtual_negate_if_value dividend remainder = result)
    (h_sail : js.sail = reference) :
    ∃ js',
      (JoltISA.execProgram (phase_writeback rs1 rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite reference rd result := by
  unfold phase_writeback
  obtain ⟨s', hw⟩ := wX_shape rd result js.sail
  have hwrite : wX_bits rd
      (jolt_virtual_negate_if_value dividend (js.vregs v3)) js.sail = .ok () s' := by
    rw [h_v3, hresult]
    exact hw
  have hrun := JoltISA.virtual_negate_if_run_xreg_xreg_vreg
    rd rs1 v3 js dividend hrs1 s' hwrite
  refine ⟨{ js with sail := s' }, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js
      { js with sail := s' } hrun]
    rfl
  · rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd result js.sail s' hw

theorem phase_writeback_run_sound
    (rs1 rd : regidx) (js js' : SailJoltState) (reference : SailState)
    (dividend remainder result : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (h_v3 : js.vregs v3 = remainder)
    (hresult : jolt_virtual_negate_if_value dividend remainder = result)
    (h_sail : js.sail = reference)
    (hrun : (JoltISA.execProgram (phase_writeback rs1 rd)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.sail = stateAfterWrite reference rd result := by
  unfold phase_writeback at hrun
  obtain ⟨s1, h1, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s', hw⟩ := wX_shape rd result js.sail
  have hwrite : wX_bits rd
      (jolt_virtual_negate_if_value dividend (js.vregs v3)) js.sail = .ok () s' := by
    rw [h_v3, hresult]
    exact hw
  have h1' := JoltISA.virtual_negate_if_run_xreg_xreg_vreg
    rd rs1 v3 js dividend hrs1 s' hwrite
  rw [h1'] at h1
  cases h1
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd result js.sail s' hw

end Rem

end
