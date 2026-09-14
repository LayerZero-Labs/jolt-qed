import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.SignedW_math
import JoltBytecode.InstructionEquivalence.ProofSupport.ProgramComposition

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

namespace Divw

abbrev v0 : JoltISA.VReg := JoltISA.inlineTmp0
abbrev v1 : JoltISA.VReg := JoltISA.inlineTmp1
abbrev v2 : JoltISA.VReg := JoltISA.inlineTmp2
abbrev v3 : JoltISA.VReg := JoltISA.inlineTmp3
abbrev v4 : JoltISA.VReg := JoltISA.inlineTmp4
abbrev v5 : JoltISA.VReg := JoltISA.inlineTmp5
abbrev v6 : JoltISA.VReg := JoltISA.inlineTmp6
abbrev v7 : JoltISA.VReg := JoltISA.inlineTmp7

def phase_setup (rs1 rs2 : regidx) (quotient : BitVec 64) : JoltISA.Program :=
  .instr (.VirtualSignExtendWord (.vreg v0) (.xreg rs1)) <|
  .instr (.VirtualSignExtendWord (.vreg v1) (.xreg rs2)) <|
  .instr (.VirtualAdvice (.vreg v2) quotient) <|
  .instr (.VirtualAssertValidDiv0 (.vreg v1) (.vreg v2)) <|
  .done RETIRE_SUCCESS

def phase_magnitudes : JoltISA.Program :=
  .instr (.VirtualNegateIf (.vreg v3) (.vreg v0) (.vreg v0)) <|
  .instr (.VirtualNegateIf (.vreg v4) (.vreg v1) (.vreg v1)) <|
  .done RETIRE_SUCCESS

def phase_quotient_magnitude : JoltISA.Program :=
  .instr (.XOR (.vreg v5) (.vreg v0) (.vreg v1)) <|
  .instr (.VirtualNegateIf (.vreg v6) (.vreg v5) (.vreg v2)) <|
  .done RETIRE_SUCCESS

def phase_product : JoltISA.Program :=
  .instr (.VirtualAssertMulUNoOverflow (.vreg v6) (.vreg v4)) <|
  .instr (.MUL (.vreg v7) (.vreg v6) (.vreg v4)) <|
  .instr (.VirtualAssertLTE (.vreg v7) (.vreg v3)) <|
  .done RETIRE_SUCCESS

def phase_remainder : JoltISA.Program :=
  .instr (.SUB (.vreg v7) (.vreg v3) (.vreg v7)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg v7) (.vreg v4)) <|
  .done RETIRE_SUCCESS

def phase_writeback (rd : regidx) : JoltISA.Program :=
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg v2)) <|
  .done RETIRE_SUCCESS

theorem phase_setup_run
    (rs1 rs2 : regidx) (q dividend divisor : BitVec 64)
    (js : SailJoltState)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard : ¬ (signedWordValue divisor = 0#64 ∧ q ≠ (-1 : BitVec 64))) :
    ∃ js',
      (JoltISA.execProgram (phase_setup rs1 rs2 q)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs v0 = signedWordValue dividend ∧
      js'.vregs v1 = signedWordValue divisor ∧
      js'.vregs v2 = q ∧
      js'.sail = js.sail := by
  unfold phase_setup
  obtain ⟨s1, h1, hs1_v0, hs1_pres, hs1_sail⟩ :=
    JoltISA.virtual_sign_extend_word_run_vreg_xreg_ex
      v0 rs1 js dividend hrs1 (by unfold WritableVReg; decide)
  have hrs2_s1 : rX_bits rs2 s1.sail = .ok divisor s1.sail :=
    hs1_sail.symm ▸ hrs2
  obtain ⟨s2, h2, hs2_v1, hs2_pres, hs2_sail⟩ :=
    JoltISA.virtual_sign_extend_word_run_vreg_xreg_ex
      v1 rs2 s1 divisor hrs2_s1 (by unfold WritableVReg; decide)
  obtain ⟨s3, h3, hs3_v2, hs3_pres, hs3_sail⟩ :=
    JoltISA.virtual_advice_run_ex v2 q s2
      (by unfold WritableVReg; decide)
  have hs3_v0 : s3.vregs v0 = signedWordValue dividend :=
    (hs3_pres v0 (by decide)).trans
      ((hs2_pres v0 (by decide)).trans hs1_v0)
  have hs3_v1 : s3.vregs v1 = signedWordValue divisor :=
    (hs3_pres v1 (by decide)).trans hs2_v1
  have hguard_s3 :
      ¬ (s3.vregs v1 = 0#64 ∧ s3.vregs v2 ≠ (-1 : BitVec 64)) := by
    rw [hs3_v1, hs3_v2]
    exact hguard
  have h4 := JoltISA.virtual_assert_valid_div0_v_run_ok v1 v2 s3 hguard_s3
  refine ⟨s3, ?_, hs3_v0, hs3_v1, hs3_v2,
    hs3_sail.trans (hs2_sail.trans hs1_sail)⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s3 h4]
  rfl

theorem phase_magnitudes_run
    (js : SailJoltState) (q dividend divisor : BitVec 64)
    (h_v0 : js.vregs v0 = dividend)
    (h_v1 : js.vregs v1 = divisor)
    (h_v2 : js.vregs v2 = q) :
    ∃ js',
      (JoltISA.execProgram phase_magnitudes).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs v0 = dividend ∧
      js'.vregs v1 = divisor ∧
      js'.vregs v2 = q ∧
      js'.vregs v3 = bv_abs dividend ∧
      js'.vregs v4 = bv_abs divisor ∧
      js'.sail = js.sail := by
  unfold phase_magnitudes
  obtain ⟨s1, h1, hs1_v3, hs1_pres, hs1_sail⟩ :=
    JoltISA.virtual_negate_if_run_vreg_vreg_vreg_ex v3 v0 v0 js
      (by unfold WritableVReg; decide)
  have hs1_v0 : s1.vregs v0 = dividend :=
    (hs1_pres v0 (by decide)).trans h_v0
  have hs1_v1 : s1.vregs v1 = divisor :=
    (hs1_pres v1 (by decide)).trans h_v1
  have hs1_v2 : s1.vregs v2 = q :=
    (hs1_pres v2 (by decide)).trans h_v2
  have hs1_v3_abs : s1.vregs v3 = bv_abs dividend := by
    rw [hs1_v3, h_v0]
    rfl
  obtain ⟨s2, h2, hs2_v4, hs2_pres, hs2_sail⟩ :=
    JoltISA.virtual_negate_if_run_vreg_vreg_vreg_ex v4 v1 v1 s1
      (by unfold WritableVReg; decide)
  have hs2_v0 : s2.vregs v0 = dividend :=
    (hs2_pres v0 (by decide)).trans hs1_v0
  have hs2_v1 : s2.vregs v1 = divisor :=
    (hs2_pres v1 (by decide)).trans hs1_v1
  have hs2_v2 : s2.vregs v2 = q :=
    (hs2_pres v2 (by decide)).trans hs1_v2
  have hs2_v3 : s2.vregs v3 = bv_abs dividend :=
    (hs2_pres v3 (by decide)).trans hs1_v3_abs
  have hs2_v4_abs : s2.vregs v4 = bv_abs divisor := by
    rw [hs2_v4, hs1_v1]
    rfl
  refine ⟨s2, ?_, hs2_v0, hs2_v1, hs2_v2, hs2_v3, hs2_v4_abs,
    hs2_sail.trans hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rfl

theorem phase_quotient_magnitude_run
    (js : SailJoltState) (q dividend divisor : BitVec 64)
    (h_v0 : js.vregs v0 = dividend)
    (h_v1 : js.vregs v1 = divisor)
    (h_v2 : js.vregs v2 = q)
    (h_v3 : js.vregs v3 = bv_abs dividend)
    (h_v4 : js.vregs v4 = bv_abs divisor) :
    ∃ js',
      (JoltISA.execProgram phase_quotient_magnitude).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs v2 = q ∧
      js'.vregs v3 = bv_abs dividend ∧
      js'.vregs v4 = bv_abs divisor ∧
      js'.vregs v6 = signedQuotientMagnitude dividend divisor q ∧
      js'.sail = js.sail := by
  unfold phase_quotient_magnitude
  obtain ⟨s1, h1, hs1_v5, hs1_pres, hs1_sail⟩ :=
    JoltISA.xor_run_vreg_vreg_vreg_ex v5 v0 v1 js
      (by unfold WritableVReg; decide)
  have hs1_v2 : s1.vregs v2 = q :=
    (hs1_pres v2 (by decide)).trans h_v2
  have hs1_v3 : s1.vregs v3 = bv_abs dividend :=
    (hs1_pres v3 (by decide)).trans h_v3
  have hs1_v4 : s1.vregs v4 = bv_abs divisor :=
    (hs1_pres v4 (by decide)).trans h_v4
  obtain ⟨s2, h2, hs2_v6, hs2_pres, hs2_sail⟩ :=
    JoltISA.virtual_negate_if_run_vreg_vreg_vreg_ex v6 v5 v2 s1
      (by unfold WritableVReg; decide)
  have hs2_v2 : s2.vregs v2 = q :=
    (hs2_pres v2 (by decide)).trans hs1_v2
  have hs2_v3 : s2.vregs v3 = bv_abs dividend :=
    (hs2_pres v3 (by decide)).trans hs1_v3
  have hs2_v4 : s2.vregs v4 = bv_abs divisor :=
    (hs2_pres v4 (by decide)).trans hs1_v4
  have hs2_v6_value :
      s2.vregs v6 = signedQuotientMagnitude dividend divisor q := by
    rw [hs2_v6, hs1_v5, h_v0, h_v1, hs1_v2]
    rfl
  refine ⟨s2, ?_, hs2_v2, hs2_v3, hs2_v4, hs2_v6_value,
    hs2_sail.trans hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rfl

theorem phase_product_run
    (js : SailJoltState)
    (q dividendMagnitude divisorMagnitude qMagnitude : BitVec 64)
    (h_v2 : js.vregs v2 = q)
    (h_v3 : js.vregs v3 = dividendMagnitude)
    (h_v4 : js.vregs v4 = divisorMagnitude)
    (h_v6 : js.vregs v6 = qMagnitude)
    (hoverflow : qMagnitude.toNat * divisorMagnitude.toNat < 2^64)
    (hlte : (qMagnitude * divisorMagnitude).toNat ≤ dividendMagnitude.toNat) :
    ∃ js',
      (JoltISA.execProgram phase_product).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs v2 = q ∧
      js'.vregs v3 = dividendMagnitude ∧
      js'.vregs v4 = divisorMagnitude ∧
      js'.vregs v6 = qMagnitude ∧
      js'.vregs v7 = qMagnitude * divisorMagnitude ∧
      js'.sail = js.sail := by
  unfold phase_product
  have hguard1 : (js.vregs v6).toNat * (js.vregs v4).toNat < 2^64 := by
    rw [h_v6, h_v4]
    exact hoverflow
  have h1 := JoltISA.virtual_assert_mulu_no_overflow_v_run_ok v6 v4 js hguard1
  obtain ⟨s2, h2, hs2_v7, hs2_pres, hs2_sail⟩ :=
    JoltISA.mul_run_vreg_vreg_vreg_ex v7 v6 v4 js
      (by unfold WritableVReg; decide)
  have hs2_v2 : s2.vregs v2 = q := (hs2_pres v2 (by decide)).trans h_v2
  have hs2_v3 : s2.vregs v3 = dividendMagnitude :=
    (hs2_pres v3 (by decide)).trans h_v3
  have hs2_v4 : s2.vregs v4 = divisorMagnitude :=
    (hs2_pres v4 (by decide)).trans h_v4
  have hs2_v6 : s2.vregs v6 = qMagnitude :=
    (hs2_pres v6 (by decide)).trans h_v6
  have hs2_v7_value : s2.vregs v7 = qMagnitude * divisorMagnitude := by
    rw [hs2_v7, h_v6, h_v4]
  have hguard3 : (s2.vregs v7).toNat ≤ (s2.vregs v3).toNat := by
    rw [hs2_v7_value, hs2_v3]
    exact hlte
  have h3 := JoltISA.virtual_assert_lte_run_ok v7 v3 s2 hguard3
  refine ⟨s2, ?_, hs2_v2, hs2_v3, hs2_v4, hs2_v6, hs2_v7_value,
    hs2_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ js s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s2 h3]
  rfl

theorem phase_remainder_run
    (js : SailJoltState) (q dividendMagnitude divisorMagnitude qMagnitude : BitVec 64)
    (h_v2 : js.vregs v2 = q)
    (h_v3 : js.vregs v3 = dividendMagnitude)
    (h_v4 : js.vregs v4 = divisorMagnitude)
    (h_v7 : js.vregs v7 = qMagnitude * divisorMagnitude)
    (hguard : divisorMagnitude = 0#64 ∨
      (dividendMagnitude - qMagnitude * divisorMagnitude).toNat <
        divisorMagnitude.toNat) :
    ∃ js',
      (JoltISA.execProgram phase_remainder).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs v2 = q ∧
      js'.sail = js.sail := by
  unfold phase_remainder
  obtain ⟨s1, h1, hs1_v7, hs1_pres, hs1_sail⟩ :=
    JoltISA.sub_run_vreg_vreg_vreg_ex v7 v3 v7 js
      (by unfold WritableVReg; decide)
  have hs1_v2 : s1.vregs v2 = q := (hs1_pres v2 (by decide)).trans h_v2
  have hs1_v4 : s1.vregs v4 = divisorMagnitude :=
    (hs1_pres v4 (by decide)).trans h_v4
  have hs1_v7_value :
      s1.vregs v7 = dividendMagnitude - qMagnitude * divisorMagnitude := by
    rw [hs1_v7, h_v3, h_v7]
  have hguard_s1 :
      s1.vregs v4 = 0#64 ∨ (s1.vregs v7).toNat < (s1.vregs v4).toNat := by
    rw [hs1_v4, hs1_v7_value]
    exact hguard
  have h2 := JoltISA.virtual_assert_valid_unsigned_remainder_run_ok
    v7 v4 s1 hguard_s1
  refine ⟨s1, ?_, hs1_v2, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

theorem phase_writeback_run
    (rd : regidx) (js : SailJoltState) (reference : SailState)
    (q result : BitVec 64)
    (h_v2 : js.vregs v2 = q)
    (hresult : jolt_virtual_sign_extend_word_value q = result)
    (h_sail : js.sail = reference) :
    ∃ js',
      (JoltISA.execProgram (phase_writeback rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite reference rd result := by
  unfold phase_writeback
  obtain ⟨s', hw⟩ := wX_shape rd result js.sail
  have hwrite : wX_bits rd
      (sign_extend (m := 64) (Sail.BitVec.extractLsb (js.vregs v2) 31 0))
      js.sail = .ok () s' := by
    rw [h_v2, sign_extend_word_eq_jolt_virtual, hresult]
    exact hw
  have hrun := JoltISA.virtual_sign_extend_word_run_xreg_vreg
    rd v2 js s' hwrite
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · rw [JoltISA.execProgram_instr_run_retire _ _ js
      { sail := s', vregs := js.vregs } hrun]
    rfl
  · rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd result js.sail s' hw

theorem phase_setup_run_sound
    (rs1 rs2 : regidx) (q dividend divisor : BitVec 64)
    (js js' : SailJoltState)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrun : (JoltISA.execProgram (phase_setup rs1 rs2 q)).run js =
      .ok RETIRE_SUCCESS js') :
    ¬ (signedWordValue divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) ∧
    js'.vregs v0 = signedWordValue dividend ∧
    js'.vregs v1 = signedWordValue divisor ∧
    js'.vregs v2 = q ∧
    js'.sail = js.sail := by
  unfold phase_setup at hrun
  obtain ⟨s1, h1, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s1, h1', hs1_v0, hs1_pres, hs1_sail⟩ :=
    JoltISA.virtual_sign_extend_word_run_vreg_xreg_ex
      v0 rs1 js dividend hrs1 (by unfold WritableVReg; decide)
  rw [h1'] at h1
  cases h1
  obtain ⟨s2, h2, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  have hrs2_s1 : rX_bits rs2 s1.sail = .ok divisor s1.sail :=
    hs1_sail.symm ▸ hrs2
  obtain ⟨s2, h2', hs2_v1, hs2_pres, hs2_sail⟩ :=
    JoltISA.virtual_sign_extend_word_run_vreg_xreg_ex
      v1 rs2 s1 divisor hrs2_s1 (by unfold WritableVReg; decide)
  rw [h2'] at h2
  cases h2
  obtain ⟨s3, h3, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s3, h3', hs3_v2, hs3_pres, hs3_sail⟩ :=
    JoltISA.virtual_advice_run_ex v2 q s2
      (by unfold WritableVReg; decide)
  rw [h3'] at h3
  cases h3
  obtain ⟨s4, h4, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs3_v0 : s3.vregs v0 = signedWordValue dividend :=
    (hs3_pres v0 (by decide)).trans
      ((hs2_pres v0 (by decide)).trans hs1_v0)
  have hs3_v1 : s3.vregs v1 = signedWordValue divisor :=
    (hs3_pres v1 (by decide)).trans hs2_v1
  by_cases hbad : s3.vregs v1 = 0#64 ∧ s3.vregs v2 ≠ (-1 : BitVec 64)
  · have herr := JoltISA.virtual_assert_valid_div0_v_run_err v1 v2 s3 hbad
    rw [herr] at h4
    cases h4
  · have hok := JoltISA.virtual_assert_valid_div0_v_run_ok v1 v2 s3 hbad
    rw [hok] at h4
    cases h4
    rw [hs3_v1, hs3_v2] at hbad
    exact ⟨hbad, hs3_v0, hs3_v1, hs3_v2,
      hs3_sail.trans (hs2_sail.trans hs1_sail)⟩

theorem phase_magnitudes_run_sound
    (js js' : SailJoltState) (q dividend divisor : BitVec 64)
    (h_v0 : js.vregs v0 = dividend)
    (h_v1 : js.vregs v1 = divisor)
    (h_v2 : js.vregs v2 = q)
    (hrun : (JoltISA.execProgram phase_magnitudes).run js =
      .ok RETIRE_SUCCESS js') :
    js'.vregs v0 = dividend ∧
    js'.vregs v1 = divisor ∧
    js'.vregs v2 = q ∧
    js'.vregs v3 = bv_abs dividend ∧
    js'.vregs v4 = bv_abs divisor ∧
    js'.sail = js.sail := by
  unfold phase_magnitudes at hrun
  obtain ⟨s1, h1, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s1, h1', hs1_v3, hs1_pres, hs1_sail⟩ :=
    JoltISA.virtual_negate_if_run_vreg_vreg_vreg_ex v3 v0 v0 js
      (by unfold WritableVReg; decide)
  rw [h1'] at h1
  cases h1
  obtain ⟨s2, h2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s2, h2', hs2_v4, hs2_pres, hs2_sail⟩ :=
    JoltISA.virtual_negate_if_run_vreg_vreg_vreg_ex v4 v1 v1 s1
      (by unfold WritableVReg; decide)
  rw [h2'] at h2
  cases h2
  have hs1_v0 : s1.vregs v0 = dividend :=
    (hs1_pres v0 (by decide)).trans h_v0
  have hs1_v1 : s1.vregs v1 = divisor :=
    (hs1_pres v1 (by decide)).trans h_v1
  have hs1_v3_abs : s1.vregs v3 = bv_abs dividend := by
    rw [hs1_v3, h_v0]
    rfl
  have hs2_v4_abs : s2.vregs v4 = bv_abs divisor := by
    rw [hs2_v4, hs1_v1]
    rfl
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  exact ⟨
    (hs2_pres v0 (by decide)).trans hs1_v0,
    (hs2_pres v1 (by decide)).trans hs1_v1,
    (hs2_pres v2 (by decide)).trans
      ((hs1_pres v2 (by decide)).trans h_v2),
    (hs2_pres v3 (by decide)).trans hs1_v3_abs,
    hs2_v4_abs,
    hs2_sail.trans hs1_sail⟩

theorem phase_quotient_magnitude_run_sound
    (js js' : SailJoltState) (q dividend divisor : BitVec 64)
    (h_v0 : js.vregs v0 = dividend)
    (h_v1 : js.vregs v1 = divisor)
    (h_v2 : js.vregs v2 = q)
    (h_v3 : js.vregs v3 = bv_abs dividend)
    (h_v4 : js.vregs v4 = bv_abs divisor)
    (hrun : (JoltISA.execProgram phase_quotient_magnitude).run js =
      .ok RETIRE_SUCCESS js') :
    js'.vregs v2 = q ∧
    js'.vregs v3 = bv_abs dividend ∧
    js'.vregs v4 = bv_abs divisor ∧
    js'.vregs v6 = signedQuotientMagnitude dividend divisor q ∧
    js'.sail = js.sail := by
  unfold phase_quotient_magnitude at hrun
  obtain ⟨s1, h1, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s1, h1', hs1_v5, hs1_pres, hs1_sail⟩ :=
    JoltISA.xor_run_vreg_vreg_vreg_ex v5 v0 v1 js
      (by unfold WritableVReg; decide)
  rw [h1'] at h1
  cases h1
  obtain ⟨s2, h2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s2, h2', hs2_v6, hs2_pres, hs2_sail⟩ :=
    JoltISA.virtual_negate_if_run_vreg_vreg_vreg_ex v6 v5 v2 s1
      (by unfold WritableVReg; decide)
  rw [h2'] at h2
  cases h2
  have hs1_v2 : s1.vregs v2 = q :=
    (hs1_pres v2 (by decide)).trans h_v2
  have hs2_v6_value :
      s2.vregs v6 = signedQuotientMagnitude dividend divisor q := by
    rw [hs2_v6, hs1_v5, h_v0, h_v1, hs1_v2]
    rfl
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  exact ⟨
    (hs2_pres v2 (by decide)).trans hs1_v2,
    (hs2_pres v3 (by decide)).trans
      ((hs1_pres v3 (by decide)).trans h_v3),
    (hs2_pres v4 (by decide)).trans
      ((hs1_pres v4 (by decide)).trans h_v4),
    hs2_v6_value,
    hs2_sail.trans hs1_sail⟩

theorem phase_product_run_sound
    (js js' : SailJoltState)
    (q dividendMagnitude divisorMagnitude qMagnitude : BitVec 64)
    (h_v2 : js.vregs v2 = q)
    (h_v3 : js.vregs v3 = dividendMagnitude)
    (h_v4 : js.vregs v4 = divisorMagnitude)
    (h_v6 : js.vregs v6 = qMagnitude)
    (hrun : (JoltISA.execProgram phase_product).run js =
      .ok RETIRE_SUCCESS js') :
    qMagnitude.toNat * divisorMagnitude.toNat < 2^64 ∧
    (qMagnitude * divisorMagnitude).toNat ≤ dividendMagnitude.toNat ∧
    js'.vregs v2 = q ∧
    js'.vregs v3 = dividendMagnitude ∧
    js'.vregs v4 = divisorMagnitude ∧
    js'.vregs v6 = qMagnitude ∧
    js'.vregs v7 = qMagnitude * divisorMagnitude ∧
    js'.sail = js.sail := by
  unfold phase_product at hrun
  obtain ⟨s1, h1, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  have hguard1 : (js.vregs v6).toNat * (js.vregs v4).toNat < 2^64 := by
    by_contra hbad
    have herr := JoltISA.virtual_assert_mulu_no_overflow_v_run_err
      v6 v4 js hbad
    rw [herr] at h1
    cases h1
  have h1' := JoltISA.virtual_assert_mulu_no_overflow_v_run_ok
    v6 v4 js hguard1
  rw [h1'] at h1
  cases h1
  obtain ⟨s2, h2, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s2, h2', hs2_v7, hs2_pres, hs2_sail⟩ :=
    JoltISA.mul_run_vreg_vreg_vreg_ex v7 v6 v4 js
      (by unfold WritableVReg; decide)
  rw [h2'] at h2
  cases h2
  obtain ⟨s3, h3, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  have hs2_v2 : s2.vregs v2 = q := (hs2_pres v2 (by decide)).trans h_v2
  have hs2_v3 : s2.vregs v3 = dividendMagnitude :=
    (hs2_pres v3 (by decide)).trans h_v3
  have hs2_v4 : s2.vregs v4 = divisorMagnitude :=
    (hs2_pres v4 (by decide)).trans h_v4
  have hs2_v6 : s2.vregs v6 = qMagnitude :=
    (hs2_pres v6 (by decide)).trans h_v6
  have hs2_v7_value : s2.vregs v7 = qMagnitude * divisorMagnitude := by
    rw [hs2_v7, h_v6, h_v4]
  have hguard3 : (s2.vregs v7).toNat ≤ (s2.vregs v3).toNat := by
    by_contra hbad
    have herr := JoltISA.virtual_assert_lte_run_err v7 v3 s2 hbad
    rw [herr] at h3
    cases h3
  have h3' := JoltISA.virtual_assert_lte_run_ok v7 v3 s2 hguard3
  rw [h3'] at h3
  cases h3
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  refine ⟨?_, ?_, hs2_v2, hs2_v3, hs2_v4, hs2_v6,
    hs2_v7_value, hs2_sail⟩
  · simpa only [h_v6, h_v4] using hguard1
  · simpa only [hs2_v7_value, hs2_v3] using hguard3

theorem phase_remainder_run_sound
    (js js' : SailJoltState)
    (q dividendMagnitude divisorMagnitude qMagnitude : BitVec 64)
    (h_v2 : js.vregs v2 = q)
    (h_v3 : js.vregs v3 = dividendMagnitude)
    (h_v4 : js.vregs v4 = divisorMagnitude)
    (h_v7 : js.vregs v7 = qMagnitude * divisorMagnitude)
    (hrun : (JoltISA.execProgram phase_remainder).run js =
      .ok RETIRE_SUCCESS js') :
    (divisorMagnitude = 0#64 ∨
      (dividendMagnitude - qMagnitude * divisorMagnitude).toNat <
        divisorMagnitude.toNat) ∧
    js'.vregs v2 = q ∧
    js'.sail = js.sail := by
  unfold phase_remainder at hrun
  obtain ⟨s1, h1, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s1, h1', hs1_v7, hs1_pres, hs1_sail⟩ :=
    JoltISA.sub_run_vreg_vreg_vreg_ex v7 v3 v7 js
      (by unfold WritableVReg; decide)
  rw [h1'] at h1
  cases h1
  obtain ⟨s2, h2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  have hs1_v2 : s1.vregs v2 = q := (hs1_pres v2 (by decide)).trans h_v2
  have hs1_v4 : s1.vregs v4 = divisorMagnitude :=
    (hs1_pres v4 (by decide)).trans h_v4
  have hs1_v7_value :
      s1.vregs v7 = dividendMagnitude - qMagnitude * divisorMagnitude := by
    rw [hs1_v7, h_v3, h_v7]
  have hguard :
      s1.vregs v4 = 0#64 ∨ (s1.vregs v7).toNat < (s1.vregs v4).toNat := by
    by_contra hbad
    have herr := JoltISA.virtual_assert_valid_unsigned_remainder_run_err
      v7 v4 s1 hbad
    rw [herr] at h2
    cases h2
  have h2' := JoltISA.virtual_assert_valid_unsigned_remainder_run_ok
    v7 v4 s1 hguard
  rw [h2'] at h2
  cases h2
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hguardValue :
      divisorMagnitude = 0#64 ∨
        (dividendMagnitude - qMagnitude * divisorMagnitude).toNat <
          divisorMagnitude.toNat := by
    rw [← hs1_v7_value, ← hs1_v4]
    exact hguard
  exact ⟨hguardValue, hs1_v2, hs1_sail⟩

theorem phase_writeback_run_sound
    (rd : regidx) (js js' : SailJoltState) (reference : SailState)
    (q result : BitVec 64)
    (h_v2 : js.vregs v2 = q)
    (hresult : jolt_virtual_sign_extend_word_value q = result)
    (h_sail : js.sail = reference)
    (hrun : (JoltISA.execProgram (phase_writeback rd)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.sail = stateAfterWrite reference rd result := by
  unfold phase_writeback at hrun
  obtain ⟨s1, h1, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s', hw⟩ := wX_shape rd result js.sail
  have hwrite : wX_bits rd
      (sign_extend (m := 64) (Sail.BitVec.extractLsb (js.vregs v2) 31 0))
      js.sail = .ok () s' := by
    rw [h_v2, sign_extend_word_eq_jolt_virtual, hresult]
    exact hw
  have h1' := JoltISA.virtual_sign_extend_word_run_xreg_vreg
    rd v2 js s' hwrite
  rw [h1'] at h1
  cases h1
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd result js.sail s' hw

end Divw

end
