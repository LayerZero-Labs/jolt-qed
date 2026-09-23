import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Primitives
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Signed_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.DivuProgramBlocks
import JoltBytecode.InstructionEquivalence.ProofSupport.ProgramComposition

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

namespace Div

abbrev v0 : JoltISA.VReg := JoltISA.inlineTmp0
abbrev v1 : JoltISA.VReg := JoltISA.inlineTmp1
abbrev v2 : JoltISA.VReg := JoltISA.inlineTmp2
abbrev v3 : JoltISA.VReg := JoltISA.inlineTmp3
abbrev v4 : JoltISA.VReg := JoltISA.inlineTmp4
abbrev v5 : JoltISA.VReg := JoltISA.inlineTmp5

def phase_setup (rs2 : regidx) (quotient : BitVec 64) : JoltISA.Program :=
  .instr (.VirtualAdvice (.vreg v0) quotient) <|
  .instr (.VirtualAssertValidDiv0 (.xreg rs2) (.vreg v0)) <|
  .done RETIRE_SUCCESS

def phase_magnitudes (rs1 rs2 : regidx) : JoltISA.Program :=
  .instr (.VirtualNegateIf (.vreg v1) (.xreg rs1) (.xreg rs1)) <|
  .instr (.VirtualNegateIf (.vreg v2) (.xreg rs2) (.xreg rs2)) <|
  .done RETIRE_SUCCESS

def phase_quotient_magnitude (rs1 rs2 : regidx) : JoltISA.Program :=
  .instr (.XOR (.vreg v3) (.xreg rs1) (.xreg rs2)) <|
  .instr (.VirtualNegateIf (.vreg v4) (.vreg v3) (.vreg v0)) <|
  .done RETIRE_SUCCESS

def phase_product : JoltISA.Program :=
  .instr (.VirtualAssertMulUNoOverflow (.vreg v4) (.vreg v2)) <|
  .instr (.MUL (.vreg v5) (.vreg v4) (.vreg v2)) <|
  .instr (.VirtualAssertLTE (.vreg v5) (.vreg v1)) <|
  .done RETIRE_SUCCESS

def phase_remainder : JoltISA.Program :=
  .instr (.SUB (.vreg v5) (.vreg v1) (.vreg v5)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg v5) (.vreg v2)) <|
  .done RETIRE_SUCCESS

def phase_writeback (rd : regidx) : JoltISA.Program :=
  .instr (JoltISA.Encoded.ADDI (.xreg rd) (.vreg v0) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

theorem phase_setup_run
    (rs2 : regidx) (q divisor : BitVec 64) (js : SailJoltState)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64))) :
    ∃ js',
      (JoltISA.execProgram (phase_setup rs2 q)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs v0 = q ∧ js'.sail = js.sail := by
  unfold phase_setup
  obtain ⟨s1, h1, hs1_v0, _, hs1_sail⟩ :=
    JoltISA.virtual_advice_run_ex v0 q js (by unfold WritableVReg; decide)
  have hrs2_s1 : rX_bits rs2 s1.sail = .ok divisor s1.sail :=
    hs1_sail.symm ▸ hrs2
  have hguard_s1 :
      ¬ (divisor = 0#64 ∧ s1.vregs v0 ≠ (-1 : BitVec 64)) := by
    rw [hs1_v0]
    exact hguard
  have h2 := JoltISA.virtual_assert_valid_div0_run_ok
    rs2 v0 s1 divisor hrs2_s1 hguard_s1
  refine ⟨s1, ?_, hs1_v0, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

theorem phase_magnitudes_run
    (rs1 rs2 : regidx) (dividend divisor q : BitVec 64)
    (js : SailJoltState)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs v0 = q) :
    ∃ js',
      (JoltISA.execProgram (phase_magnitudes rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs v0 = q ∧
      js'.vregs v1 = bv_abs dividend ∧
      js'.vregs v2 = bv_abs divisor ∧
      js'.sail = js.sail := by
  unfold phase_magnitudes
  obtain ⟨s1, h1, hs1_v1, hs1_pres, hs1_sail⟩ :=
    JoltISA.virtual_negate_if_run_vreg_xreg_xreg_ex
      v1 rs1 rs1 js dividend dividend hrs1 hrs1
      (by unfold WritableVReg; decide)
  have hs1_v0 : s1.vregs v0 = q := (hs1_pres v0 (by decide)).trans h_v0
  have hs1_v1_abs : s1.vregs v1 = bv_abs dividend := hs1_v1
  have hrs2_s1 : rX_bits rs2 s1.sail = .ok divisor s1.sail :=
    hs1_sail.symm ▸ hrs2
  obtain ⟨s2, h2, hs2_v2, hs2_pres, hs2_sail⟩ :=
    JoltISA.virtual_negate_if_run_vreg_xreg_xreg_ex
      v2 rs2 rs2 s1 divisor divisor hrs2_s1 hrs2_s1
      (by unfold WritableVReg; decide)
  have hs2_v0 : s2.vregs v0 = q :=
    (hs2_pres v0 (by decide)).trans hs1_v0
  have hs2_v1 : s2.vregs v1 = bv_abs dividend :=
    (hs2_pres v1 (by decide)).trans hs1_v1_abs
  have hs2_v2_abs : s2.vregs v2 = bv_abs divisor := hs2_v2
  refine ⟨s2, ?_, hs2_v0, hs2_v1, hs2_v2_abs, hs2_sail.trans hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rfl

theorem phase_quotient_magnitude_run
    (rs1 rs2 : regidx) (dividend divisor q : BitVec 64)
    (js : SailJoltState)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs v0 = q)
    (h_v1 : js.vregs v1 = bv_abs dividend)
    (h_v2 : js.vregs v2 = bv_abs divisor) :
    ∃ js',
      (JoltISA.execProgram (phase_quotient_magnitude rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs v0 = q ∧
      js'.vregs v1 = bv_abs dividend ∧
      js'.vregs v2 = bv_abs divisor ∧
      js'.vregs v4 = signedQuotientMagnitude dividend divisor q ∧
      js'.sail = js.sail := by
  unfold phase_quotient_magnitude
  obtain ⟨s1, h1, hs1_v3, hs1_pres, hs1_sail⟩ :=
    JoltISA.xor_run_vreg_xreg_xreg_ex v3 rs1 rs2 js dividend divisor
      hrs1 hrs2 (by unfold WritableVReg; decide)
  have hs1_v0 : s1.vregs v0 = q := (hs1_pres v0 (by decide)).trans h_v0
  have hs1_v1 : s1.vregs v1 = bv_abs dividend :=
    (hs1_pres v1 (by decide)).trans h_v1
  have hs1_v2 : s1.vregs v2 = bv_abs divisor :=
    (hs1_pres v2 (by decide)).trans h_v2
  obtain ⟨s2, h2, hs2_v4, hs2_pres, hs2_sail⟩ :=
    JoltISA.virtual_negate_if_run_vreg_vreg_vreg_ex v4 v3 v0 s1
      (by unfold WritableVReg; decide)
  have hs2_v0 : s2.vregs v0 = q :=
    (hs2_pres v0 (by decide)).trans hs1_v0
  have hs2_v1 : s2.vregs v1 = bv_abs dividend :=
    (hs2_pres v1 (by decide)).trans hs1_v1
  have hs2_v2 : s2.vregs v2 = bv_abs divisor :=
    (hs2_pres v2 (by decide)).trans hs1_v2
  have hs2_v4_value :
      s2.vregs v4 = signedQuotientMagnitude dividend divisor q := by
    rw [hs2_v4, hs1_v3, hs1_v0]
    rfl
  refine ⟨s2, ?_, hs2_v0, hs2_v1, hs2_v2, hs2_v4_value,
    hs2_sail.trans hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rfl

theorem phase_product_run
    (js : SailJoltState)
    (q dividendMagnitude divisorMagnitude qMagnitude : BitVec 64)
    (h_v0 : js.vregs v0 = q)
    (h_v1 : js.vregs v1 = dividendMagnitude)
    (h_v2 : js.vregs v2 = divisorMagnitude)
    (h_v4 : js.vregs v4 = qMagnitude)
    (hoverflow : qMagnitude.toNat * divisorMagnitude.toNat < 2^64)
    (hlte : (qMagnitude * divisorMagnitude).toNat ≤ dividendMagnitude.toNat) :
    ∃ js',
      (JoltISA.execProgram phase_product).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs v0 = q ∧
      js'.vregs v1 = dividendMagnitude ∧
      js'.vregs v2 = divisorMagnitude ∧
      js'.vregs v4 = qMagnitude ∧
      js'.vregs v5 = qMagnitude * divisorMagnitude ∧
      js'.sail = js.sail := by
  unfold phase_product
  have hguard1 : (js.vregs v4).toNat * (js.vregs v2).toNat < 2^64 := by
    rw [h_v4, h_v2]
    exact hoverflow
  have h1 := JoltISA.virtual_assert_mulu_no_overflow_v_run_ok v4 v2 js hguard1
  obtain ⟨s2, h2, hs2_v5, hs2_pres, hs2_sail⟩ :=
    JoltISA.mul_run_vreg_vreg_vreg_ex v5 v4 v2 js
      (by unfold WritableVReg; decide)
  have hs2_v0 : s2.vregs v0 = q := (hs2_pres v0 (by decide)).trans h_v0
  have hs2_v1 : s2.vregs v1 = dividendMagnitude :=
    (hs2_pres v1 (by decide)).trans h_v1
  have hs2_v2 : s2.vregs v2 = divisorMagnitude :=
    (hs2_pres v2 (by decide)).trans h_v2
  have hs2_v4 : s2.vregs v4 = qMagnitude :=
    (hs2_pres v4 (by decide)).trans h_v4
  have hs2_v5_value : s2.vregs v5 = qMagnitude * divisorMagnitude := by
    rw [hs2_v5, h_v4, h_v2]
  have hguard3 : (s2.vregs v5).toNat ≤ (s2.vregs v1).toNat := by
    rw [hs2_v5_value, hs2_v1]
    exact hlte
  have h3 := JoltISA.virtual_assert_lte_run_ok v5 v1 s2 hguard3
  refine ⟨s2, ?_, hs2_v0, hs2_v1, hs2_v2, hs2_v4, hs2_v5_value,
    hs2_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ js s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s2 h3]
  rfl

theorem phase_remainder_run
    (js : SailJoltState) (q dividendMagnitude divisorMagnitude qMagnitude : BitVec 64)
    (h_v0 : js.vregs v0 = q)
    (h_v1 : js.vregs v1 = dividendMagnitude)
    (h_v2 : js.vregs v2 = divisorMagnitude)
    (h_v4 : js.vregs v4 = qMagnitude)
    (h_v5 : js.vregs v5 = qMagnitude * divisorMagnitude)
    (hguard : divisorMagnitude = 0#64 ∨
      (dividendMagnitude - qMagnitude * divisorMagnitude).toNat <
        divisorMagnitude.toNat) :
    ∃ js',
      (JoltISA.execProgram phase_remainder).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs v0 = q ∧
      js'.vregs v5 = dividendMagnitude - qMagnitude * divisorMagnitude ∧
      js'.sail = js.sail := by
  unfold phase_remainder
  obtain ⟨s1, h1, hs1_v5, hs1_pres, hs1_sail⟩ :=
    JoltISA.sub_run_vreg_vreg_vreg_ex v5 v1 v5 js
      (by unfold WritableVReg; decide)
  have hs1_v0 : s1.vregs v0 = q := (hs1_pres v0 (by decide)).trans h_v0
  have hs1_v2 : s1.vregs v2 = divisorMagnitude :=
    (hs1_pres v2 (by decide)).trans h_v2
  have hs1_v5_value :
      s1.vregs v5 = dividendMagnitude - qMagnitude * divisorMagnitude := by
    rw [hs1_v5, h_v1, h_v5]
  have hguard_s1 :
      s1.vregs v2 = 0#64 ∨ (s1.vregs v5).toNat < (s1.vregs v2).toNat := by
    rw [hs1_v2, hs1_v5_value]
    exact hguard
  have h2 := JoltISA.virtual_assert_valid_unsigned_remainder_run_ok
    v5 v2 s1 hguard_s1
  refine ⟨s1, ?_, hs1_v0, hs1_v5_value, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

theorem phase_writeback_run
    (rd : regidx) (js : SailJoltState) (reference : SailState)
    (q : BitVec 64) (h_v0 : js.vregs v0 = q)
    (h_sail : js.sail = reference) :
    ∃ js',
      (JoltISA.execProgram (phase_writeback rd)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite reference rd q := by
  exact Divu.phase_writeback_run rd js reference q h_v0 h_sail

theorem phase_setup_run_sound
    (rs2 : regidx) (q divisor : BitVec 64) (js js' : SailJoltState)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrun : (JoltISA.execProgram (phase_setup rs2 q)).run js =
      .ok RETIRE_SUCCESS js') :
    ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) ∧
    js'.vregs v0 = q ∧ js'.sail = js.sail := by
  unfold phase_setup at hrun
  obtain ⟨s1, h1, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s1, h1', hs1_v0, _, hs1_sail⟩ :=
    JoltISA.virtual_advice_run_ex v0 q js (by unfold WritableVReg; decide)
  rw [h1'] at h1
  cases h1
  obtain ⟨s2, h2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hrs2_s1 : rX_bits rs2 s1.sail = .ok divisor s1.sail :=
    hs1_sail.symm ▸ hrs2
  by_cases hguard : divisor = 0#64 ∧ s1.vregs v0 ≠ (-1 : BitVec 64)
  · have herr := JoltISA.virtual_assert_valid_div0_run_err
      rs2 v0 s1 divisor hrs2_s1 hguard
    rw [herr] at h2
    cases h2
  · have hok := JoltISA.virtual_assert_valid_div0_run_ok
      rs2 v0 s1 divisor hrs2_s1 hguard
    rw [hok] at h2
    cases h2
    rw [hs1_v0] at hguard
    exact ⟨hguard, hs1_v0, hs1_sail⟩

theorem phase_magnitudes_run_sound
    (rs1 rs2 : regidx) (dividend divisor q : BitVec 64)
    (js js' : SailJoltState)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs v0 = q)
    (hrun : (JoltISA.execProgram (phase_magnitudes rs1 rs2)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.vregs v0 = q ∧
    js'.vregs v1 = bv_abs dividend ∧
    js'.vregs v2 = bv_abs divisor ∧
    js'.sail = js.sail := by
  unfold phase_magnitudes at hrun
  obtain ⟨s1, h1, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s1, h1', hs1_v1, hs1_pres, hs1_sail⟩ :=
    JoltISA.virtual_negate_if_run_vreg_xreg_xreg_ex
      v1 rs1 rs1 js dividend dividend hrs1 hrs1
      (by unfold WritableVReg; decide)
  rw [h1'] at h1
  cases h1
  have hrs2_s1 : rX_bits rs2 s1.sail = .ok divisor s1.sail :=
    hs1_sail.symm ▸ hrs2
  obtain ⟨s2, h2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s2, h2', hs2_v2, hs2_pres, hs2_sail⟩ :=
    JoltISA.virtual_negate_if_run_vreg_xreg_xreg_ex
      v2 rs2 rs2 s1 divisor divisor hrs2_s1 hrs2_s1
      (by unfold WritableVReg; decide)
  rw [h2'] at h2
  cases h2
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  exact ⟨
    (hs2_pres v0 (by decide)).trans ((hs1_pres v0 (by decide)).trans h_v0),
    (hs2_pres v1 (by decide)).trans hs1_v1,
    hs2_v2,
    hs2_sail.trans hs1_sail⟩

theorem phase_quotient_magnitude_run_sound
    (rs1 rs2 : regidx) (dividend divisor q : BitVec 64)
    (js js' : SailJoltState)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs v0 = q)
    (h_v1 : js.vregs v1 = bv_abs dividend)
    (h_v2 : js.vregs v2 = bv_abs divisor)
    (hrun : (JoltISA.execProgram (phase_quotient_magnitude rs1 rs2)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.vregs v0 = q ∧
    js'.vregs v1 = bv_abs dividend ∧
    js'.vregs v2 = bv_abs divisor ∧
    js'.vregs v4 = signedQuotientMagnitude dividend divisor q ∧
    js'.sail = js.sail := by
  unfold phase_quotient_magnitude at hrun
  obtain ⟨s1, h1, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s1, h1', hs1_v3, hs1_pres, hs1_sail⟩ :=
    JoltISA.xor_run_vreg_xreg_xreg_ex v3 rs1 rs2 js dividend divisor
      hrs1 hrs2 (by unfold WritableVReg; decide)
  rw [h1'] at h1
  cases h1
  obtain ⟨s2, h2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s2, h2', hs2_v4, hs2_pres, hs2_sail⟩ :=
    JoltISA.virtual_negate_if_run_vreg_vreg_vreg_ex v4 v3 v0 s1
      (by unfold WritableVReg; decide)
  rw [h2'] at h2
  cases h2
  have hs1_v0 : s1.vregs v0 = q := (hs1_pres v0 (by decide)).trans h_v0
  have hs2_v4_value :
      s2.vregs v4 = signedQuotientMagnitude dividend divisor q := by
    rw [hs2_v4, hs1_v3, hs1_v0]
    rfl
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  exact ⟨
    (hs2_pres v0 (by decide)).trans hs1_v0,
    (hs2_pres v1 (by decide)).trans ((hs1_pres v1 (by decide)).trans h_v1),
    (hs2_pres v2 (by decide)).trans ((hs1_pres v2 (by decide)).trans h_v2),
    hs2_v4_value,
    hs2_sail.trans hs1_sail⟩

theorem phase_product_run_sound
    (js js' : SailJoltState)
    (q dividendMagnitude divisorMagnitude qMagnitude : BitVec 64)
    (h_v0 : js.vregs v0 = q)
    (h_v1 : js.vregs v1 = dividendMagnitude)
    (h_v2 : js.vregs v2 = divisorMagnitude)
    (h_v4 : js.vregs v4 = qMagnitude)
    (hrun : (JoltISA.execProgram phase_product).run js =
      .ok RETIRE_SUCCESS js') :
    qMagnitude.toNat * divisorMagnitude.toNat < 2^64 ∧
    (qMagnitude * divisorMagnitude).toNat ≤ dividendMagnitude.toNat ∧
    js'.vregs v0 = q ∧
    js'.vregs v1 = dividendMagnitude ∧
    js'.vregs v2 = divisorMagnitude ∧
    js'.vregs v4 = qMagnitude ∧
    js'.vregs v5 = qMagnitude * divisorMagnitude ∧
    js'.sail = js.sail := by
  unfold phase_product at hrun
  obtain ⟨s1, h1, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  have hguard1 : (js.vregs v4).toNat * (js.vregs v2).toNat < 2^64 := by
    by_contra hbad
    have herr := JoltISA.virtual_assert_mulu_no_overflow_v_run_err
      v4 v2 js hbad
    rw [herr] at h1
    cases h1
  have h1' := JoltISA.virtual_assert_mulu_no_overflow_v_run_ok
    v4 v2 js hguard1
  rw [h1'] at h1
  cases h1
  obtain ⟨s2, h2, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s2, h2', hs2_v5, hs2_pres, hs2_sail⟩ :=
    JoltISA.mul_run_vreg_vreg_vreg_ex v5 v4 v2 js
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
  have hs2_v4 : s2.vregs v4 = qMagnitude :=
    (hs2_pres v4 (by decide)).trans h_v4
  have hs2_v5_value : s2.vregs v5 = qMagnitude * divisorMagnitude := by
    rw [hs2_v5, h_v4, h_v2]
  have hguard3 : (s2.vregs v5).toNat ≤ (s2.vregs v1).toNat := by
    by_contra hbad
    have herr := JoltISA.virtual_assert_lte_run_err v5 v1 s2 hbad
    rw [herr] at h3
    cases h3
  have h3' := JoltISA.virtual_assert_lte_run_ok v5 v1 s2 hguard3
  rw [h3'] at h3
  cases h3
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  refine ⟨?_, ?_, hs2_v0, hs2_v1, hs2_v2, hs2_v4, hs2_v5_value,
    hs2_sail⟩
  · simpa only [h_v4, h_v2] using hguard1
  · simpa only [hs2_v5_value, hs2_v1] using hguard3

theorem phase_remainder_run_sound
    (js js' : SailJoltState)
    (q dividendMagnitude divisorMagnitude qMagnitude : BitVec 64)
    (h_v0 : js.vregs v0 = q)
    (h_v1 : js.vregs v1 = dividendMagnitude)
    (h_v2 : js.vregs v2 = divisorMagnitude)
    (h_v5 : js.vregs v5 = qMagnitude * divisorMagnitude)
    (hrun : (JoltISA.execProgram phase_remainder).run js =
      .ok RETIRE_SUCCESS js') :
    (divisorMagnitude = 0#64 ∨
      (dividendMagnitude - qMagnitude * divisorMagnitude).toNat <
        divisorMagnitude.toNat) ∧
    js'.vregs v0 = q ∧
    js'.vregs v5 = dividendMagnitude - qMagnitude * divisorMagnitude ∧
    js'.sail = js.sail := by
  unfold phase_remainder at hrun
  obtain ⟨s1, h1, hrun⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  obtain ⟨s1, h1', hs1_v5, hs1_pres, hs1_sail⟩ :=
    JoltISA.sub_run_vreg_vreg_vreg_ex v5 v1 v5 js
      (by unfold WritableVReg; decide)
  rw [h1'] at h1
  cases h1
  obtain ⟨s2, h2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hrun
  have hs1_v0 : s1.vregs v0 = q := (hs1_pres v0 (by decide)).trans h_v0
  have hs1_v2 : s1.vregs v2 = divisorMagnitude :=
    (hs1_pres v2 (by decide)).trans h_v2
  have hs1_v5_value :
      s1.vregs v5 = dividendMagnitude - qMagnitude * divisorMagnitude := by
    rw [hs1_v5, h_v1, h_v5]
  have hguard :
      s1.vregs v2 = 0#64 ∨ (s1.vregs v5).toNat < (s1.vregs v2).toNat := by
    by_contra hbad
    have herr := JoltISA.virtual_assert_valid_unsigned_remainder_run_err
      v5 v2 s1 hbad
    rw [herr] at h2
    cases h2
  have h2' := JoltISA.virtual_assert_valid_unsigned_remainder_run_ok
    v5 v2 s1 hguard
  rw [h2'] at h2
  cases h2
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hguard_value :
      divisorMagnitude = 0#64 ∨
        (dividendMagnitude - qMagnitude * divisorMagnitude).toNat <
          divisorMagnitude.toNat := by
    rw [← hs1_v5_value, ← hs1_v2]
    exact hguard
  exact ⟨hguard_value, hs1_v0, hs1_v5_value, hs1_sail⟩

end Div

end
