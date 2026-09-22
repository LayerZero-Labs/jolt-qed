import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Primitives
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.DivuProgramBlocks
import JoltBytecode.InstructionEquivalence.ProofSupport.ProgramComposition

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Program blocks for `remuProgram`

REMU uses one virtual register.  `v0` starts as quotient advice, then is
overwritten by `q * divisor`, then by the computed remainder.
-/

namespace Remu

/-- Rust `v0`: quotient advice, then product, then computed remainder. -/
abbrev v0VReg : JoltISA.VReg := JoltISA.inlineTmp0

/-- One top-level Rust `allocate()` call from an empty instruction-local live
set produces REMU's `v0` guard. -/
theorem allocate_layout :
    JoltISA.allocateInstructionRegister [] = some (v0VReg, [0]) := by
  decide

def phase_setup (quotient : BitVec 64) : JoltISA.Program :=
  .instr (.VirtualAdvice (.vreg v0VReg) quotient) <|
  .done RETIRE_SUCCESS

def phase_overflow_check (rs2 : regidx) : JoltISA.Program :=
  .instr (.VirtualAssertMulUNoOverflow (.vreg v0VReg) (.xreg rs2)) <|
  .done RETIRE_SUCCESS

def phase_quotient_product (rs1 rs2 : regidx) : JoltISA.Program :=
  .instr (.MUL (.vreg v0VReg) (.vreg v0VReg) (.xreg rs2)) <|
  .instr (.VirtualAssertLTE (.vreg v0VReg) (.xreg rs1)) <|
  .done RETIRE_SUCCESS

def phase_remainder_bound (rs1 rs2 : regidx) : JoltISA.Program :=
  .instr (.SUB (.vreg v0VReg) (.xreg rs1) (.vreg v0VReg)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg v0VReg) (.xreg rs2)) <|
  .done RETIRE_SUCCESS

def phase_writeback (rd : regidx) : JoltISA.Program :=
  .instr (.ADDI (.xreg rd) (.vreg v0VReg) (0 : BitVec 12)) <|
  .done RETIRE_SUCCESS

theorem phase_setup_run
    (q : BitVec 64) (js : SailJoltState) :
    ∃ js',
      (JoltISA.execProgram (phase_setup q)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs v0VReg = q ∧
      js'.sail = js.sail := by
  unfold phase_setup
  obtain ⟨js', hrun, h_v0, _, h_sail⟩ := JoltISA.virtual_advice_run_ex v0VReg q js (by unfold WritableVReg; decide)
  refine ⟨js', ?_, h_v0, h_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js' hrun]
  rfl

theorem phase_overflow_check_run
    (rs2 : regidx) (js : SailJoltState) (q divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs v0VReg = q)
    (hguard_no_overflow : q.toNat * divisor.toNat < 2^64) :
    ∃ js',
      (JoltISA.execProgram (phase_overflow_check rs2)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs v0VReg = q ∧
      js'.sail = js.sail := by
  unfold phase_overflow_check
  have hguard : (js.vregs v0VReg).toNat * divisor.toNat < 2^64 := h_v0 ▸ hguard_no_overflow
  have hrun : (JoltISA.execInstr (.VirtualAssertMulUNoOverflow (.vreg v0VReg) (.xreg rs2))).run js =
      .ok RETIRE_SUCCESS js :=
    vreg_assert_mulu_no_overflow_run_ok v0VReg rs2 js divisor hrs2 hguard
  refine ⟨js, ?_, h_v0, rfl⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js js hrun]
  rfl

theorem phase_quotient_product_run
    (rs1 rs2 : regidx) (js : SailJoltState)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs v0VReg = q)
    (hguard_lte : (q * divisor).toNat ≤ dividend.toNat) :
    ∃ js',
      (JoltISA.execProgram (phase_quotient_product rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs v0VReg = q * divisor ∧
      js'.sail = js.sail := by
  unfold phase_quotient_product
  obtain ⟨s1, h1, hs1_v0, _, hs1_sail⟩ :=
    vreg_MUL_from_real_vs2_run_ex v0VReg v0VReg rs2 js divisor hrs2 (by unfold WritableVReg; decide)
  have hs1_v0_eq : s1.vregs v0VReg = q * divisor := by rw [hs1_v0, h_v0]
  have hrs1_s1 : rX_bits rs1 s1.sail = .ok dividend s1.sail := hs1_sail.symm ▸ hrs1
  have hguard : (s1.vregs v0VReg).toNat ≤ dividend.toNat := by
    rw [hs1_v0_eq]
    exact hguard_lte
  have h2 : (JoltISA.execInstr (.VirtualAssertLTE (.vreg v0VReg) (.xreg rs1))).run s1 =
      .ok RETIRE_SUCCESS s1 :=
    vreg_assert_lte_real_run_ok v0VReg rs1 s1 dividend hrs1_s1 hguard
  refine ⟨s1, ?_, hs1_v0_eq, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

theorem phase_remainder_bound_run
    (rs1 rs2 : regidx) (js : SailJoltState)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs v0VReg = q * divisor)
    (hguard_rem_bound :
      divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat) :
    ∃ js',
      (JoltISA.execProgram (phase_remainder_bound rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs v0VReg = dividend - q * divisor ∧
      js'.sail = js.sail := by
  unfold phase_remainder_bound
  obtain ⟨s1, h1, hs1_v0, _, hs1_sail⟩ :=
    vreg_SUB_from_real_vs1_run_ex v0VReg rs1 v0VReg js dividend hrs1 (by unfold WritableVReg; decide)
  have hs1_v0_eq : s1.vregs v0VReg = dividend - q * divisor := by rw [hs1_v0, h_v0]
  have hrs2_s1 : rX_bits rs2 s1.sail = .ok divisor s1.sail := hs1_sail.symm ▸ hrs2
  have hguard : divisor = 0#64 ∨ (s1.vregs v0VReg).toNat < divisor.toNat := by
    rw [hs1_v0_eq]
    exact hguard_rem_bound
  have h2 : (JoltISA.execInstr (.VirtualAssertValidUnsignedRemainder (.vreg v0VReg) (.xreg rs2))).run s1 =
      .ok RETIRE_SUCCESS s1 :=
    vreg_assert_valid_unsigned_remainder_real_run_ok v0VReg rs2 s1 divisor hrs2_s1 hguard
  refine ⟨s1, ?_, hs1_v0_eq, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (rem : BitVec 64)
    (h_v0 : js.vregs v0VReg = rem)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (JoltISA.execProgram (phase_writeback rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd rem := by
  unfold phase_writeback
  have hrem : js.vregs v0VReg + sign_extend (m := 64) (0 : BitVec 12) = rem := by
    rw [h_v0]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd rem js.sail
  refine ⟨{ js with sail := s' }, ?_, ?_⟩
  · have hrun := JoltISA.addi_run_xreg_vreg rd v0VReg 0 js s' (by rw [hrem]; exact hw)
    rw [JoltISA.execProgram_instr_run_retire _ _ js { js with sail := s' } hrun]
    rfl
  · show s' = stateAfterWrite js_ref rd rem
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd rem js.sail s' hw

theorem phase_setup_run_sound
    (q : BitVec 64)
    (js js₁ : SailJoltState)
    (hp : (JoltISA.execProgram (phase_setup q)).run js =
      .ok RETIRE_SUCCESS js₁) :
    js₁.vregs v0VReg = q ∧
    js₁.sail = js.sail := by
  unfold phase_setup at hp
  obtain ⟨js_afterAdvice, hrun, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  obtain ⟨s₁, hrun_ex, hs1_v0, _, hs1_sail⟩ := JoltISA.virtual_advice_run_ex v0VReg q js (by unfold WritableVReg; decide)
  rw [hrun_ex] at hrun
  cases hrun
  exact ⟨hs1_v0, hs1_sail⟩

theorem phase_overflow_check_run_sound
    (rs2 : regidx)
    (js js₁ : SailJoltState)
    (q divisor : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs v0VReg = q)
    (hp : (JoltISA.execProgram (phase_overflow_check rs2)).run js =
      .ok RETIRE_SUCCESS js₁) :
    q.toNat * divisor.toNat < 2^64 ∧
    js₁.vregs v0VReg = q ∧
    js₁.sail = js.sail := by
  unfold phase_overflow_check at hp
  obtain ⟨js_afterAssert, hrun, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  by_cases hguard : (js.vregs v0VReg).toNat * divisor.toNat < 2^64
  · have hok := vreg_assert_mulu_no_overflow_run_ok v0VReg rs2 js divisor hrs2 hguard
    rw [hok] at hrun
    cases hrun
    exact ⟨h_v0 ▸ hguard, h_v0, rfl⟩
  · exfalso
    have herr := vreg_assert_mulu_no_overflow_run_err v0VReg rs2 js divisor hrs2 hguard
    rw [herr] at hrun
    cases hrun

theorem phase_quotient_product_run_sound
    (rs1 rs2 : regidx)
    (js js₁ : SailJoltState)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs v0VReg = q)
    (hp : (JoltISA.execProgram (phase_quotient_product rs1 rs2)).run js =
      .ok RETIRE_SUCCESS js₁) :
    (q * divisor).toNat ≤ dividend.toNat ∧
    js₁.vregs v0VReg = q * divisor ∧
    js₁.sail = js.sail := by
  unfold phase_quotient_product at hp
  obtain ⟨s₁, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₁, hrun1_ex, hs1_v0, _, hs1_sail⟩ :=
    vreg_MUL_from_real_vs2_run_ex v0VReg v0VReg rs2 js divisor hrs2 (by unfold WritableVReg; decide)
  rw [hrun1_ex] at hrun1
  cases hrun1
  obtain ⟨js_afterAssert, hrun2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs1_v0_eq : s₁.vregs v0VReg = q * divisor := by rw [hs1_v0, h_v0]
  have hrs1_s1 : rX_bits rs1 s₁.sail = .ok dividend s₁.sail := hs1_sail.symm ▸ hrs1
  by_cases hguard : (s₁.vregs v0VReg).toNat ≤ dividend.toNat
  · have hok := vreg_assert_lte_real_run_ok v0VReg rs1 s₁ dividend hrs1_s1 hguard
    rw [hok] at hrun2
    cases hrun2
    exact ⟨hs1_v0_eq ▸ hguard, hs1_v0_eq, hs1_sail⟩
  · exfalso
    have herr := vreg_assert_lte_real_run_err v0VReg rs1 s₁ dividend hrs1_s1 hguard
    rw [herr] at hrun2
    cases hrun2

theorem phase_remainder_bound_run_sound
    (rs1 rs2 : regidx)
    (js js₁ : SailJoltState)
    (q dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (h_v0 : js.vregs v0VReg = q * divisor)
    (hp : (JoltISA.execProgram (phase_remainder_bound rs1 rs2)).run js =
      .ok RETIRE_SUCCESS js₁) :
    (divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat) ∧
    js₁.vregs v0VReg = dividend - q * divisor ∧
    js₁.sail = js.sail := by
  unfold phase_remainder_bound at hp
  obtain ⟨s₁, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  obtain ⟨s₁, hrun1_ex, hs1_v0, _, hs1_sail⟩ :=
    vreg_SUB_from_real_vs1_run_ex v0VReg rs1 v0VReg js dividend hrs1 (by unfold WritableVReg; decide)
  rw [hrun1_ex] at hrun1
  cases hrun1
  obtain ⟨js_afterAssert, hrun2, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hs1_v0_eq : s₁.vregs v0VReg = dividend - q * divisor := by rw [hs1_v0, h_v0]
  have hrs2_s1 : rX_bits rs2 s₁.sail = .ok divisor s₁.sail := hs1_sail.symm ▸ hrs2
  by_cases hguard : divisor = 0#64 ∨ (s₁.vregs v0VReg).toNat < divisor.toNat
  · have hok :=
      vreg_assert_valid_unsigned_remainder_real_run_ok v0VReg rs2 s₁ divisor hrs2_s1 hguard
    rw [hok] at hrun2
    cases hrun2
    refine ⟨?_, hs1_v0_eq, hs1_sail⟩
    rcases hguard with h0 | hlt
    · left
      exact h0
    · right
      rw [← hs1_v0_eq]
      exact hlt
  · exfalso
    have herr :=
      vreg_assert_valid_unsigned_remainder_real_run_err v0VReg rs2 s₁ divisor hrs2_s1 hguard
    rw [herr] at hrun2
    cases hrun2

theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState)
    (rem : BitVec 64)
    (h_v0 : js.vregs v0VReg = rem)
    (h_sail : js.sail = js_ref)
    (hp : (JoltISA.execProgram (phase_writeback rd)).run js =
      .ok RETIRE_SUCCESS js₁) :
    js₁.sail = stateAfterWrite js_ref rd rem := by
  unfold phase_writeback at hp
  obtain ⟨js_afterWrite, hrun, hdone⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ _ _ hp
  simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure] at hdone
  cases hdone
  have hrem : js.vregs v0VReg + sign_extend (m := 64) (0 : BitVec 12) = rem := by
    rw [h_v0]
    have hz : sign_extend (m := 64) (0 : BitVec 12) = 0#64 := by decide
    rw [hz, BitVec.add_zero]
  obtain ⟨s', hw⟩ := wX_shape rd rem js.sail
  have hp_concrete :
      (JoltISA.execInstr (.ADDI (.xreg rd) (.vreg v0VReg) (0 : BitVec 12))).run js =
      .ok RETIRE_SUCCESS { js with sail := s' } :=
    JoltISA.addi_run_xreg_vreg rd v0VReg 0 js s' (by rw [hrem]; exact hw)
  rw [hp_concrete] at hrun
  cases hrun
  show s' = stateAfterWrite js_ref rd rem
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd rem js.sail s' hw

end Remu

end
