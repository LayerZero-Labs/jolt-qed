import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Primitives
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.DivuwProgramBlocks
import JoltBytecode.InstructionEquivalence.ProofSupport.ProgramComposition

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Program blocks for `remuwProgram`

REMUW follows Rust's `remuw.rs` allocation exactly: `rs1`, `rs2`, and one
`v_tmp`.  The same `v_tmp` register holds quotient advice, then
`quotient * divisor`, then the computed remainder.
-/

namespace Remuw

/-- Rust `rs1 = allocator.allocate()`: zero-extended dividend. -/
abbrev rs1VReg : JoltISA.VReg := JoltISA.inlineTmp0

/-- Rust `rs2 = allocator.allocate()`: zero-extended divisor. -/
abbrev rs2VReg : JoltISA.VReg := JoltISA.inlineTmp1

/-- Rust `v_tmp = allocator.allocate()`: quotient advice, product, remainder. -/
abbrev vTmpVReg : JoltISA.VReg := JoltISA.inlineTmp2

/-- Backwards-compatible name for Rust `v_tmp`. -/
abbrev tempVReg : JoltISA.VReg := vTmpVReg

/-- Three top-level Rust `allocate()` calls from an empty instruction-local
live set produce REMUW's `rs1`, `rs2`, and `v_tmp` guards. -/
theorem allocate_layout :
    JoltISA.allocateInstructionRegister [] = some (rs1VReg, [0]) ∧
    JoltISA.allocateInstructionRegister [0] = some (rs2VReg, [1, 0]) ∧
    JoltISA.allocateInstructionRegister [1, 0] = some (vTmpVReg, [2, 1, 0]) := by
  decide

def phase_setup (rs1 rs2 : regidx) (quotient : BitVec 64) :
    JoltISA.Program :=
  .instr (.VirtualZeroExtendWord (.vreg rs1VReg) (.xreg rs1)) <|
  .instr (.VirtualZeroExtendWord (.vreg rs2VReg) (.xreg rs2)) <|
  .instr (.VirtualAdvice (.vreg vTmpVReg) quotient) <|
  .instr (.VirtualAssertMulUNoOverflow (.vreg vTmpVReg) (.vreg rs2VReg)) <|
  .done RETIRE_SUCCESS

def phase_quotient_product : JoltISA.Program :=
  .instr (.MUL (.vreg vTmpVReg) (.vreg vTmpVReg) (.vreg rs2VReg)) <|
  .instr (.VirtualAssertLTE (.vreg vTmpVReg) (.vreg rs1VReg)) <|
  .done RETIRE_SUCCESS

def phase_remainder_bound : JoltISA.Program :=
  .instr (.SUB (.vreg vTmpVReg) (.vreg rs1VReg) (.vreg vTmpVReg)) <|
  .instr (.VirtualAssertValidUnsignedRemainder (.vreg vTmpVReg) (.vreg rs2VReg)) <|
  .done RETIRE_SUCCESS

def phase_writeback (rd : regidx) : JoltISA.Program :=
  .instr (.VirtualSignExtendWord (.xreg rd) (.vreg vTmpVReg)) <|
  .done RETIRE_SUCCESS

theorem phase_setup_run
    (rs1 rs2 : regidx) (q : BitVec 64) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hguard_no_overflow :
      q.toNat *
        (zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)).toNat
      < 2^64) :
    ∃ js',
      (JoltISA.execProgram (phase_setup rs1 rs2 q)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs rs1VReg = zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
      js'.vregs rs2VReg = zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
      js'.vregs vTmpVReg = q ∧
      js'.sail = js.sail := by
  unfold phase_setup
  obtain ⟨s1, h1, hs1_v0, hs1_pres, hs1_sail⟩ :=
    JoltISA.exists_state_after_virtual_zero_extend_word_run_vreg_xreg
      rs1VReg rs1 js dividend hrs1 (by unfold WritableVReg; decide)
  obtain ⟨s2, h2, hs2_v1, hs2_pres, hs2_sail⟩ :=
    JoltISA.exists_state_after_virtual_zero_extend_word_run_vreg_xreg
      rs2VReg rs2 s1 divisor (hs1_sail.symm ▸ hrs2)
      (by unfold WritableVReg; decide)
  obtain ⟨s3, h3, hs3_v2, hs3_pres, hs3_sail⟩ := JoltISA.virtual_advice_run_ex vTmpVReg q s2 (by unfold WritableVReg; decide)
  have hs3_v0 : s3.vregs rs1VReg = zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) :=
    (hs3_pres rs1VReg (by decide)).trans ((hs2_pres rs1VReg (by decide)).trans hs1_v0)
  have hs3_v1 : s3.vregs rs2VReg = zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) :=
    (hs3_pres rs2VReg (by decide)).trans hs2_v1
  have hguard : (s3.vregs vTmpVReg).toNat * (s3.vregs rs2VReg).toNat < 2^64 := by
    rw [hs3_v2, hs3_v1]
    exact hguard_no_overflow
  have h4 := JoltISA.virtual_assert_mulu_no_overflow_v_run_ok vTmpVReg rs2VReg s3 hguard
  have hs3_sail_orig : s3.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  refine ⟨s3, ?_, hs3_v0, hs3_v1, hs3_v2, hs3_sail_orig⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s2 h2]
  rw [JoltISA.execProgram_instr_run_retire _ _ s2 s3 h3]
  rw [JoltISA.execProgram_instr_run_retire _ _ s3 s3 h4]
  rfl

theorem phase_quotient_product_run
    (js : SailJoltState)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs rs1VReg = zd)
    (h_v1 : js.vregs rs2VReg = zv)
    (h_v2 : js.vregs vTmpVReg = q)
    (hguard_lte : (q * zv).toNat ≤ zd.toNat) :
    ∃ js',
      (JoltISA.execProgram phase_quotient_product).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs rs1VReg = zd ∧
      js'.vregs rs2VReg = zv ∧
      js'.vregs tempVReg = q * zv ∧
      js'.sail = js.sail := by
  unfold phase_quotient_product
  obtain ⟨s1, h1, hs1_v3, hs1_pres, hs1_sail⟩ := JoltISA.mul_run_vreg_vreg_vreg_ex vTmpVReg vTmpVReg rs2VReg js (by unfold WritableVReg; decide)
  have hs1_v0 : s1.vregs rs1VReg = zd := (hs1_pres rs1VReg (by decide)).trans h_v0
  have hs1_v1 : s1.vregs rs2VReg = zv := (hs1_pres rs2VReg (by decide)).trans h_v1
  have hs1_v3_eq : s1.vregs vTmpVReg = q * zv := by rw [hs1_v3, h_v2, h_v1]
  have hguard : (s1.vregs vTmpVReg).toNat ≤ (s1.vregs rs1VReg).toNat := by
    rw [hs1_v3_eq, hs1_v0]
    exact hguard_lte
  have h2 := JoltISA.virtual_assert_lte_run_ok vTmpVReg rs1VReg s1 hguard
  refine ⟨s1, ?_, hs1_v0, hs1_v1, hs1_v3_eq, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

theorem phase_remainder_bound_run
    (js : SailJoltState)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs rs1VReg = zd)
    (h_v1 : js.vregs rs2VReg = zv)
    (h_v3 : js.vregs tempVReg = q * zv)
    (hguard_rem_bound : zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat) :
    ∃ js',
      (JoltISA.execProgram phase_remainder_bound).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs tempVReg = zd - q * zv ∧
      js'.sail = js.sail := by
  unfold phase_remainder_bound
  obtain ⟨s1, h1, hs1_v3, hs1_pres, hs1_sail⟩ := JoltISA.sub_run_vreg_vreg_vreg_ex tempVReg rs1VReg tempVReg js (by unfold WritableVReg; decide)
  have hs1_v1 : s1.vregs rs2VReg = zv := (hs1_pres rs2VReg (by decide)).trans h_v1
  have hs1_v3_eq : s1.vregs tempVReg = zd - q * zv := by rw [hs1_v3, h_v0, h_v3]
  have hguard : s1.vregs rs2VReg = 0#64 ∨ (s1.vregs tempVReg).toNat < (s1.vregs rs2VReg).toNat := by
    rw [hs1_v3_eq, hs1_v1]
    exact hguard_rem_bound
  have h2 := JoltISA.virtual_assert_valid_unsigned_remainder_run_ok tempVReg rs2VReg s1 hguard
  refine ⟨s1, ?_, hs1_v3_eq, hs1_sail⟩
  rw [JoltISA.execProgram_instr_run_retire _ _ js s1 h1]
  rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 h2]
  rfl

theorem phase_writeback_run
    (rd : regidx)
    (js : SailJoltState) (js_ref : SailState)
    (rem : BitVec 64)
    (h_v3 : js.vregs tempVReg = rem)
    (h_sail : js.sail = js_ref) :
    ∃ js',
      (JoltISA.execProgram (phase_writeback rd)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js_ref rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0)) := by
  unfold phase_writeback
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0)) js.sail
  refine ⟨{ sail := s', vregs := js.vregs }, ?_, ?_⟩
  · have h1 : (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.vreg tempVReg))).run js =
        .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
      apply vreg_sign_extend_word_to_real_run rd tempVReg js s'
      rw [h_v3]
      exact hw
    rw [JoltISA.execProgram_instr_run_retire _ _ js { sail := s', vregs := js.vregs } h1]
    rfl
  · show s' = stateAfterWrite js_ref rd
        (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0))
    rw [← h_sail]
    exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

theorem phase_setup_run_sound
    (rs1 rs2 : regidx) (q : BitVec 64)
    (js js₁ : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hp : JoltISA.Program.Run (phase_setup rs1 rs2 q) js js₁) :
    q.toNat *
        (zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)).toNat
      < 2^64 ∧
    js₁.vregs rs1VReg = zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) ∧
    js₁.vregs rs2VReg = zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) ∧
    js₁.vregs vTmpVReg = q ∧
    js₁.sail = js.sail := by
  unfold JoltISA.Program.Run phase_setup at hp
  obtain ⟨s1, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ js js₁ hp
  obtain ⟨s1', hrun1_ex, hs1_v0, hs1_pres, hs1_sail⟩ :=
    JoltISA.exists_state_after_virtual_zero_extend_word_run_vreg_xreg
      rs1VReg rs1 js dividend hrs1 (by unfold WritableVReg; decide)
  rw [hrun1_ex] at hrun1
  cases hrun1
  obtain ⟨s2, hrun2, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ s1 js₁ hp
  obtain ⟨s2', hrun2_ex, hs2_v1, hs2_pres, hs2_sail⟩ :=
    JoltISA.exists_state_after_virtual_zero_extend_word_run_vreg_xreg
      rs2VReg rs2 s1 divisor (hs1_sail.symm ▸ hrs2)
      (by unfold WritableVReg; decide)
  rw [hrun2_ex] at hrun2
  cases hrun2
  obtain ⟨s3, hrun3, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ s2 js₁ hp
  obtain ⟨s3', hrun3_ex, hs3_v2, hs3_pres, hs3_sail⟩ := JoltISA.virtual_advice_run_ex vTmpVReg q s2 (by unfold WritableVReg; decide)
  rw [hrun3_ex] at hrun3
  cases hrun3
  have hs3_v0 : s3.vregs rs1VReg = zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) :=
    (hs3_pres rs1VReg (by decide)).trans ((hs2_pres rs1VReg (by decide)).trans hs1_v0)
  have hs3_v1 : s3.vregs rs2VReg = zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) :=
    (hs3_pres rs2VReg (by decide)).trans hs2_v1
  have hs3_sail_orig : s3.sail = js.sail := hs3_sail.trans (hs2_sail.trans hs1_sail)
  change (JoltISA.execProgram
      (.instr (.VirtualAssertMulUNoOverflow (.vreg vTmpVReg) (.vreg rs2VReg)) (.done RETIRE_SUCCESS))).run s3 =
        .ok RETIRE_SUCCESS js₁ at hp
  by_cases hguard : (s3.vregs vTmpVReg).toNat * (s3.vregs rs2VReg).toNat < 2^64
  · have hok := JoltISA.virtual_assert_mulu_no_overflow_v_run_ok vTmpVReg rs2VReg s3 hguard
    rw [JoltISA.execProgram_instr_run_retire _ _ s3 s3 hok] at hp
    cases hp
    refine ⟨?_, hs3_v0, hs3_v1, hs3_v2, hs3_sail_orig⟩
    rw [hs3_v2, hs3_v1] at hguard
    exact hguard
  · exfalso
    have herr := JoltISA.virtual_assert_mulu_no_overflow_v_run_err vTmpVReg rs2VReg s3 hguard
    rw [JoltISA.execProgram_instr_run_error _ _ s3 s3 _ herr] at hp
    cases hp

theorem phase_quotient_product_run_sound
    (js js₁ : SailJoltState)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs rs1VReg = zd)
    (h_v1 : js.vregs rs2VReg = zv)
    (h_v2 : js.vregs vTmpVReg = q)
    (hp : JoltISA.Program.Run phase_quotient_product js js₁) :
    (q * zv).toNat ≤ zd.toNat ∧
    js₁.vregs rs1VReg = zd ∧
    js₁.vregs rs2VReg = zv ∧
    js₁.vregs tempVReg = q * zv ∧
    js₁.sail = js.sail := by
  unfold JoltISA.Program.Run phase_quotient_product at hp
  obtain ⟨s1, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ js js₁ hp
  obtain ⟨s1', hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ := JoltISA.mul_run_vreg_vreg_vreg_ex vTmpVReg vTmpVReg rs2VReg js (by unfold WritableVReg; decide)
  rw [hrun1_ex] at hrun1
  cases hrun1
  have hs1_v0 : s1.vregs rs1VReg = zd := (hs1_pres rs1VReg (by decide)).trans h_v0
  have hs1_v1 : s1.vregs rs2VReg = zv := (hs1_pres rs2VReg (by decide)).trans h_v1
  have hs1_v3_eq : s1.vregs tempVReg = q * zv := by rw [hs1_v3, h_v2, h_v1]
  change (JoltISA.execProgram
      (.instr (.VirtualAssertLTE (.vreg vTmpVReg) (.vreg rs1VReg)) (.done RETIRE_SUCCESS))).run s1 =
        .ok RETIRE_SUCCESS js₁ at hp
  by_cases hguard : (s1.vregs vTmpVReg).toNat ≤ (s1.vregs rs1VReg).toNat
  · have hok := JoltISA.virtual_assert_lte_run_ok vTmpVReg rs1VReg s1 hguard
    rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 hok] at hp
    cases hp
    refine ⟨?_, hs1_v0, hs1_v1, hs1_v3_eq, hs1_sail⟩
    rw [hs1_v3_eq, hs1_v0] at hguard
    exact hguard
  · exfalso
    have herr := JoltISA.virtual_assert_lte_run_err vTmpVReg rs1VReg s1 hguard
    rw [JoltISA.execProgram_instr_run_error _ _ s1 s1 _ herr] at hp
    cases hp

theorem phase_remainder_bound_run_sound
    (js js₁ : SailJoltState)
    (q zd zv : BitVec 64)
    (h_v0 : js.vregs rs1VReg = zd)
    (h_v1 : js.vregs rs2VReg = zv)
    (h_v3 : js.vregs tempVReg = q * zv)
    (hp : JoltISA.Program.Run phase_remainder_bound js js₁) :
    (zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat) ∧
    js₁.vregs tempVReg = zd - q * zv ∧
    js₁.sail = js.sail := by
  unfold JoltISA.Program.Run phase_remainder_bound at hp
  obtain ⟨s1, hrun1, hp⟩ :=
    JoltISA.execProgram_instr_run_retire_inv _ _ js js₁ hp
  obtain ⟨s1, hrun1_ex, hs1_v3, hs1_pres, hs1_sail⟩ := JoltISA.sub_run_vreg_vreg_vreg_ex tempVReg rs1VReg tempVReg js (by unfold WritableVReg; decide)
  rw [hrun1_ex] at hrun1
  cases hrun1
  have hs1_v1 : s1.vregs rs2VReg = zv := (hs1_pres rs2VReg (by decide)).trans h_v1
  have hs1_v3_eq : s1.vregs tempVReg = zd - q * zv := by rw [hs1_v3, h_v0, h_v3]
  change (JoltISA.execProgram
      (.instr (.VirtualAssertValidUnsignedRemainder (.vreg tempVReg) (.vreg rs2VReg))
        (.done RETIRE_SUCCESS))).run s1 =
        .ok RETIRE_SUCCESS js₁ at hp
  by_cases hguard : s1.vregs rs2VReg = 0#64 ∨ (s1.vregs tempVReg).toNat < (s1.vregs rs2VReg).toNat
  · have hok := JoltISA.virtual_assert_valid_unsigned_remainder_run_ok tempVReg rs2VReg s1 hguard
    rw [JoltISA.execProgram_instr_run_retire _ _ s1 s1 hok] at hp
    cases hp
    refine ⟨?_, hs1_v3_eq, hs1_sail⟩
    rcases hguard with h0 | hlt
    · left
      exact hs1_v1.symm.trans h0
    · right
      rw [hs1_v3_eq, hs1_v1] at hlt
      exact hlt
  · exfalso
    have herr := JoltISA.virtual_assert_valid_unsigned_remainder_run_err tempVReg rs2VReg s1 hguard
    rw [JoltISA.execProgram_instr_run_error _ _ s1 s1 _ herr] at hp
    cases hp

theorem phase_writeback_run_sound
    (rd : regidx)
    (js js₁ : SailJoltState) (js_ref : SailState)
    (rem : BitVec 64)
    (h_v3 : js.vregs tempVReg = rem)
    (h_sail : js.sail = js_ref)
    (hp : JoltISA.Program.Run (phase_writeback rd) js js₁) :
    js₁.sail = stateAfterWrite js_ref rd
      (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0)) := by
  unfold JoltISA.Program.Run phase_writeback at hp
  obtain ⟨s', hw⟩ := wX_shape rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0)) js.sail
  have hrun :
      (JoltISA.execInstr (.VirtualSignExtendWord (.xreg rd) (.vreg tempVReg))).run js =
        .ok RETIRE_SUCCESS
      { sail := s', vregs := js.vregs } :=
    vreg_sign_extend_word_to_real_run rd tempVReg js s' (by rw [h_v3]; exact hw)
  rw [JoltISA.execProgram_instr_run_retire _ _ js { sail := s', vregs := js.vregs } hrun] at hp
  cases hp
  show s' = stateAfterWrite js_ref rd
    (sign_extend (m := 64) (Sail.BitVec.extractLsb rem 31 0))
  rw [← h_sail]
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

end Remuw

end
