import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.RemwSignedProgramBlocks

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

namespace JoltISA

def remwProgramPhases
    (rs2 rs1 rd : regidx) (quotientMagnitude : BitVec 64) : Program :=
  (Remw.phase_setup rs1 rs2 quotientMagnitude).append <|
  Divw.phase_magnitudes.append <|
  Remw.phase_product.append <|
  Remw.phase_remainder.append <|
  Remw.phase_writeback rd

theorem remwProgramAuto_eq_phases_of_ne_zero
    (rs2 rs1 rd : regidx) (quotientMagnitude : BitVec 64)
    (hrd : rd ≠ regidx.Regidx 0) :
    remwProgramAuto rd rs1 rs2 quotientMagnitude =
      remwProgramPhases rs2 rs1 rd quotientMagnitude := by
  unfold remwProgramAuto
  rw [isX0_eq_false_of_ne_zero hrd]
  rfl

theorem remwProgramAuto_of_zero
    (rs2 rs1 : regidx) (quotientMagnitude : BitVec 64) :
    remwProgramAuto (regidx.Regidx 0) rs1 rs2 quotientMagnitude =
      pureWritebackRdZeroProgram := by
  rfl

theorem remwProgram_concrete
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ js',
      (execProgram (remwProgramAuto rd rs1 rs2
        (remw_advice_value dividend divisor))).run js =
          .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sail_remw_value dividend divisor false) := by
  let dividendWord := signedWordValue dividend
  let divisorWord := signedWordValue divisor
  let q := remw_advice_value dividend divisor
  let rem := bv_abs dividendWord - q * bv_abs divisorWord
  have hadvice : q = rem_advice_value dividendWord divisorWord := by
    unfold q dividendWord divisorWord
    exact remw_advice_value_eq_rem_signed_words dividend divisor
  have hoverflow : q.toNat * (bv_abs divisorWord).toNat < 2^64 := by
    rw [hadvice]
    exact hguard_no_overflow_of_honest_rem dividendWord divisorWord
  have hlte : (q * bv_abs divisorWord).toNat ≤ (bv_abs dividendWord).toNat := by
    rw [hadvice]
    exact hguard_product_lte_of_honest_rem dividendWord divisorWord
  have hremainder :
      bv_abs divisorWord = 0#64 ∨
        (bv_abs dividendWord - q * bv_abs divisorWord).toNat <
          (bv_abs divisorWord).toNat := by
    rw [hadvice]
    exact hguard_remainder_bound_of_honest_rem dividendWord divisorWord
  have hresult :
      jolt_virtual_negate_if_value dividendWord rem =
        sail_remw_value dividend divisor false := by
    have hcore := signed_remainder_eq_of_guards dividendWord divisorWord q
      hoverflow hlte hremainder
    unfold rem
    exact hcore.trans
      (sail_remw_value_eq_sail_rem_signed_words dividend divisor).symm

  obtain ⟨js1, hrun1, h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Remw.phase_setup_run rs1 rs2 q dividend divisor js hrs1 hrs2
  obtain ⟨js2, hrun2, h2_v0, h2_v1, h2_v2, h2_v3, h2_v4, h2_sail⟩ :=
    Divw.phase_magnitudes_run js1 q dividendWord divisorWord
      h1_v0 h1_v1 h1_v2
  obtain ⟨js3, hrun3, h3_v0, h3_v2, h3_v3, h3_v4, h3_v5, h3_sail⟩ :=
    Remw.phase_product_run js2 q (bv_abs dividendWord) (bv_abs divisorWord)
      dividendWord h2_v0 h2_v2 h2_v3 h2_v4 hoverflow hlte
  obtain ⟨js4, hrun4, h4_v0, h4_v5, h4_sail⟩ :=
    Remw.phase_remainder_run js3 q (bv_abs dividendWord)
      (bv_abs divisorWord) dividendWord
      h3_v0 h3_v2 h3_v3 h3_v4 h3_v5 hremainder

  have h4_sail_initial : js4.sail = js.sail :=
    h4_sail.trans (h3_sail.trans (h2_sail.trans h1_sail))
  obtain ⟨js5, hrun5, h5_sail⟩ :=
    Remw.phase_writeback_run rd js4 js.sail dividendWord rem
      (sail_remw_value dividend divisor false)
      h4_v0 h4_v5 hresult h4_sail_initial

  have hphases : Program.Run (remwProgramPhases rs2 rs1 rd q) js js5 := by
    unfold remwProgramPhases
    exact Program.Run.append hrun1 <|
      Program.Run.append hrun2 <|
      Program.Run.append hrun3 <|
      Program.Run.append hrun4 hrun5
  have hprogram : Program.Run (remwProgramAuto rd rs1 rs2 q) js js5 := by
    rw [remwProgramAuto_eq_phases_of_ne_zero rs2 rs1 rd q hrd]
    exact hphases
  exact ⟨js5, hprogram, h5_sail⟩

theorem remwProgram_sound
    (rs2 rs1 rd : regidx) (q : BitVec 64)
    (js : SailJoltState) (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0)
    (js' : SailJoltState)
    (hrun : (execProgram (remwProgramAuto rd rs1 rs2 q)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.sail = stateAfterWrite js.sail rd
      (sail_remw_value dividend divisor false) := by
  let dividendWord := signedWordValue dividend
  let divisorWord := signedWordValue divisor
  have hphases : Program.Run (remwProgramPhases rs2 rs1 rd q) js js' := by
    rw [← remwProgramAuto_eq_phases_of_ne_zero rs2 rs1 rd q hrd]
    exact hrun
  unfold remwProgramPhases at hphases
  obtain ⟨js1, hp1, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js2, hp2, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js3, hp3, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js4, hp4, hp5⟩ := Program.Run.append_inv hphases

  obtain ⟨h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Remw.phase_setup_run_sound rs1 rs2 q dividend divisor js js1
      hrs1 hrs2 hp1
  obtain ⟨h2_v0, h2_v1, h2_v2, h2_v3, h2_v4, h2_sail⟩ :=
    Divw.phase_magnitudes_run_sound js1 js2 q dividendWord divisorWord
      h1_v0 h1_v1 h1_v2 hp2
  obtain ⟨hoverflow, hlte, h3_v0, h3_v2, h3_v3, h3_v4, h3_v5, h3_sail⟩ :=
    Remw.phase_product_run_sound js2 js3 q
      (bv_abs dividendWord) (bv_abs divisorWord) dividendWord
      h2_v0 h2_v2 h2_v3 h2_v4 hp3
  obtain ⟨hremainder, h4_v0, h4_v5, h4_sail⟩ :=
    Remw.phase_remainder_run_sound js3 js4 q
      (bv_abs dividendWord) (bv_abs divisorWord) dividendWord
      h3_v0 h3_v3 h3_v4 h3_v5 hp4

  let rem := bv_abs dividendWord - q * bv_abs divisorWord
  have hresult :
      jolt_virtual_negate_if_value dividendWord rem =
        sail_remw_value dividend divisor false := by
    have hcore := signed_remainder_eq_of_guards dividendWord divisorWord q
      hoverflow hlte hremainder
    unfold rem
    exact hcore.trans
      (sail_remw_value_eq_sail_rem_signed_words dividend divisor).symm
  have h4_sail_initial : js4.sail = js.sail :=
    h4_sail.trans (h3_sail.trans (h2_sail.trans h1_sail))
  exact Remw.phase_writeback_run_sound rd js4 js' js.sail
    dividendWord rem (sail_remw_value dividend divisor false)
    h4_v0 h4_v5 hresult h4_sail_initial hp5

theorem execute_REMW_signed_factored
    (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_REMW rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_remw_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_REMW, sail_remw_value, bind_pure_comp]

theorem execute_REMW_signed_reduces
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_REMW rs2 rs1 rd false).run js.sail =
      .ok RETIRE_SUCCESS
        (stateAfterWrite js.sail rd
          (sail_remw_value dividend divisor false)) := by
  rw [execute_REMW_signed_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_remw_value dividend divisor false) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

end JoltISA

theorem remwProgram_preserves_projected_vregs
    (rs2 rs1 rd : regidx) (quotientMagnitude : BitVec 64)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram
      (JoltISA.remwProgramAuto rd rs1 rs2 quotientMagnitude)).run js =
        .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.remwProgramAuto rd rs1 rs2 quotientMagnitude) := by
    unfold JoltISA.remwProgramAuto
    split
    · exact JoltISA.pureWritebackRdZeroProgram_writesNoProtected
    · simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg,
        JoltISA.DstWritesNoProtectedVReg,
        JoltISA.VRegWritesNoProtectedVReg, true_and, and_true]
      exact ⟨JoltISA.inlineTmp0_not_protected,
        JoltISA.inlineTmp1_not_protected,
        JoltISA.inlineTmp2_not_protected,
        JoltISA.inlineTmp3_not_protected,
        JoltISA.inlineTmp4_not_protected,
        JoltISA.inlineTmp5_not_protected,
        JoltISA.inlineTmp5_not_protected⟩
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

def remwProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  quotientMagnitude = remw_advice_value h.rs1_val h.rs2_val →
    System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.remwProgramAuto rd rs1 rs2 quotientMagnitude)).run js) =
    (execute_REMW rs2 rs1 rd false).run js.sail

def remwProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram
        (JoltISA.remwProgramAuto rd rs1 rs2 quotientMagnitude)).run js =
          .ok RETIRE_SUCCESS js' →
        js'.sail = stateAfterWrite js.sail rd
          (sail_remw_value h.rs1_val h.rs2_val false)

def remwProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  remwProgramCompletenessStatement rs2 rs1 rd quotientMagnitude js h ∧
  remwProgramSoundnessStatement rs2 rs1 rd quotientMagnitude js h

theorem remwProgram_eq_sail
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    remwProgramEqSailStatement rs2 rs1 rd quotientMagnitude js h := by
  unfold remwProgramEqSailStatement remwProgramCompletenessStatement
    remwProgramSoundnessStatement
  constructor
  · intro hquotient
    subst quotientMagnitude
    let dividend := h.rs1_val
    let divisor := h.rs2_val
    have hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail := h.rs1_read
    have hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail := h.rs2_read
    have h_project_initial : System.systemProject js = js.sail := by
      simpa [project] using
        Projection.systemProject_eq_project_of_compatible js h.linkedCSRs
    by_cases hrd : rd = regidx.Regidx 0
    · subst rd
      rw [JoltISA.remwProgramAuto_of_zero]
      rw [JoltISA.pureWritebackRdZeroProgram_run js]
      simp only [System.systemProjectResult]
      rw [h_project_initial]
      rw [JoltISA.execute_REMW_signed_factored rs2 rs1 (regidx.Regidx 0) false]
      simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
        hrs1, hrs2, wX_bits_regidx_zero]
    · obtain ⟨js', hjolt, hjolt_sail⟩ :=
        JoltISA.remwProgram_concrete rs2 rs1 rd js dividend divisor
          hrs1 hrs2 hrd
      have h_projected_vregs : Projection.ProjectedVRegsPreserved js js' :=
        remwProgram_preserves_projected_vregs rs2 rs1 rd
          (remw_advice_value dividend divisor) hjolt
      rw [hjolt]
      simp only [System.systemProjectResult]
      rw [JoltISA.execute_REMW_signed_reduces
        rs2 rs1 rd js dividend divisor hrs1 hrs2]
      congr 1
      rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
        js js' rd (sail_remw_value dividend divisor false)
        hjolt_sail h_projected_vregs]
      rw [h_project_initial]
  · intro hrd js' hrun
    exact JoltISA.remwProgram_sound rs2 rs1 rd quotientMagnitude js
      h.rs1_val h.rs2_val h.rs1_read h.rs2_read hrd js' hrun

end
