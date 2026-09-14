import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.DivwSignedProgramBlocks

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

namespace JoltISA

def divwProgramPhases
    (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  (Divw.phase_setup rs1 rs2 quotient).append <|
  Divw.phase_magnitudes.append <|
  Divw.phase_quotient_magnitude.append <|
  Divw.phase_product.append <|
  Divw.phase_remainder.append <|
  Divw.phase_writeback rd

theorem divwProgramAuto_eq_phases_of_ne_zero
    (rs2 rs1 rd : regidx) (quotient : BitVec 64)
    (hrd : rd ≠ regidx.Regidx 0) :
    divwProgramAuto rd rs1 rs2 quotient =
      divwProgramPhases rs2 rs1 rd quotient := by
  unfold divwProgramAuto
  rw [isX0_eq_false_of_ne_zero hrd]
  rfl

theorem divwProgramAuto_of_zero
    (rs2 rs1 : regidx) (quotient : BitVec 64) :
    divwProgramAuto (regidx.Regidx 0) rs1 rs2 quotient =
      pureWritebackRdZeroProgram := by
  rfl

theorem divwProgram_concrete
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ js',
      (execProgram (divwProgramAuto rd rs1 rs2
        (divw_advice_value dividend divisor))).run js =
          .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sail_divw_value dividend divisor false) := by
  let dividendWord := signedWordValue dividend
  let divisorWord := signedWordValue divisor
  let q := sail_div_value dividendWord divisorWord false
  let qMagnitude := signedQuotientMagnitude dividendWord divisorWord q
  have hadvice : divw_advice_value dividend divisor = q := by
    unfold q dividendWord divisorWord
    exact divw_advice_value_eq_sail_div_signed_words dividend divisor
  have hresult :
      jolt_virtual_sign_extend_word_value q =
        sail_divw_value dividend divisor false := by
    rw [← hadvice]
    exact sign_extend_divw_advice_value dividend divisor
  have hdiv0 := hguard_div0_of_honest_signed dividendWord divisorWord
  have hoverflow := hguard_no_overflow_of_honest_signed dividendWord divisorWord
  have hlte := hguard_product_lte_of_honest_signed dividendWord divisorWord
  have hremainder := hguard_remainder_bound_of_honest_signed
    dividendWord divisorWord

  obtain ⟨js1, hrun1, h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Divw.phase_setup_run rs1 rs2 q dividend divisor js hrs1 hrs2 hdiv0
  obtain ⟨js2, hrun2, h2_v0, h2_v1, h2_v2, h2_v3, h2_v4, h2_sail⟩ :=
    Divw.phase_magnitudes_run js1 q dividendWord divisorWord
      h1_v0 h1_v1 h1_v2
  obtain ⟨js3, hrun3, h3_v2, h3_v3, h3_v4, h3_v6, h3_sail⟩ :=
    Divw.phase_quotient_magnitude_run js2 q dividendWord divisorWord
      h2_v0 h2_v1 h2_v2 h2_v3 h2_v4
  obtain ⟨js4, hrun4, h4_v2, h4_v3, h4_v4, h4_v6, h4_v7, h4_sail⟩ :=
    Divw.phase_product_run js3 q (bv_abs dividendWord) (bv_abs divisorWord)
      qMagnitude h3_v2 h3_v3 h3_v4 h3_v6 hoverflow hlte
  obtain ⟨js5, hrun5, h5_v2, h5_sail⟩ :=
    Divw.phase_remainder_run js4 q (bv_abs dividendWord) (bv_abs divisorWord)
      qMagnitude h4_v2 h4_v3 h4_v4 h4_v7 hremainder

  have h5_sail_initial : js5.sail = js.sail :=
    h5_sail.trans (h4_sail.trans
      (h3_sail.trans (h2_sail.trans h1_sail)))
  obtain ⟨js6, hrun6, h6_sail⟩ :=
    Divw.phase_writeback_run rd js5 js.sail q
      (sail_divw_value dividend divisor false)
      h5_v2 hresult h5_sail_initial

  have hphases : Program.Run (divwProgramPhases rs2 rs1 rd q) js js6 := by
    unfold divwProgramPhases
    exact Program.Run.append hrun1 <|
      Program.Run.append hrun2 <|
      Program.Run.append hrun3 <|
      Program.Run.append hrun4 <|
      Program.Run.append hrun5 hrun6
  have hprogram : Program.Run (divwProgramAuto rd rs1 rs2 q) js js6 := by
    rw [divwProgramAuto_eq_phases_of_ne_zero rs2 rs1 rd q hrd]
    exact hphases
  rw [hadvice]
  exact ⟨js6, hprogram, h6_sail⟩

theorem divwProgram_sound
    (rs2 rs1 rd : regidx) (q : BitVec 64)
    (js : SailJoltState) (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0)
    (js' : SailJoltState)
    (hrun : (execProgram (divwProgramAuto rd rs1 rs2 q)).run js =
      .ok RETIRE_SUCCESS js') :
    q = divw_advice_value dividend divisor := by
  let dividendWord := signedWordValue dividend
  let divisorWord := signedWordValue divisor
  have hphases : Program.Run (divwProgramPhases rs2 rs1 rd q) js js' := by
    rw [← divwProgramAuto_eq_phases_of_ne_zero rs2 rs1 rd q hrd]
    exact hrun
  unfold divwProgramPhases at hphases
  obtain ⟨js1, hp1, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js2, hp2, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js3, hp3, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js4, hp4, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js5, hp5, _⟩ := Program.Run.append_inv hphases

  obtain ⟨hdiv0, h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Divw.phase_setup_run_sound rs1 rs2 q dividend divisor js js1
      hrs1 hrs2 hp1
  obtain ⟨h2_v0, h2_v1, h2_v2, h2_v3, h2_v4, h2_sail⟩ :=
    Divw.phase_magnitudes_run_sound js1 js2 q dividendWord divisorWord
      h1_v0 h1_v1 h1_v2 hp2
  obtain ⟨h3_v2, h3_v3, h3_v4, h3_v6, _⟩ :=
    Divw.phase_quotient_magnitude_run_sound js2 js3 q
      dividendWord divisorWord h2_v0 h2_v1 h2_v2 h2_v3 h2_v4 hp3
  obtain ⟨hoverflow, hlte, h4_v2, h4_v3, h4_v4, _, h4_v7, _⟩ :=
    Divw.phase_product_run_sound js3 js4 q
      (bv_abs dividendWord) (bv_abs divisorWord)
      (signedQuotientMagnitude dividendWord divisorWord q)
      h3_v2 h3_v3 h3_v4 h3_v6 hp4
  obtain ⟨hremainder, _, _⟩ :=
    Divw.phase_remainder_run_sound js4 js5 q
      (bv_abs dividendWord) (bv_abs divisorWord)
      (signedQuotientMagnitude dividendWord divisorWord q)
      h4_v2 h4_v3 h4_v4 h4_v7 hp5
  have hq : q = sail_div_value dividendWord divisorWord false :=
    signed_quotient_eq_of_guards dividendWord divisorWord q
      hdiv0 hoverflow hlte hremainder
  rw [hq]
  exact (divw_advice_value_eq_sail_div_signed_words dividend divisor).symm

theorem execute_DIVW_signed_factored
    (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIVW rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_divw_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_DIVW, sail_divw_value, bind_pure_comp]

theorem execute_DIVW_signed_reduces
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_DIVW rs2 rs1 rd false).run js.sail =
      .ok RETIRE_SUCCESS
        (stateAfterWrite js.sail rd
          (sail_divw_value dividend divisor false)) := by
  rw [execute_DIVW_signed_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_divw_value dividend divisor false) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

end JoltISA

theorem divwProgram_preserves_projected_vregs
    (rs2 rs1 rd : regidx) (quotient : BitVec 64)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram
      (JoltISA.divwProgramAuto rd rs1 rs2 quotient)).run js = .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.divwProgramAuto rd rs1 rs2 quotient) := by
    unfold JoltISA.divwProgramAuto
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
        JoltISA.inlineTmp6_not_protected,
        JoltISA.inlineTmp7_not_protected,
        JoltISA.inlineTmp7_not_protected⟩
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

def divwProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  quotient = divw_advice_value h.rs1_val h.rs2_val →
    System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.divwProgramAuto rd rs1 rs2 quotient)).run js) =
    (execute_DIVW rs2 rs1 rd false).run js.sail

def divwProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram
        (JoltISA.divwProgramAuto rd rs1 rs2 quotient)).run js =
          .ok RETIRE_SUCCESS js' →
        quotient = divw_advice_value h.rs1_val h.rs2_val

def divwProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  divwProgramCompletenessStatement rs2 rs1 rd quotient js h ∧
  divwProgramSoundnessStatement rs2 rs1 rd quotient js h

theorem divwProgram_eq_sail
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    divwProgramEqSailStatement rs2 rs1 rd quotient js h := by
  unfold divwProgramEqSailStatement divwProgramCompletenessStatement
    divwProgramSoundnessStatement
  constructor
  · intro hquotient
    subst quotient
    let dividend := h.rs1_val
    let divisor := h.rs2_val
    have hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail := h.rs1_read
    have hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail := h.rs2_read
    have h_project_initial : System.systemProject js = js.sail := by
      simpa [project] using
        Projection.systemProject_eq_project_of_compatible js h.linkedCSRs
    by_cases hrd : rd = regidx.Regidx 0
    · subst rd
      rw [JoltISA.divwProgramAuto_of_zero]
      rw [JoltISA.pureWritebackRdZeroProgram_run js]
      simp only [System.systemProjectResult]
      rw [h_project_initial]
      rw [JoltISA.execute_DIVW_signed_factored rs2 rs1 (regidx.Regidx 0) false]
      simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
        hrs1, hrs2, wX_bits_regidx_zero]
    · obtain ⟨js', hjolt, hjolt_sail⟩ :=
        JoltISA.divwProgram_concrete rs2 rs1 rd js dividend divisor
          hrs1 hrs2 hrd
      have h_projected_vregs : Projection.ProjectedVRegsPreserved js js' :=
        divwProgram_preserves_projected_vregs rs2 rs1 rd
          (divw_advice_value dividend divisor) hjolt
      rw [hjolt]
      simp only [System.systemProjectResult]
      rw [JoltISA.execute_DIVW_signed_reduces
        rs2 rs1 rd js dividend divisor hrs1 hrs2]
      congr 1
      rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
        js js' rd (sail_divw_value dividend divisor false)
        hjolt_sail h_projected_vregs]
      rw [h_project_initial]
  · intro hrd js' hrun
    exact JoltISA.divwProgram_sound rs2 rs1 rd quotient js
      h.rs1_val h.rs2_val h.rs1_read h.rs2_read hrd js' hrun

end
