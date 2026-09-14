import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.DivProgramBlocks

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

namespace JoltISA

/-- Proof-facing decomposition of the current one-advice Rust `DIV` rows. -/
def divProgramPhases
    (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  (Div.phase_setup rs2 quotient).append <|
  (Div.phase_magnitudes rs1 rs2).append <|
  (Div.phase_quotient_magnitude rs1 rs2).append <|
  Div.phase_product.append <|
  Div.phase_remainder.append <|
  Div.phase_writeback rd

theorem divProgramAuto_eq_phases_of_ne_zero
    (rs2 rs1 rd : regidx) (quotient : BitVec 64)
    (hrd : rd ≠ regidx.Regidx 0) :
    divProgramAuto rd rs1 rs2 quotient =
      divProgramPhases rs2 rs1 rd quotient := by
  unfold divProgramAuto
  rw [isX0_eq_false_of_ne_zero hrd]
  rfl

theorem divProgramAuto_of_zero
    (rs2 rs1 : regidx) (quotient : BitVec 64) :
    divProgramAuto (regidx.Regidx 0) rs1 rs2 quotient =
      pureWritebackRdZeroProgram := by
  rfl

theorem divProgram_concrete
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ js',
      (execProgram (divProgramAuto rd rs1 rs2
        (sail_div_value dividend divisor false))).run js =
          .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sail_div_value dividend divisor false) := by
  let q := sail_div_value dividend divisor false
  let qMagnitude := signedQuotientMagnitude dividend divisor q
  have hdiv0 := hguard_div0_of_honest_signed dividend divisor
  have hoverflow := hguard_no_overflow_of_honest_signed dividend divisor
  have hlte := hguard_product_lte_of_honest_signed dividend divisor
  have hremainder := hguard_remainder_bound_of_honest_signed dividend divisor

  obtain ⟨js1, hrun1, h1_v0, h1_sail⟩ :=
    Div.phase_setup_run rs2 q divisor js hrs2 hdiv0
  have hrs1_1 : rX_bits rs1 js1.sail = .ok dividend js1.sail :=
    h1_sail.symm ▸ hrs1
  have hrs2_1 : rX_bits rs2 js1.sail = .ok divisor js1.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨js2, hrun2, h2_v0, h2_v1, h2_v2, h2_sail⟩ :=
    Div.phase_magnitudes_run rs1 rs2 dividend divisor q js1
      hrs1_1 hrs2_1 h1_v0

  have h2_sail_initial : js2.sail = js.sail := h2_sail.trans h1_sail
  have hrs1_2 : rX_bits rs1 js2.sail = .ok dividend js2.sail :=
    h2_sail_initial.symm ▸ hrs1
  have hrs2_2 : rX_bits rs2 js2.sail = .ok divisor js2.sail :=
    h2_sail_initial.symm ▸ hrs2
  obtain ⟨js3, hrun3, h3_v0, h3_v1, h3_v2, h3_v4, h3_sail⟩ :=
    Div.phase_quotient_magnitude_run rs1 rs2 dividend divisor q js2
      hrs1_2 hrs2_2 h2_v0 h2_v1 h2_v2

  obtain ⟨js4, hrun4, h4_v0, h4_v1, h4_v2, h4_v4, h4_v5, h4_sail⟩ :=
    Div.phase_product_run js3 q (bv_abs dividend) (bv_abs divisor) qMagnitude
      h3_v0 h3_v1 h3_v2 h3_v4 hoverflow hlte
  obtain ⟨js5, hrun5, h5_v0, _, h5_sail⟩ :=
    Div.phase_remainder_run js4 q (bv_abs dividend) (bv_abs divisor)
      qMagnitude h4_v0 h4_v1 h4_v2 h4_v4 h4_v5 hremainder

  have h5_sail_initial : js5.sail = js.sail :=
    h5_sail.trans (h4_sail.trans (h3_sail.trans h2_sail_initial))
  obtain ⟨js6, hrun6, h6_sail⟩ :=
    Div.phase_writeback_run rd js5 js.sail q h5_v0 h5_sail_initial

  have hphases : Program.Run (divProgramPhases rs2 rs1 rd q) js js6 := by
    unfold divProgramPhases
    exact Program.Run.append hrun1 <|
      Program.Run.append hrun2 <|
      Program.Run.append hrun3 <|
      Program.Run.append hrun4 <|
      Program.Run.append hrun5 hrun6
  have hprogram : Program.Run (divProgramAuto rd rs1 rs2 q) js js6 := by
    rw [divProgramAuto_eq_phases_of_ne_zero rs2 rs1 rd q hrd]
    exact hphases
  exact ⟨js6, hprogram, h6_sail⟩

theorem divProgram_sound
    (rs2 rs1 rd : regidx) (q : BitVec 64)
    (js : SailJoltState) (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0)
    (js' : SailJoltState)
    (hrun : (execProgram (divProgramAuto rd rs1 rs2 q)).run js =
      .ok RETIRE_SUCCESS js') :
    q = sail_div_value dividend divisor false := by
  have hphases : Program.Run (divProgramPhases rs2 rs1 rd q) js js' := by
    rw [← divProgramAuto_eq_phases_of_ne_zero rs2 rs1 rd q hrd]
    exact hrun
  unfold divProgramPhases at hphases
  obtain ⟨js1, hp1, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js2, hp2, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js3, hp3, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js4, hp4, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js5, hp5, _⟩ := Program.Run.append_inv hphases

  obtain ⟨hdiv0, h1_v0, h1_sail⟩ :=
    Div.phase_setup_run_sound rs2 q divisor js js1 hrs2 hp1
  have hrs1_1 : rX_bits rs1 js1.sail = .ok dividend js1.sail :=
    h1_sail.symm ▸ hrs1
  have hrs2_1 : rX_bits rs2 js1.sail = .ok divisor js1.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨h2_v0, h2_v1, h2_v2, h2_sail⟩ :=
    Div.phase_magnitudes_run_sound rs1 rs2 dividend divisor q js1 js2
      hrs1_1 hrs2_1 h1_v0 hp2

  have h2_sail_initial : js2.sail = js.sail := h2_sail.trans h1_sail
  have hrs1_2 : rX_bits rs1 js2.sail = .ok dividend js2.sail :=
    h2_sail_initial.symm ▸ hrs1
  have hrs2_2 : rX_bits rs2 js2.sail = .ok divisor js2.sail :=
    h2_sail_initial.symm ▸ hrs2
  obtain ⟨h3_v0, h3_v1, h3_v2, h3_v4, _⟩ :=
    Div.phase_quotient_magnitude_run_sound rs1 rs2 dividend divisor q js2 js3
      hrs1_2 hrs2_2 h2_v0 h2_v1 h2_v2 hp3

  obtain ⟨hoverflow, hlte, h4_v0, h4_v1, h4_v2, _, h4_v5, _⟩ :=
    Div.phase_product_run_sound js3 js4 q (bv_abs dividend) (bv_abs divisor)
      (signedQuotientMagnitude dividend divisor q)
      h3_v0 h3_v1 h3_v2 h3_v4 hp4
  obtain ⟨hremainder, _, _, _⟩ :=
    Div.phase_remainder_run_sound js4 js5 q (bv_abs dividend) (bv_abs divisor)
      (signedQuotientMagnitude dividend divisor q)
      h4_v0 h4_v1 h4_v2 h4_v5 hp5
  exact signed_quotient_eq_of_guards dividend divisor q
    hdiv0 hoverflow hlte hremainder

theorem execute_DIV_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIV rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_div_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_DIV, sail_div_value, bind_pure_comp]

theorem execute_DIV_reduces
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_DIV rs2 rs1 rd false).run js.sail =
      .ok RETIRE_SUCCESS
        (stateAfterWrite js.sail rd
          (sail_div_value dividend divisor false)) := by
  rw [execute_DIV_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_div_value dividend divisor false) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

end JoltISA

theorem divProgram_preserves_projected_vregs
    (rs2 rs1 rd : regidx) (quotient : BitVec 64)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram
      (JoltISA.divProgramAuto rd rs1 rs2 quotient)).run js = .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.divProgramAuto rd rs1 rs2 quotient) := by
    unfold JoltISA.divProgramAuto
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

def divProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  quotient = sail_div_value h.rs1_val h.rs2_val false →
    System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.divProgramAuto rd rs1 rs2 quotient)).run js) =
    (execute_DIV rs2 rs1 rd false).run js.sail

def divProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram
        (JoltISA.divProgramAuto rd rs1 rs2 quotient)).run js =
          .ok RETIRE_SUCCESS js' →
        quotient = sail_div_value h.rs1_val h.rs2_val false

def divProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  divProgramCompletenessStatement rs2 rs1 rd quotient js h ∧
  divProgramSoundnessStatement rs2 rs1 rd quotient js h

theorem divProgram_eq_sail
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    divProgramEqSailStatement rs2 rs1 rd quotient js h := by
  unfold divProgramEqSailStatement divProgramCompletenessStatement
    divProgramSoundnessStatement
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
      rw [JoltISA.divProgramAuto_of_zero]
      rw [JoltISA.pureWritebackRdZeroProgram_run js]
      simp only [System.systemProjectResult]
      rw [h_project_initial]
      rw [JoltISA.execute_DIV_factored rs2 rs1 (regidx.Regidx 0) false]
      simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
        hrs1, hrs2, wX_bits_regidx_zero]
    · obtain ⟨js', hjolt, hjolt_sail⟩ :=
        JoltISA.divProgram_concrete rs2 rs1 rd js dividend divisor
          hrs1 hrs2 hrd
      have h_projected_vregs : Projection.ProjectedVRegsPreserved js js' :=
        divProgram_preserves_projected_vregs rs2 rs1 rd
          (sail_div_value dividend divisor false) hjolt
      rw [hjolt]
      simp only [System.systemProjectResult]
      rw [JoltISA.execute_DIV_reduces rs2 rs1 rd js dividend divisor hrs1 hrs2]
      congr 1
      rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
        js js' rd (sail_div_value dividend divisor false)
        hjolt_sail h_projected_vregs]
      rw [h_project_initial]
  · intro hrd js' hrun
    exact JoltISA.divProgram_sound rs2 rs1 rd quotient js
      h.rs1_val h.rs2_val h.rs1_read h.rs2_read hrd js' hrun

end
