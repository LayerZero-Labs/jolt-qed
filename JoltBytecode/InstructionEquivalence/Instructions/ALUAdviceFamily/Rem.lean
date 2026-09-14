import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.RemProgramBlocks

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

namespace JoltISA

/-- Proof-facing decomposition of the current one-advice Rust `REM` rows. -/
def remProgramPhases
    (rs2 rs1 rd : regidx) (quotientMagnitude : BitVec 64) : Program :=
  (Rem.phase_setup quotientMagnitude).append <|
  (Div.phase_magnitudes rs1 rs2).append <|
  Rem.phase_product.append <|
  Rem.phase_remainder.append <|
  Rem.phase_writeback rs1 rd

theorem remProgramAuto_eq_phases_of_ne_zero
    (rs2 rs1 rd : regidx) (quotientMagnitude : BitVec 64)
    (hrd : rd ≠ regidx.Regidx 0) :
    remProgramAuto rd rs1 rs2 quotientMagnitude =
      remProgramPhases rs2 rs1 rd quotientMagnitude := by
  unfold remProgramAuto
  rw [isX0_eq_false_of_ne_zero hrd]
  rfl

theorem remProgramAuto_of_zero
    (rs2 rs1 : regidx) (quotientMagnitude : BitVec 64) :
    remProgramAuto (regidx.Regidx 0) rs1 rs2 quotientMagnitude =
      pureWritebackRdZeroProgram := by
  rfl

theorem remProgram_concrete
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ js',
      (execProgram (remProgramAuto rd rs1 rs2
        (rem_advice_value dividend divisor))).run js =
          .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sail_rem_value dividend divisor false) := by
  let q := rem_advice_value dividend divisor
  let rem := bv_abs dividend - q * bv_abs divisor
  have hoverflow := hguard_no_overflow_of_honest_rem dividend divisor
  have hlte := hguard_product_lte_of_honest_rem dividend divisor
  have hremainder := hguard_remainder_bound_of_honest_rem dividend divisor
  have hresult :
      jolt_virtual_negate_if_value dividend rem =
        sail_rem_value dividend divisor false := by
    unfold rem q
    exact signed_remainder_eq_of_guards dividend divisor
      (rem_advice_value dividend divisor) hoverflow hlte hremainder

  obtain ⟨js1, hrun1, h1_v0, h1_sail⟩ :=
    Rem.phase_setup_run q js
  have hrs1_1 : rX_bits rs1 js1.sail = .ok dividend js1.sail :=
    h1_sail.symm ▸ hrs1
  have hrs2_1 : rX_bits rs2 js1.sail = .ok divisor js1.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨js2, hrun2, h2_v0, h2_v1, h2_v2, h2_sail⟩ :=
    Div.phase_magnitudes_run rs1 rs2 dividend divisor q js1
      hrs1_1 hrs2_1 h1_v0

  obtain ⟨js3, hrun3, h3_v0, h3_v1, h3_v2, h3_v3, h3_sail⟩ :=
    Rem.phase_product_run js2 q (bv_abs dividend) (bv_abs divisor)
      h2_v0 h2_v1 h2_v2 hoverflow hlte
  obtain ⟨js4, hrun4, h4_v3, h4_sail⟩ :=
    Rem.phase_remainder_run js3 q (bv_abs dividend) (bv_abs divisor)
      h3_v0 h3_v1 h3_v2 h3_v3 hremainder

  have h4_sail_initial : js4.sail = js.sail :=
    h4_sail.trans (h3_sail.trans (h2_sail.trans h1_sail))
  have hrs1_4 : rX_bits rs1 js4.sail = .ok dividend js4.sail :=
    h4_sail_initial.symm ▸ hrs1
  obtain ⟨js5, hrun5, h5_sail⟩ :=
    Rem.phase_writeback_run rs1 rd js4 js.sail dividend rem
      (sail_rem_value dividend divisor false)
      hrs1_4 h4_v3 hresult h4_sail_initial

  have hphases : Program.Run (remProgramPhases rs2 rs1 rd q) js js5 := by
    unfold remProgramPhases
    exact Program.Run.append hrun1 <|
      Program.Run.append hrun2 <|
      Program.Run.append hrun3 <|
      Program.Run.append hrun4 hrun5
  have hprogram : Program.Run (remProgramAuto rd rs1 rs2 q) js js5 := by
    rw [remProgramAuto_eq_phases_of_ne_zero rs2 rs1 rd q hrd]
    exact hphases
  exact ⟨js5, hprogram, h5_sail⟩

theorem remProgram_sound
    (rs2 rs1 rd : regidx) (q : BitVec 64)
    (js : SailJoltState) (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0)
    (js' : SailJoltState)
    (hrun : (execProgram (remProgramAuto rd rs1 rs2 q)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.sail = stateAfterWrite js.sail rd
      (sail_rem_value dividend divisor false) := by
  have hphases : Program.Run (remProgramPhases rs2 rs1 rd q) js js' := by
    rw [← remProgramAuto_eq_phases_of_ne_zero rs2 rs1 rd q hrd]
    exact hrun
  unfold remProgramPhases at hphases
  obtain ⟨js1, hp1, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js2, hp2, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js3, hp3, hphases⟩ := Program.Run.append_inv hphases
  obtain ⟨js4, hp4, hp5⟩ := Program.Run.append_inv hphases

  obtain ⟨h1_v0, h1_sail⟩ :=
    Rem.phase_setup_run_sound q js js1 hp1
  have hrs1_1 : rX_bits rs1 js1.sail = .ok dividend js1.sail :=
    h1_sail.symm ▸ hrs1
  have hrs2_1 : rX_bits rs2 js1.sail = .ok divisor js1.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨h2_v0, h2_v1, h2_v2, h2_sail⟩ :=
    Div.phase_magnitudes_run_sound rs1 rs2 dividend divisor q js1 js2
      hrs1_1 hrs2_1 h1_v0 hp2

  obtain ⟨hoverflow, hlte, h3_v0, h3_v1, h3_v2, h3_v3, h3_sail⟩ :=
    Rem.phase_product_run_sound js2 js3 q (bv_abs dividend) (bv_abs divisor)
      h2_v0 h2_v1 h2_v2 hp3
  obtain ⟨hremainder, h4_v3, h4_sail⟩ :=
    Rem.phase_remainder_run_sound js3 js4 q
      (bv_abs dividend) (bv_abs divisor) h3_v1 h3_v2 h3_v3 hp4

  let rem := bv_abs dividend - q * bv_abs divisor
  have hresult :
      jolt_virtual_negate_if_value dividend rem =
        sail_rem_value dividend divisor false := by
    unfold rem
    exact signed_remainder_eq_of_guards dividend divisor q
      hoverflow hlte hremainder
  have h4_sail_initial : js4.sail = js.sail :=
    h4_sail.trans (h3_sail.trans (h2_sail.trans h1_sail))
  have hrs1_4 : rX_bits rs1 js4.sail = .ok dividend js4.sail :=
    h4_sail_initial.symm ▸ hrs1
  exact Rem.phase_writeback_run_sound rs1 rd js4 js' js.sail
    dividend rem (sail_rem_value dividend divisor false)
    hrs1_4 h4_v3 hresult h4_sail_initial hp5

theorem execute_REM_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_REM rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_rem_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_REM, sail_rem_value, bind_pure_comp]

theorem execute_REM_reduces
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_REM rs2 rs1 rd false).run js.sail =
      .ok RETIRE_SUCCESS
        (stateAfterWrite js.sail rd
          (sail_rem_value dividend divisor false)) := by
  rw [execute_REM_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_rem_value dividend divisor false) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

end JoltISA

theorem remProgram_preserves_projected_vregs
    (rs2 rs1 rd : regidx) (quotientMagnitude : BitVec 64)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram
      (JoltISA.remProgramAuto rd rs1 rs2 quotientMagnitude)).run js =
        .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.remProgramAuto rd rs1 rs2 quotientMagnitude) := by
    unfold JoltISA.remProgramAuto
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
        JoltISA.inlineTmp3_not_protected⟩
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

def remProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  quotientMagnitude = rem_advice_value h.rs1_val h.rs2_val →
    System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.remProgramAuto rd rs1 rs2 quotientMagnitude)).run js) =
    (execute_REM rs2 rs1 rd false).run js.sail

def remProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram
        (JoltISA.remProgramAuto rd rs1 rs2 quotientMagnitude)).run js =
          .ok RETIRE_SUCCESS js' →
        js'.sail = stateAfterWrite js.sail rd
          (sail_rem_value h.rs1_val h.rs2_val false)

def remProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  remProgramCompletenessStatement rs2 rs1 rd quotientMagnitude js h ∧
  remProgramSoundnessStatement rs2 rs1 rd quotientMagnitude js h

theorem remProgram_eq_sail
    (rs2 rs1 rd : regidx)
    (quotientMagnitude : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    remProgramEqSailStatement rs2 rs1 rd quotientMagnitude js h := by
  unfold remProgramEqSailStatement remProgramCompletenessStatement
    remProgramSoundnessStatement
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
      rw [JoltISA.remProgramAuto_of_zero]
      rw [JoltISA.pureWritebackRdZeroProgram_run js]
      simp only [System.systemProjectResult]
      rw [h_project_initial]
      rw [JoltISA.execute_REM_factored rs2 rs1 (regidx.Regidx 0) false]
      simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
        hrs1, hrs2, wX_bits_regidx_zero]
    · obtain ⟨js', hjolt, hjolt_sail⟩ :=
        JoltISA.remProgram_concrete rs2 rs1 rd js dividend divisor
          hrs1 hrs2 hrd
      have h_projected_vregs : Projection.ProjectedVRegsPreserved js js' :=
        remProgram_preserves_projected_vregs rs2 rs1 rd
          (rem_advice_value dividend divisor) hjolt
      rw [hjolt]
      simp only [System.systemProjectResult]
      rw [JoltISA.execute_REM_reduces rs2 rs1 rd js dividend divisor hrs1 hrs2]
      congr 1
      rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
        js js' rd (sail_rem_value dividend divisor false)
        hjolt_sail h_projected_vregs]
      rw [h_project_initial]
  · intro hrd js' hrun
    exact JoltISA.remProgram_sound rs2 rs1 rd quotientMagnitude js
      h.rs1_val h.rs2_val h.rs1_read h.rs2_read hrd js' hrun

end
