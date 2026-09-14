import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Primitives
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divu_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.DivuProgramBlocks

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# DIVU: Jolt inline sequence with oracle advice

The canonical bytecode object in this file is `divuProgramAuto`.
`divuProgramPhases` is only the proof-facing decomposition used to compose the
phase lemmas.
-/

namespace JoltISA

/-- Proof-facing phase decomposition of `divuProgramAuto`. -/
def divuProgramPhases (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  (Divu.phase_setup rs2 quotient).append <|
  (Divu.phase_overflow_check rs2).append <|
  (Divu.phase_quotient_product rs1 rs2).append <|
  (Divu.phase_remainder_bound rs1 rs2).append <|
  Divu.phase_writeback rd

/-- Away from `x0`, the generated program is the proof-facing phase decomposition. -/
theorem divuProgramAuto_eq_phases_of_ne_zero
    (rs2 rs1 rd : regidx) (quotient : BitVec 64)
    (hrd : rd ≠ regidx.Regidx 0) :
    divuProgramAuto rd rs1 rs2 quotient =
      divuProgramPhases rs2 rs1 rd quotient := by
  unfold divuProgramAuto divuProgramPhases
  rw [isX0_eq_false_of_ne_zero hrd]
  simp only [Bool.false_eq_true, if_false]
  rw [pureWritebackTraceProgram_of_ne_zero hrd]
  rfl

/-- At `x0`, the generated program is the shared pure-writeback program. -/
theorem divuProgramAuto_of_zero
    (rs2 rs1 : regidx) (quotient : BitVec 64) :
    divuProgramAuto (regidx.Regidx 0) rs1 rs2 quotient =
      pureWritebackRdZeroProgram := by
  rfl

/-- Running `divuProgramAuto` with honest quotient advice succeeds and writes Sail's
unsigned DIV value to `rd`. -/
theorem divuProgram_concrete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ js',
      (execProgram (divuProgramAuto rd rs1 rs2
          (sail_div_value dividend divisor true))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sail_div_value dividend divisor true) := by
  let q := sail_div_value dividend divisor true
  have hguard_div0 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) :=
    hguard_div0_of_honest_u dividend divisor
  have hguard_no_overflow : q.toNat * divisor.toNat < 2^64 :=
    hguard_no_overflow_of_honest_u dividend divisor
  have hguard_lte : (q * divisor).toNat ≤ dividend.toNat :=
    hguard_q_times_d_le_dividend_of_honest_u dividend divisor
  have hguard_rem_bound :
      divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat :=
    hguard_rem_bound_of_honest_u dividend divisor

  obtain ⟨js₁, hrun1, h1_v0, h1_sail⟩ :=
    Divu.phase_setup_run rs2 q js divisor hrs2 hguard_div0

  have hrs2_js1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨js₂, hrun2, h2_v0, h2_sail⟩ :=
    Divu.phase_overflow_check_run rs2 js₁ q divisor
      hrs2_js1 h1_v0 hguard_no_overflow

  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hrs1_js2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  have hrs2_js2 : rX_bits rs2 js₂.sail = .ok divisor js₂.sail :=
    h2_sail_orig.symm ▸ hrs2
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_sail⟩ :=
    Divu.phase_quotient_product_run rs1 rs2 js₂ q dividend divisor
      hrs1_js2 hrs2_js2 h2_v0 hguard_lte

  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  have hrs1_js3 : rX_bits rs1 js₃.sail = .ok dividend js₃.sail :=
    h3_sail_orig.symm ▸ hrs1
  have hrs2_js3 : rX_bits rs2 js₃.sail = .ok divisor js₃.sail :=
    h3_sail_orig.symm ▸ hrs2
  obtain ⟨js₄, hrun4, h4_v0, h4_sail⟩ :=
    Divu.phase_remainder_bound_run rs1 rs2 js₃ q dividend divisor
      hrs1_js3 hrs2_js3 h3_v0 h3_v1 hguard_rem_bound

  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  obtain ⟨js₅, hrun5, h5_sail⟩ :=
    Divu.phase_writeback_run rd js₄ js.sail q h4_v0 h4_sail_orig

  have h_phase_program_succeeds :
      Program.Run (divuProgramPhases rs2 rs1 rd q) js js₅ := by
    unfold divuProgramPhases
    rw [pureWritebackTraceProgram_of_ne_zero hrd]
    exact Program.Run.append hrun1
      (Program.Run.append hrun2
        (Program.Run.append hrun3
          (Program.Run.append hrun4 hrun5)))
  have h_program_succeeds :
      Program.Run (divuProgramAuto rd rs1 rs2 q) js js₅ := by
    rw [divuProgramAuto_eq_phases_of_ne_zero rs2 rs1 rd q hrd]
    exact h_phase_program_succeeds
  exact ⟨js₅, h_program_succeeds, h5_sail⟩

/-- Factoring lemma: `execute_DIV` collapses to the pure `sail_div_value`. -/
theorem execute_DIVU_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIV rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_div_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_DIV, sail_div_value, bind_pure_comp]

/-- Sail's `execute_DIV ... true` writes `sail_div_value`. -/
theorem execute_DIVU_reduces (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_DIV rs2 rs1 rd true).run js.sail =
      .ok RETIRE_SUCCESS
        (stateAfterWrite js.sail rd (sail_div_value dividend divisor true)) := by
  rw [execute_DIVU_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_div_value dividend divisor true) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Any successful DIVU run pins the quotient advice to Sail's quotient. -/
theorem divuProgram_sound (rs2 rs1 rd : regidx)
    (q : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0)
    (js' : SailJoltState)
    (hok : (execProgram (divuProgramAuto rd rs1 rs2 q)).run js =
      .ok RETIRE_SUCCESS js') :
    q = sail_div_value dividend divisor true := by
  have h_program_succeeds : Program.Run (divuProgramPhases rs2 rs1 rd q) js js' := by
    rw [← divuProgramAuto_eq_phases_of_ne_zero rs2 rs1 rd q hrd]
    exact hok
  unfold divuProgramPhases at h_program_succeeds
  rw [pureWritebackTraceProgram_of_ne_zero hrd] at h_program_succeeds
  obtain ⟨js₁, hp1, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₂, hp2, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₃, hp3, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₄, hp4, _hp5⟩ :=
    Program.Run.append_inv h_program_succeeds

  obtain ⟨hguard1, h1_v0, h1_sail⟩ :=
    Divu.phase_setup_run_sound rs2 q js js₁ divisor hrs2 hp1

  have hrs2_1 : rX_bits rs2 js₁.sail = .ok divisor js₁.sail :=
    h1_sail.symm ▸ hrs2
  obtain ⟨hguard2, h2_v0, h2_sail⟩ :=
    Divu.phase_overflow_check_run_sound rs2 js₁ js₂ q divisor
      hrs2_1 h1_v0 hp2

  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  have hrs1_2 : rX_bits rs1 js₂.sail = .ok dividend js₂.sail :=
    h2_sail_orig.symm ▸ hrs1
  have hrs2_2 : rX_bits rs2 js₂.sail = .ok divisor js₂.sail :=
    h2_sail_orig.symm ▸ hrs2
  obtain ⟨hguard3, h3_v0, h3_v1, h3_sail⟩ :=
    Divu.phase_quotient_product_run_sound rs1 rs2 js₂ js₃ q dividend divisor
      hrs1_2 hrs2_2 h2_v0 hp3

  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  have hrs1_3 : rX_bits rs1 js₃.sail = .ok dividend js₃.sail :=
    h3_sail_orig.symm ▸ hrs1
  have hrs2_3 : rX_bits rs2 js₃.sail = .ok divisor js₃.sail :=
    h3_sail_orig.symm ▸ hrs2
  obtain ⟨hguard4, _, _⟩ :=
    Divu.phase_remainder_bound_run_sound rs1 rs2 js₃ js₄ q dividend divisor
      hrs1_3 hrs2_3 h3_v0 h3_v1 hp4

  exact advice_unique_of_guards_u dividend divisor q
    hguard1 hguard2 hguard3 hguard4

end JoltISA

/-- `DIVU` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem divuProgram_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram
      (JoltISA.divuProgramAuto rd rs1 rs2 quotient)).run js = .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.divuProgramAuto rd rs1 rs2 quotient) := by
    unfold JoltISA.divuProgramAuto
    split
    · exact JoltISA.pureWritebackRdZeroProgram_writesNoProtected
    · simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg,
        JoltISA.DstWritesNoProtectedVReg,
        JoltISA.VRegWritesNoProtectedVReg, true_and, and_true]
      exact ⟨JoltISA.inlineTmp0_not_protected,
        JoltISA.inlineTmp1_not_protected,
        JoltISA.inlineTmp1_not_protected⟩
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `DIVU` with honest advice. -/
def divuProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  quotient = sail_div_value h.rs1_val h.rs2_val true →
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.divuProgramAuto rd rs1 rs2 quotient)).run js) =
    (execute_DIV rs2 rs1 rd true).run js.sail

def divuProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram (JoltISA.divuProgramAuto rd rs1 rs2 quotient)).run js =
          .ok RETIRE_SUCCESS js' →
        quotient = sail_div_value h.rs1_val h.rs2_val true

def divuProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  divuProgramCompletenessStatement rs2 rs1 rd quotient js h ∧
  divuProgramSoundnessStatement rs2 rs1 rd quotient js h

theorem divuProgram_eq_sail (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    divuProgramEqSailStatement rs2 rs1 rd quotient js h := by
  unfold divuProgramEqSailStatement divuProgramCompletenessStatement
    divuProgramSoundnessStatement
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
      rw [JoltISA.divuProgramAuto_of_zero]
      rw [JoltISA.pureWritebackRdZeroProgram_run js]
      simp only [System.systemProjectResult]
      rw [h_project_initial]
      rw [JoltISA.execute_DIVU_factored rs2 rs1 (regidx.Regidx 0) true]
      simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
      simp only [hrs1, hrs2]
      simp only [wX_bits_regidx_zero]

    obtain ⟨js', hjolt, hjolt_sail⟩ :=
      JoltISA.divuProgram_concrete rs2 rs1 rd js dividend divisor hrs1 hrs2 hrd
    have h_projected_vregs :
        Projection.ProjectedVRegsPreserved js js' :=
      divuProgram_preserves_projected_vregs rs2 rs1 rd
        (sail_div_value dividend divisor true) hjolt
    rw [hjolt]
    simp only [System.systemProjectResult]
    rw [JoltISA.execute_DIVU_reduces rs2 rs1 rd js dividend divisor hrs1 hrs2]
    congr 1
    rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
      js js' rd (sail_div_value dividend divisor true) hjolt_sail h_projected_vregs]
    rw [h_project_initial]
  · intro hrd js' hok
    exact JoltISA.divuProgram_sound rs2 rs1 rd quotient js
      h.rs1_val h.rs2_val h.rs1_read h.rs2_read hrd js' hok

end
