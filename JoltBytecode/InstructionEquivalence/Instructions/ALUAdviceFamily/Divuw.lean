import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Primitives
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Div_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divw_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.DivuwProgramBlocks
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divuw_math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# DIVUW: Jolt inline sequence with oracle advice

The canonical bytecode object in this file is `divuwProgramAuto`.
`divuwProgramPhases` is only the proof-facing decomposition used to compose
the phase lemmas.
-/

namespace JoltISA

/-- Proof-facing phase decomposition of `divuwProgramAuto`. -/
def divuwProgramPhases (rs2 rs1 rd : regidx) (quotient : BitVec 64) : Program :=
  pureWritebackTraceProgram rd <|
  (Divuw.phase_setup rs1 rs2 quotient).append <|
  Divuw.phase_quotient_product.append <|
  Divuw.phase_remainder_bound.append <|
  Divuw.phase_div0_check.append <|
  Divuw.phase_writeback rd

/-- Away from `x0`, the generated program is the proof-facing phase decomposition. -/
theorem divuwProgramAuto_eq_phases_of_ne_zero
    (rs2 rs1 rd : regidx) (quotient : BitVec 64)
    (hrd : rd ≠ regidx.Regidx 0) :
    divuwProgramAuto rd rs1 rs2 quotient =
      divuwProgramPhases rs2 rs1 rd quotient := by
  unfold divuwProgramAuto divuwProgramPhases
  rw [isX0_eq_false_of_ne_zero hrd]
  simp only [Bool.false_eq_true, if_false]
  rw [pureWritebackTraceProgram_of_ne_zero hrd]
  rfl

/-- At `x0`, the generated program is the shared pure-writeback program. -/
theorem divuwProgramAuto_of_zero
    (rs2 rs1 : regidx) (quotient : BitVec 64) :
    divuwProgramAuto (regidx.Regidx 0) rs1 rs2 quotient =
      pureWritebackRdZeroProgram := by
  rfl

/-- Running `divuwProgramAuto` with honest quotient advice succeeds and writes
Sail's unsigned 32-bit DIV value to `rd`. -/
theorem divuwProgram_concrete (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ js',
      (execProgram (divuwProgramAuto rd rs1 rs2
          (sail_divuw_advice dividend divisor))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sail_divw_value dividend divisor true) := by
  let q := sail_divuw_advice dividend divisor
  let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)

  have hguard_no_overflow : q.toNat * zv.toNat < 2^64 :=
    hguard_no_overflow_of_honest_uw dividend divisor
  have hguard_lte : (q * zv).toNat ≤ zd.toNat :=
    hguard_q_times_d_le_dividend_of_honest_uw dividend divisor
  have hguard_rem_bound : zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat :=
    hguard_rem_bound_of_honest_uw dividend divisor
  have hguard_div0 :
      ¬ (zv = 0#64 ∧
        sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ≠ (-1 : BitVec 64)) :=
    hguard_div0_of_honest_uw dividend divisor
  have h_sext_q :
      sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) =
        sail_divw_value dividend divisor true :=
    sext_advice_eq_sail_divw_value dividend divisor

  obtain ⟨js₁, hrun1, h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Divuw.phase_setup_run rs1 rs2 q js dividend divisor
      hrs1 hrs2 hguard_no_overflow

  obtain ⟨js₂, hrun2, h2_v0, h2_v1, h2_v2, h2_v3, h2_sail⟩ :=
    Divuw.phase_quotient_product_run js₁ q zd zv
      h1_v0 h1_v1 h1_v2 hguard_lte

  have h2_sail_orig : js₂.sail = js.sail := h2_sail.trans h1_sail
  obtain ⟨js₃, hrun3, h3_v0, h3_v1, h3_v2, h3_sail⟩ :=
    Divuw.phase_remainder_bound_run js₂ q zd zv
      h2_v0 h2_v1 h2_v2 h2_v3 hguard_rem_bound

  have h3_sail_orig : js₃.sail = js.sail := h3_sail.trans h2_sail_orig
  obtain ⟨js₄, hrun4, h4_v3, h4_sail⟩ :=
    Divuw.phase_div0_check_run js₃ q zv h3_v1 h3_v2 hguard_div0

  have h4_sail_orig : js₄.sail = js.sail := h4_sail.trans h3_sail_orig
  obtain ⟨js₅, hrun5, h5_sail⟩ :=
    Divuw.phase_writeback_run rd js₄ js.sail
      (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0))
      h4_v3 h4_sail_orig

  have h_phase_program_succeeds :
      Program.Run (divuwProgramPhases rs2 rs1 rd q) js js₅ := by
    unfold divuwProgramPhases
    rw [pureWritebackTraceProgram_of_ne_zero hrd]
    exact Program.Run.append hrun1
      (Program.Run.append hrun2
        (Program.Run.append hrun3
          (Program.Run.append hrun4 hrun5)))
  have h_program_succeeds :
      Program.Run (divuwProgramAuto rd rs1 rs2 q) js js₅ := by
    rw [divuwProgramAuto_eq_phases_of_ne_zero rs2 rs1 rd q hrd]
    exact h_phase_program_succeeds
  rw [h_sext_q] at h5_sail
  exact ⟨js₅, h_program_succeeds, h5_sail⟩

/-- Factoring lemma: `execute_DIVW` collapses to the pure `sail_divw_value`. -/
theorem execute_DIVUW_factored (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIVW rs2 rs1 rd is_unsigned = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sail_divw_value v1 v2 is_unsigned)
      pure RETIRE_SUCCESS) := by
  simp [execute_DIVW, sail_divw_value, bind_pure_comp]

/-- Sail's `execute_DIVW ... true` writes `sail_divw_value`. -/
theorem execute_DIVUW_reduces (rs2 rs1 rd : regidx) (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail) :
    (execute_DIVW rs2 rs1 rd true).run js.sail =
      .ok RETIRE_SUCCESS
        (stateAfterWrite js.sail rd (sail_divw_value dividend divisor true)) := by
  rw [execute_DIVUW_factored]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure, hrs1, hrs2]
  obtain ⟨s', hw⟩ := wX_shape rd (sail_divw_value dividend divisor true) js.sail
  rw [hw]
  simp only []
  congr 1
  exact wX_bits_eq_stateAfterWrite rd _ js.sail s' hw

/-- Any successful DIVUW run writes Sail's unsigned 32-bit quotient. -/
theorem divuwProgram_sound (rs2 rs1 rd : regidx)
    (q : BitVec 64)
    (js : SailJoltState)
    (dividend divisor : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok dividend js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok divisor js.sail)
    (hrd : rd ≠ regidx.Regidx 0)
    (js' : SailJoltState)
    (hok : (execProgram (divuwProgramAuto rd rs1 rs2 q)).run js =
      .ok RETIRE_SUCCESS js') :
    js'.sail =
      stateAfterWrite js.sail rd (sail_divw_value dividend divisor true) := by
  let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
  let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
  have h_program_succeeds : Program.Run (divuwProgramPhases rs2 rs1 rd q) js js' := by
    rw [← divuwProgramAuto_eq_phases_of_ne_zero rs2 rs1 rd q hrd]
    exact hok
  unfold divuwProgramPhases at h_program_succeeds
  rw [pureWritebackTraceProgram_of_ne_zero hrd] at h_program_succeeds
  obtain ⟨js₁, hp1, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₂, hp2, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₃, hp3, h_program_succeeds⟩ :=
    Program.Run.append_inv h_program_succeeds
  obtain ⟨js₄, hp4, hp5⟩ :=
    Program.Run.append_inv h_program_succeeds

  obtain ⟨hguard1, h1_v0, h1_v1, h1_v2, h1_sail⟩ :=
    Divuw.phase_setup_run_sound rs1 rs2 q js js₁ dividend divisor
      hrs1 hrs2 hp1

  obtain ⟨hguard2, h2_v0, h2_v1, h2_v2, h2_v3, h2_sail⟩ :=
    Divuw.phase_quotient_product_run_sound js₁ js₂ q zd zv
      h1_v0 h1_v1 h1_v2 hp2

  obtain ⟨hguard3, h3_v0, h3_v1, h3_v2, h3_sail⟩ :=
    Divuw.phase_remainder_bound_run_sound js₂ js₃ q zd zv
      h2_v0 h2_v1 h2_v2 h2_v3 hp3

  obtain ⟨hguard4, h4_v3, h4_sail⟩ :=
    Divuw.phase_div0_check_run_sound js₃ js₄ q zv
      h3_v1 h3_v2 hp4

  have h_sext :
      sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) =
        sail_divw_value dividend divisor true :=
    sext_advice_eq_sail_divw_value_of_guards_uw dividend divisor q
      hguard1 hguard2 hguard3 hguard4
  have h4_sail_orig : js₄.sail = js.sail :=
    h4_sail.trans (h3_sail.trans (h2_sail.trans h1_sail))
  have hwrite :=
    Divuw.phase_writeback_run_sound rd js₄ js' js.sail
      (sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0))
      h4_v3 h4_sail_orig hp5
  rw [h_sext] at hwrite
  exact hwrite

end JoltISA

/-- `DIVUW` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem divuwProgram_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram
      (JoltISA.divuwProgramAuto rd rs1 rs2 quotient)).run js = .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.divuwProgramAuto rd rs1 rs2 quotient) := by
    unfold JoltISA.divuwProgramAuto
    split
    · exact JoltISA.pureWritebackRdZeroProgram_writesNoProtected
    · simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg,
        JoltISA.DstWritesNoProtectedVReg,
        JoltISA.VRegWritesNoProtectedVReg, true_and, and_true]
      repeat' apply And.intro
      all_goals exact JoltISA.not_protected_of_instructionTmp rfl
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `DIVUW` with honest advice. -/
def divuwProgramCompletenessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  quotient = sail_divuw_advice h.rs1_val h.rs2_val →
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.divuwProgramAuto rd rs1 rs2 quotient)).run js) =
    (execute_DIVW rs2 rs1 rd true).run js.sail

def divuwProgramSoundnessStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  rd ≠ regidx.Regidx 0 →
    ∀ js',
      (JoltISA.execProgram (JoltISA.divuwProgramAuto rd rs1 rs2 quotient)).run js =
          .ok RETIRE_SUCCESS js' →
        js'.sail = stateAfterWrite js.sail rd
          (sail_divw_value h.rs1_val h.rs2_val true)

def divuwProgramEqSailStatement
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  divuwProgramCompletenessStatement rs2 rs1 rd quotient js h ∧
  divuwProgramSoundnessStatement rs2 rs1 rd quotient js h

theorem divuwProgram_eq_sail
    (rs2 rs1 rd : regidx)
    (quotient : BitVec 64)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    divuwProgramEqSailStatement rs2 rs1 rd quotient js h := by
  unfold divuwProgramEqSailStatement divuwProgramCompletenessStatement
    divuwProgramSoundnessStatement
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
      rw [JoltISA.divuwProgramAuto_of_zero]
      rw [JoltISA.pureWritebackRdZeroProgram_run js]
      simp only [System.systemProjectResult]
      rw [h_project_initial]
      rw [JoltISA.execute_DIVUW_factored rs2 rs1 (regidx.Regidx 0) true]
      simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
      simp only [hrs1, hrs2]
      simp only [wX_bits_regidx_zero]

    obtain ⟨js', hjolt, hjolt_sail⟩ :=
      JoltISA.divuwProgram_concrete rs2 rs1 rd js dividend divisor hrs1 hrs2 hrd
    have h_projected_vregs :
        Projection.ProjectedVRegsPreserved js js' :=
      divuwProgram_preserves_projected_vregs rs2 rs1 rd
        (sail_divuw_advice dividend divisor) hjolt
    rw [hjolt]
    simp only [System.systemProjectResult]
    rw [JoltISA.execute_DIVUW_reduces rs2 rs1 rd js dividend divisor hrs1 hrs2]
    congr 1
    rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
      js js' rd (sail_divw_value dividend divisor true) hjolt_sail h_projected_vregs]
    rw [h_project_initial]
  · intro hrd js' hok
    exact JoltISA.divuwProgram_sound rs2 rs1 rd quotient js
      h.rs1_val h.rs2_val h.rs1_read h.rs2_read hrd js' hok

end
