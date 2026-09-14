import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.ExpansionBlocks.ALU
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLLI: Jolt VirtualMULI = Sail SLLI

Jolt program sequence:
1. `VirtualMULI rd, rs1, 2^shamt` — multiply by power of two
-/

private theorem extractLsb_shamt6_id (shamt : BitVec 6) :
    Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0 = shamt := by
  simp only [LeanRV64D.Functions.log2_xlen, Sail.BitVec.extractLsb]
  ext i; simp; rfl

private theorem mul_pow2_eq_shiftLeft (v : BitVec 64) (s : BitVec 6) :
    v * BitVec.ofNat 64 (2 ^ s.toNat) = v <<< s := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_ofNat]

private theorem slli_mul_eq_shift (v : BitVec 64) (shamt : BitVec 6) :
    v * BitVec.ofNat 64 (2 ^ shamt.toNat) =
    shift_bits_left v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold shift_bits_left
  rw [extractLsb_shamt6_id]
  exact mul_pow2_eq_shiftLeft v shamt

abbrev slli_sail_operation (shamt : BitVec 6) (v : BitVec 64) : BitVec 64 :=
  shift_bits_left v (Sail.BitVec.extractLsb shamt (LeanRV64D.Functions.log2_xlen -i 1) 0)

abbrev slli_jolt_val (shamt : BitVec 6) (v : BitVec 64) : BitVec 64 :=
  jolt_virtual_muli_value v (BitVec.ofNat 64 (2 ^ shamt.toNat))

private theorem slli_value_eq_sail (shamt : BitVec 6) (v : BitVec 64) :
    slli_jolt_val shamt v = slli_sail_operation shamt v := by
  simp only [slli_jolt_val, slli_sail_operation, jolt_virtual_muli_value]
  exact slli_mul_eq_shift v shamt

theorem execute_SHIFTIOP_SLLI_factored (shamt : BitVec 6) (rs1 rd : regidx) :
    execute_SHIFTIOP shamt rs1 rd sop.SLLI = (do
      let v ← rX_bits rs1
      wX_bits rd (slli_sail_operation shamt v)
      pure RETIRE_SUCCESS) := by
  simp only [execute_SHIFTIOP]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind, slli_sail_operation]

/-- Program-level concrete theorem for `SLLI`.

This is the theorem that the new architecture wants proofs to consume: the
left-hand side is the explicit Jolt-ISA program, not the older hand-written
monadic expansion. The instruction sequence is visible in the statement. -/
theorem slliProgramAuto_concrete (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState)
    (v : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.slliProgramAuto rd rs1 shamt)).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd (slli_sail_operation shamt v) := by

  -- Block 1: Rust `SLLI::inline_sequence` writes the shifted source to `rd`.
  let shiftedSource := shift_bits_left v shamt
  obtain ⟨js_afterSlli, h_slli_reads_rs1, h_slli_writes_shiftedSource, _,
      h_slli_block_succeeds⟩ :=
    JoltISA.exists_state_after_slli_block_run_xreg_xreg rd rs1 shamt js v h_read_rs1

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.slliProgramAuto rd rs1 shamt)).run js =
        .ok RETIRE_SUCCESS js_afterSlli := by
    unfold JoltISA.slliProgramAuto
    rw [JoltISA.isX0_eq_false_of_ne_zero hrd]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact h_slli_block_succeeds _

  refine ⟨js_afterSlli, h_program_succeeds, ?_⟩

  -- The block leaves `rd` containing the shifted source value.
  have h_final_shiftedSource :
      js_afterSlli.sail = stateAfterWrite js.sail rd shiftedSource := by
    exact h_slli_writes_shiftedSource

  -- No more execution reasoning remains. The only content left is that the
  -- block value is Sail's `SLLI` value.
  have h_slli_value :
      shiftedSource = slli_sail_operation shamt v := by
    simp only [shiftedSource, slli_sail_operation]
    rw [extractLsb_shamt6_id]
    rfl

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_slli_value]
  exact h_final_shiftedSource

/-- `SLLI` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem slliProgramAuto_preserves_projected_vregs
    (shamt : BitVec 6) (rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.slliProgramAuto rd rs1 shamt)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.slliProgramAuto rd rs1 shamt) := by
    unfold JoltISA.slliProgramAuto
    split <;>
      simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg,
        JoltISA.DstWritesNoProtectedVReg, and_true]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `SLLI`. -/
def slliProgramEqSailStatement (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : UnarySourceReadWithLinkedCSRs rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.slliProgramAuto rd rs1 shamt)).run js) =
    (execute_SHIFTIOP shamt rs1 rd sop.SLLI).run js.sail

/-- Main program-level equivalence for `SLLI`. -/
theorem slliProgram_eq_sail (shamt : BitVec 6) (rs1 rd : regidx)
    (js : SailJoltState)
    (h : UnarySourceReadWithLinkedCSRs rs1 js) :
    slliProgramEqSailStatement shamt rs1 rd js h := by
  unfold slliProgramEqSailStatement
  let v := h.rs1_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v js.sail := h.rs1_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.slliProgramAuto
    rw [JoltISA.isX0_regidx_zero]
    simp only [↓reduceIte]
    have hzero := JoltISA.pureWritebackRdZeroProgram_run js
    unfold JoltISA.pureWritebackRdZeroProgram at hzero
    rw [hzero]
    simp only [System.systemProjectResult]
    rw [h_project_initial]
    rw [execute_SHIFTIOP_SLLI_factored shamt rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterMuli, h_program_succeeds, h_final_sail⟩ :=
    slliProgramAuto_concrete shamt rs1 rd js v h_read_rs1 hrd
  have h_projected_vregs :
      Projection.ProjectedVRegsPreserved js js_afterMuli :=
    slliProgramAuto_preserves_projected_vregs shamt rs1 rd h_program_succeeds

  rw [h_program_succeeds]
  simp only [System.systemProjectResult]

  rw [execute_SHIFTIOP_SLLI_factored shamt rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1]

  obtain ⟨s', h_write⟩ := wX_shape rd (slli_sail_operation shamt v) js.sail
  simp only [h_write]
  congr 1

  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_afterMuli rd (slli_sail_operation shamt v)
    h_final_sail h_projected_vregs]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (slli_sail_operation shamt v)
    js.sail s' h_write).symm

end
