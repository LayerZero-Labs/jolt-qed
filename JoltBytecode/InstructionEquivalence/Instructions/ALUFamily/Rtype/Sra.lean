import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSRA
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualShiftRightBitmask
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.JoltISA.Values

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRA: Jolt VirtualSRA via bitmask = Sail SRA

Jolt program sequence:
1. `VirtualShiftRightBitmask v0, rs2` — compute the encoded shift bitmask
2. `VirtualSRA rd, rs1, v0` — arithmetic right shift by `ctz(bitmask)`
-/

-- NOTE: Math theorem: the Jolt bitmask SRA instruction computes Sail SRA.
private lemma virtual_sra_eq_shift
    (v1 : BitVec 64)
    (v2 : BitVec 64) :
    jolt_virtual_sra_value v1 (jolt_virtual_shift_right_bitmask_value v2) =
    shift_bits_right_arith v1
      (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold jolt_virtual_sra_value
  rw [ctz_jolt_virtual_shift_right_bitmask_value]
  unfold shift_bits_right_arith LeanRV64D.Functions.log2_xlen
  congr 1

abbrev sra_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  shift_bits_right_arith v1
    (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)

abbrev sra_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  jolt_virtual_sra_value v1 (jolt_virtual_shift_right_bitmask_value v2)

private theorem sra_value_eq_sail (v1 v2 : BitVec 64) :
    sra_jolt_val v1 v2 = sra_sail_operation v1 v2 := by
  simp only [sra_jolt_val, sra_sail_operation]
  exact virtual_sra_eq_shift v1 v2

theorem execute_RTYPE_SRA_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRA = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sra_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind, sra_sail_operation]

/-- Program-level concrete theorem for `SRA`.

The program-level proof mirrors `SRL`: first materialize the encoded shift
bitmask in scratch `v0`, then run the arithmetic virtual right shift that
consumes that scratch value. -/
theorem sraProgramAuto_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.sraProgramAuto rd rs1 rs2)).run js =
          .ok RETIRE_SUCCESS js' ∧
        js'.sail = stateAfterWrite js.sail rd (sra_sail_operation v1 v2) := by
  -- Instruction 1: `VirtualShiftRightBitmask v0, rs2` writes the shift bitmask to `v0`.
  let shiftBitmask := jolt_virtual_shift_right_bitmask_value v2
  obtain ⟨js_afterBitmask, h_bitmask_reads_rs2, h_bitmask_keeps_sail,
      h_bitmask_writes_shiftBitmask, _, h_bitmask_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_shift_right_bitmask_run_vreg_xreg
      JoltISA.inlineTmp0 rs2 js v2 h_read_rs2
      (by unfold WritableVReg; decide)

  -- Instruction 2: `VirtualSRA rd, rs1, v0` writes the shifted result to `rd`.
  let jolt_val := sra_jolt_val v1 v2
  obtain ⟨js_afterSra, h_virtual_sra_reads_rs1, h_virtual_sra_writes_jolt_val,
      h_virtual_sra_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_sra_run_xreg_xreg_vreg_of_value
      rd rs1 JoltISA.inlineTmp0 js_afterBitmask js.sail v1 shiftBitmask
      h_bitmask_keeps_sail h_read_rs1 h_bitmask_writes_shiftBitmask

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.sraProgramAuto rd rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js_afterSra := by
    unfold JoltISA.sraProgramAuto
    rw [JoltISA.isX0_eq_false_of_ne_zero hrd]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (BitVec.ofNat 7 40 : JoltISA.VReg) = JoltISA.inlineTmp0 by rfl]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterBitmask h_bitmask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterBitmask js_afterSra
      h_virtual_sra_succeeds]
    rfl

  refine ⟨js_afterSra, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SRA value.
  have h_final_jolt_value :
      js_afterSra.sail = stateAfterWrite js.sail rd jolt_val := by
    change js_afterSra.sail = stateAfterWrite js.sail rd jolt_val
    exact h_virtual_sra_writes_jolt_val

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's two-instruction value is Sail's SRA value.
  have h_sra_value :
      jolt_val = sra_sail_operation v1 v2 := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact sra_value_eq_sail v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_sra_value]
  exact h_final_jolt_value

/-- `SRA` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem sraProgramAuto_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.sraProgramAuto rd rs1 rs2)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.sraProgramAuto rd rs1 rs2) := by
    unfold JoltISA.sraProgramAuto
    split
    · simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg,
        JoltISA.DstWritesNoProtectedVReg,
        and_true]
    · rw [show (BitVec.ofNat 7 40 : JoltISA.VReg) = JoltISA.inlineTmp0 by rfl]
      simpa only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg,
        JoltISA.DstWritesNoProtectedVReg,
        and_true] using JoltISA.inlineTmp0_not_protected
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `SRA`. -/
def sraProgramEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.sraProgramAuto rd rs1 rs2)).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SRA).run js.sail

/-- Main program-level equivalence for `SRA`. -/
theorem sraProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    sraProgramEqSailStatement rs2 rs1 rd js h := by
  unfold sraProgramEqSailStatement
  let v1 := h.rs1_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail := h.rs1_read
  let v2 := h.rs2_val
  have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail := h.rs2_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.sraProgramAuto
    rw [JoltISA.isX0_regidx_zero]
    simp only [↓reduceIte]
    have hzero := JoltISA.pureWritebackRdZeroProgram_run js
    unfold JoltISA.pureWritebackRdZeroProgram at hzero
    rw [hzero]
    simp only [System.systemProjectResult]
    rw [h_project_initial]
    rw [execute_RTYPE_SRA_factored rs2 rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterSra, h_program_succeeds, h_final_sail⟩ :=
    sraProgramAuto_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd
  have h_projected_vregs :
      Projection.ProjectedVRegsPreserved js js_afterSra :=
    sraProgramAuto_preserves_projected_vregs rs2 rs1 rd h_program_succeeds

  rw [h_program_succeeds]
  simp only [System.systemProjectResult]

  rw [execute_RTYPE_SRA_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  obtain ⟨s', h_write⟩ := wX_shape rd (sra_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1

  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_afterSra rd (sra_sail_operation v1 v2)
    h_final_sail h_projected_vregs]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (sra_sail_operation v1 v2)
    js.sail s' h_write).symm

end
