import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualSRL
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualShiftRightBitmask
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.JoltISA.Values

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SRL: Jolt VirtualSRL via bitmask = Sail SRL

Jolt program sequence:
1. `VirtualShiftRightBitmask v0, rs2` — compute the encoded shift bitmask
2. `VirtualSRL rd, rs1, bitmask` — logical right shift by `ctz(bitmask)`

`ctz(bitmask) = rs2[5:0]`, so this matches Sail's SRL.
-/

-- NOTE: Math theorem: the Jolt bitmask SRL instruction computes Sail SRL.
private lemma virtual_srl_eq_shift
    (v1 : BitVec 64)
    (v2 : BitVec 64) :
    jolt_virtual_srl_value v1 (jolt_virtual_shift_right_bitmask_value v2) =
    shift_bits_right v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold jolt_virtual_srl_value
  rw [ctz_jolt_virtual_shift_right_bitmask_value]
  unfold shift_bits_right LeanRV64D.Functions.log2_xlen
  congr 1

abbrev srl_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  shift_bits_right v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)

abbrev srl_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  jolt_virtual_srl_value v1 (jolt_virtual_shift_right_bitmask_value v2)

private theorem srl_value_eq_sail (v1 v2 : BitVec 64) :
    srl_jolt_val v1 v2 = srl_sail_operation v1 v2 := by
  simp only [srl_jolt_val, srl_sail_operation]
  exact virtual_srl_eq_shift v1 v2

theorem execute_RTYPE_SRL_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SRL = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (srl_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind, srl_sail_operation]

/-- Program-level concrete theorem for `SRL`.

The program first writes the virtual right-shift bitmask for `rs2` into
scratch `v0`; the second instruction consumes that scratch value with
`VirtualSRL` and writes the real destination. -/
theorem srlProgramAuto_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.srlProgramAuto rd rs1 rs2)).run js =
          .ok RETIRE_SUCCESS js' ∧
        js'.sail = stateAfterWrite js.sail rd (srl_sail_operation v1 v2) := by
  -- Instruction 1: `VirtualShiftRightBitmask v0, rs2` writes the shift bitmask to `v0`.
  let shiftBitmask := jolt_virtual_shift_right_bitmask_value v2
  obtain ⟨js_afterBitmask, h_bitmask_reads_rs2, h_bitmask_keeps_sail,
      h_bitmask_writes_shiftBitmask, _, h_bitmask_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_shift_right_bitmask_run_vreg_xreg
      JoltISA.inlineTmp0 rs2 js v2 h_read_rs2
      (by unfold WritableVReg; decide)

  -- Instruction 2: `VirtualSRL rd, rs1, v0` writes the shifted result to `rd`.
  let jolt_val := srl_jolt_val v1 v2
  obtain ⟨js_afterSrl, h_virtual_srl_reads_rs1, h_virtual_srl_writes_jolt_val,
      h_virtual_srl_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_srl_run_xreg_xreg_vreg_of_value
      rd rs1 JoltISA.inlineTmp0 js_afterBitmask js.sail v1 shiftBitmask
      h_bitmask_keeps_sail h_read_rs1 h_bitmask_writes_shiftBitmask

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.srlProgramAuto rd rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js_afterSrl := by
    unfold JoltISA.srlProgramAuto
    rw [JoltISA.isX0_eq_false_of_ne_zero hrd]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (BitVec.ofNat 7 40 : JoltISA.VReg) = JoltISA.inlineTmp0 by rfl]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterBitmask h_bitmask_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterBitmask js_afterSrl
      h_virtual_srl_succeeds]
    rfl

  refine ⟨js_afterSrl, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SRL value.
  have h_final_jolt_value :
      js_afterSrl.sail = stateAfterWrite js.sail rd jolt_val := by
    change js_afterSrl.sail = stateAfterWrite js.sail rd jolt_val
    exact h_virtual_srl_writes_jolt_val

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's two-instruction value is Sail's SRL value.
  have h_srl_value :
      jolt_val = srl_sail_operation v1 v2 := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact srl_value_eq_sail v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_srl_value]
  exact h_final_jolt_value

/-- `SRL` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem srlProgramAuto_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.srlProgramAuto rd rs1 rs2)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.srlProgramAuto rd rs1 rs2) := by
    unfold JoltISA.srlProgramAuto
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

/-- Main program-level statement for `SRL`. -/
def srlProgramEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.srlProgramAuto rd rs1 rs2)).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SRL).run js.sail

/-- Main program-level theorem for `SRL`: projected Sail behavior matches, and
the Jolt run preserves every protected Jolt register address. Scratch registers
allocated by the SRL expansion are deliberately outside the protected
predicate. -/
theorem srlProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    srlProgramEqSailStatement rs2 rs1 rd js h := by
  unfold srlProgramEqSailStatement
  let v1 := h.rs1_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail := h.rs1_read
  let v2 := h.rs2_val
  have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail := h.rs2_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.srlProgramAuto
    rw [JoltISA.isX0_regidx_zero]
    simp only [↓reduceIte]
    have hzero := JoltISA.pureWritebackRdZeroProgram_run js
    unfold JoltISA.pureWritebackRdZeroProgram at hzero
    rw [hzero]
    simp only [System.systemProjectResult]
    rw [h_project_initial]
    rw [execute_RTYPE_SRL_factored rs2 rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterSrl, h_program_succeeds, h_final_sail⟩ :=
    srlProgramAuto_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd
  have h_projected_vregs :
      Projection.ProjectedVRegsPreserved js js_afterSrl :=
    srlProgramAuto_preserves_projected_vregs rs2 rs1 rd h_program_succeeds

  rw [h_program_succeeds]
  simp only [System.systemProjectResult]

  rw [execute_RTYPE_SRL_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  obtain ⟨s', h_write⟩ := wX_shape rd (srl_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1

  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_afterSrl rd (srl_sail_operation v1 v2)
    h_final_sail h_projected_vregs]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (srl_sail_operation v1 v2)
    js.sail s' h_write).symm

end
