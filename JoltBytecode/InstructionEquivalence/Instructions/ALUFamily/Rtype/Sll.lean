import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.Mul
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualPow2
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.JoltISA.Values

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# SLL: Jolt VirtualPow2 + MUL = Sail SLL

Jolt program sequence:
1. `VirtualPow2 v0, rs2` — compute `2^(rs2[5:0])`
2. `MUL rd, rs1, v0` — multiply by power of two

Multiply-by-`2^s` = left-shift-by-`s`; the bridge fact is inlined here
because it is SLL-specific (not shared with other shift instructions).
-/

private theorem setWidth_eq_extractLsb
    (v : BitVec 64) :
    v.setWidth 6 = Sail.BitVec.extractLsb v (LeanRV64D.Functions.log2_xlen -i 1) 0 := by
  unfold Sail.BitVec.extractLsb
  ext i hi
  simp only [BitVec.getElem_setWidth]
  change v.getLsbD i =
    (BitVec.extractLsb (LeanRV64D.Functions.log2_xlen -i 1) 0 v).getLsbD i
  simp only [BitVec.getLsbD_extractLsb]
  have hlt : i < (LeanRV64D.Functions.log2_xlen -i 1) - 0 + 1 := by
    norm_num [LeanRV64D.Functions.log2_xlen] at hi ⊢
    omega
  simp only [hlt, decide_true, Bool.true_and, Nat.zero_add]

private theorem mul_pow2_eq_shiftLeft
    (v : BitVec 64)
    (s : BitVec 6) :
    v * BitVec.ofNat 64 (2 ^ s.toNat) = v <<< s := by
  exact (shiftLeft_eq_mul_pow2 v s.toNat).symm

private theorem sll_mul_eq_shift
    (v1 : BitVec 64)
    (v2 : BitVec 64) :
    v1 * BitVec.ofNat 64 (2 ^ (v2.setWidth 6).toNat) =
    shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0) := by
  unfold shift_bits_left
  rw [← setWidth_eq_extractLsb]
  exact mul_pow2_eq_shiftLeft v1 (v2.setWidth 6)

abbrev sll_sail_operation (v1 v2 : BitVec 64) : BitVec 64 :=
  shift_bits_left v1 (Sail.BitVec.extractLsb v2 (LeanRV64D.Functions.log2_xlen -i 1) 0)

abbrev sll_jolt_val (v1 v2 : BitVec 64) : BitVec 64 :=
  v1 * jolt_virtual_pow2_value v2

private theorem sll_value_eq_sail (v1 v2 : BitVec 64) :
    sll_jolt_val v1 v2 = sll_sail_operation v1 v2 := by
  simp only [sll_jolt_val, sll_sail_operation]
  dsimp only [jolt_virtual_pow2_value]
  rw [sll_mul_eq_shift]

theorem execute_RTYPE_SLL_factored
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx) :
    execute_RTYPE rs2 rs1 rd rop.SLL = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sll_sail_operation v1 v2)
      pure RETIRE_SUCCESS) := by
  simp only [execute_RTYPE]
  simp only [bind_pure_comp]
  simp only [map_eq_pure_bind]
  simp only [bind_assoc]
  simp only [pure_bind, sll_sail_operation]

/-- Program-level concrete theorem for `SLL`.

The explicit Jolt-ISA program first writes `VirtualPow2 rs2` to scratch `v0`,
then multiplies `rs1` by that scratch value.  The arithmetic bridge below
identifies multiplication by `2^rs2[5:0]` with Sail's left shift. -/
theorem sllProgramAuto_concrete
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (v1 v2 : BitVec 64)
    (h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail)
    (h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail)
    (hrd : rd ≠ regidx.Regidx 0) :
    ∃ (js' : SailJoltState),
      (JoltISA.execProgram (JoltISA.sllProgramAuto rd rs1 rs2)).run js =
          .ok RETIRE_SUCCESS js' ∧
        js'.sail = stateAfterWrite js.sail rd (sll_sail_operation v1 v2) := by
  -- Instruction 1: `VirtualPow2 v0, rs2` writes `2 ^ rs2[5:0]` to `v0`.
  let pow2 := jolt_virtual_pow2_value v2
  obtain ⟨js_afterPow2, h_pow2_reads_rs2, h_pow2_keeps_sail,
      h_pow2_writes_pow2, _, h_pow2_succeeds⟩ :=
    JoltISA.exists_state_after_virtual_pow2_run_vreg_xreg
      JoltISA.inlineTmp0 rs2 js v2 h_read_rs2
      (by unfold WritableVReg; decide)

  -- Instruction 2: `MUL rd, rs1, v0` writes the shifted result to `rd`.
  let jolt_val := sll_jolt_val v1 v2
  obtain ⟨js_afterMul, h_mul_reads_rs1, h_mul_writes_jolt_val, h_mul_succeeds⟩ :=
    JoltISA.exists_state_after_mul_run_xreg_xreg_vreg_of_value
      rd rs1 JoltISA.inlineTmp0 js_afterPow2 js.sail v1 pow2
      h_pow2_keeps_sail h_read_rs1 h_pow2_writes_pow2

  have h_program_succeeds :
      (JoltISA.execProgram (JoltISA.sllProgramAuto rd rs1 rs2)).run js =
        .ok RETIRE_SUCCESS js_afterMul := by
    unfold JoltISA.sllProgramAuto
    rw [JoltISA.isX0_eq_false_of_ne_zero hrd]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (BitVec.ofNat 7 40 : JoltISA.VReg) = JoltISA.inlineTmp0 by rfl]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterPow2 h_pow2_succeeds]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_afterPow2 js_afterMul h_mul_succeeds]
    rfl

  refine ⟨js_afterMul, h_program_succeeds, ?_⟩

  -- The instruction trace leaves `rd` containing the Jolt SLL value.
  have h_final_jolt_value :
      js_afterMul.sail = stateAfterWrite js.sail rd jolt_val := by
    change js_afterMul.sail = stateAfterWrite js.sail rd jolt_val
    exact h_mul_writes_jolt_val

  -- No more execution reasoning remains.
  -- The only real content left is the pure value equality:
  -- Jolt's two-instruction value is Sail's SLL value.
  have h_sll_value :
      jolt_val = sll_sail_operation v1 v2 := by
    simp only [jolt_val]
    -- NOTE: The core math theorem.
    exact sll_value_eq_sail v1 v2

  -- After the value theorem, the final state claim is mechanical.
  rw [← h_sll_value]
  exact h_final_jolt_value

/-- `SLL` never writes the persistent CSR virtual registers materialized by
`systemProject`. -/
theorem sllProgramAuto_preserves_projected_vregs
    (rs2 rs1 rd : regidx)
    {js js' : SailJoltState}
    {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.sllProgramAuto rd rs1 rs2)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe :
      JoltISA.ProgramWritesNoProtectedVReg
        (JoltISA.sllProgramAuto rd rs1 rs2) := by
    unfold JoltISA.sllProgramAuto
    split
    · simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg,
        JoltISA.DstWritesNoProtectedVReg,
        and_true]
    · rw [show (BitVec.ofNat 7 40 : JoltISA.VReg) = JoltISA.inlineTmp0 by rfl]
      simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg,
        JoltISA.DstWritesNoProtectedVReg,
        and_true]
      exact JoltISA.inlineTmp0_not_protected
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    (js := js) (js' := js') (result := result) hsafe hrun

/-- Main program-level equivalence for `SLL`. -/
def sllProgramEqSailStatement
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.sllProgramAuto rd rs1 rs2)).run js) =
    (execute_RTYPE rs2 rs1 rd rop.SLL).run js.sail

/-- Main program-level equivalence for `SLL`. -/
theorem sllProgram_eq_sail
    (rs2 : regidx)
    (rs1 : regidx)
    (rd : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    sllProgramEqSailStatement rs2 rs1 rd js h := by
  unfold sllProgramEqSailStatement
  let v1 := h.rs1_val
  have h_read_rs1 : rX_bits rs1 js.sail = .ok v1 js.sail := h.rs1_read
  let v2 := h.rs2_val
  have h_read_rs2 : rX_bits rs2 js.sail = .ok v2 js.sail := h.rs2_read
  have h_project_initial : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs
  by_cases hrd : rd = regidx.Regidx 0
  · subst rd
    unfold JoltISA.sllProgramAuto
    rw [JoltISA.isX0_regidx_zero]
    simp only [↓reduceIte]
    have hzero := JoltISA.pureWritebackRdZeroProgram_run js
    unfold JoltISA.pureWritebackRdZeroProgram at hzero
    rw [hzero]
    simp only [System.systemProjectResult]
    rw [h_project_initial]
    rw [execute_RTYPE_SLL_factored rs2 rs1 (regidx.Regidx 0)]
    simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
    simp only [h_read_rs1, h_read_rs2]
    simp only [wX_bits_regidx_zero]

  obtain ⟨js_afterMul, h_program_succeeds, h_final_sail⟩ :=
    sllProgramAuto_concrete rs2 rs1 rd js v1 v2 h_read_rs1 h_read_rs2 hrd
  have h_projected_vregs :
      Projection.ProjectedVRegsPreserved js js_afterMul :=
    sllProgramAuto_preserves_projected_vregs rs2 rs1 rd h_program_succeeds

  rw [h_program_succeeds]
  simp only [System.systemProjectResult]

  rw [execute_RTYPE_SLL_factored rs2 rs1 rd]
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure]
  simp only [h_read_rs1, h_read_rs2]

  obtain ⟨s', h_write⟩ := wX_shape rd (sll_sail_operation v1 v2) js.sail
  simp only [h_write]
  congr 1

  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    js js_afterMul rd (sll_sail_operation v1 v2)
    h_final_sail h_projected_vregs]
  rw [h_project_initial]
  exact (wX_bits_eq_stateAfterWrite rd (sll_sail_operation v1 v2)
    js.sail s' h_write).symm

end
