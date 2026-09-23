import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LH_main

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LHU_main

abbrev Vreg x := LH_main.Vreg x

/-- **Main program theorem for LHU.** The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
def lhuProgramEqSailStatement (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : LoadProgramEqSailAssumptions imm rs1 js) : Prop :=
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.lhuProgramAuto rd rs1 imm)).run js) =
    (execute_LOAD imm rs1 rd true 2).run js.sail

-- The alignment, aligned dword load, and halfword mask are the same as LH.
-- Only the final extraction is unsigned: VirtualPext zero-extends the selected
-- 16-bit halfword.

/-- Unsigned PEXT with the generated halfword-window mask extracts the selected
halfword and zero-extends it to 64 bits. -/
theorem pext_halfword_window
    (dval : BitVec 64) (base : BitVec 64) (imm : BitVec 12)
    (hAlign :
      load_effective_address base imm &&& (1 : BitVec 64) = 0) :
    jolt_virtual_pext_value dval
        (jolt_virtual_window_mask_h_value base imm) =
      zero_extend (m := 64)
        (halfword_of_dword dval
          (load_effective_address base imm &&& (7 : BitVec 64)).toNat) := by
  exact window_mask_h_pext
    (d := dval)
    (base := base)
    (imm := imm)
    (halign := hAlign)

/-- The final instruction of the non-`x0` LHU expansion writes the unsigned
parallel-extract result to the architectural destination register. -/
theorem lhu_virtual_pext_rd_run
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let jsAlign := stateAfterVRegWrite js (Vreg 41)
      (jolt_virtual_align_addr_value h.rs1_val imm)
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite jsAlign (Vreg 41) dval
    let maskValue := jolt_virtual_window_mask_h_value h.rs1_val imm
    let jsMask := stateAfterVRegWrite jsLoad (Vreg 40) maskValue
    let pextValue := jolt_virtual_pext_value dval maskValue
    (JoltISA.execInstr
      (.VirtualPext
        (.xreg rd) (.vreg (Vreg 41)) (.vreg (Vreg 40)))).run jsMask =
      .ok RETIRE_SUCCESS
        { jsMask with
          sail := stateAfterWrite jsMask.sail rd pextValue } := by
  apply JoltISA.virtual_pext_run_xreg_vreg_vreg
  simpa only [stateAfterVRegWrite, Vreg, LH_main.Vreg, LW_main.Vreg,
    BitVec.reduceEq, ↓reduceIte] using
    wX_bits_stateAfterWrite
      (rd := rd)
      (v := _)
      (s := js.sail)

/-- The final instruction of the `x0` LHU expansion writes the unsigned
parallel-extract result to virtual register 40. -/
theorem lhu_virtual_pext_v40_run
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let jsAlign := stateAfterVRegWrite js (Vreg 42)
      (jolt_virtual_align_addr_value h.rs1_val imm)
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite jsAlign (Vreg 42) dval
    let maskValue := jolt_virtual_window_mask_h_value h.rs1_val imm
    let jsMask := stateAfterVRegWrite jsLoad (Vreg 41) maskValue
    let pextValue := jolt_virtual_pext_value dval maskValue
    (JoltISA.execInstr
      (.VirtualPext
        (.vreg (Vreg 40)) (.vreg (Vreg 42)) (.vreg (Vreg 41)))).run jsMask =
      .ok RETIRE_SUCCESS
        (stateAfterVRegWrite jsMask (Vreg 40) pextValue) := by
  apply JoltISA.virtual_pext_run_vreg_vreg_vreg
  simp only [WritableVReg, Vreg, LH_main.Vreg, LW_main.Vreg,
    BitVec.toNat_ofNat]
  norm_num

/-- The generated `LHU` expansion writes only instruction-local scratch
vregs. -/
theorem lhuProgramAuto_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.lhuProgramAuto rd rs1 imm)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.lhuProgramAuto rd rs1 imm) := by
    unfold JoltISA.lhuProgramAuto
    split <;>
      simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
        JoltISA.sideEffectingDst, and_true] <;>
      norm_num [JoltISA.IsProtectedJoltRegister, JoltISA.joltRegisterSlot,
        JoltISA.JoltRegisterSlot.isProtected]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- After either generated `LHU` destination branch retires, `systemProject`
agrees with the embedded Sail state. -/
theorem lhuProgramAuto_systemProject_eq_sail
    (imm : BitVec 12) (rs1 rd : regidx)
    (js js' : SailJoltState) (value : BitVec 64)
    (hlinked : LinkedCSRs js)
    (hrun : (JoltISA.execProgram (JoltISA.lhuProgramAuto rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS js')
    (hsail : js'.sail = stateAfterWrite js.sail rd value) :
    System.systemProject js' = js'.sail := by
  have hprojected : Projection.ProjectedVRegsPreserved js js' :=
    lhuProgramAuto_preserves_projected_vregs
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (hrun := hrun)
  rw [Projection.systemProject_stateAfterWrite_of_projected_vregs_preserved
    (before := js)
    (after := js')
    (rd := rd)
    (value := value)
    (hsail := hsail)
    (hprojected := hprojected)]
  rw [Projection.systemProject_eq_sail_of_compatible
    (js := js)
    (h := hlinked)]
  rw [← hsail]

/-- The aligned non-`x0` generated LHU expansion runs to its explicit final
state. The first four instruction facts are reused directly from LH/LW. -/
theorem lhuProgramAuto_nonzero_run
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0)
    (hx0 : JoltISA.isX0 rd ≠ true) :
    let jsAlign := stateAfterVRegWrite js (Vreg 41)
      (jolt_virtual_align_addr_value h.rs1_val imm)
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite jsAlign (Vreg 41) dval
    let maskValue := jolt_virtual_window_mask_h_value h.rs1_val imm
    let jsMask := stateAfterVRegWrite jsLoad (Vreg 40) maskValue
    let pextValue := jolt_virtual_pext_value dval maskValue
    let jsPext :=
      { jsMask with sail := stateAfterWrite jsMask.sail rd pextValue }
    (JoltISA.execProgram (JoltISA.lhuProgramAuto rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS jsPext := by
  simp only [JoltISA.lhuProgramAuto, if_neg hx0]
  have hv40 : WritableVReg (Vreg 40) := by
    simp only [WritableVReg, Vreg, LH_main.Vreg, LW_main.Vreg,
      BitVec.toNat_ofNat]
    norm_num
  have hv41 : WritableVReg (Vreg 41) := by
    simp only [WritableVReg, Vreg, LH_main.Vreg, LW_main.Vreg,
      BitVec.toNat_ofNat]
    norm_num

  let assertInstr : JoltISA.Instr :=
    JoltISA.Encoded.VirtualAssertHalfwordAlignment rs1 imm
      (ExceptionType.E_Load_Addr_Align ())
  rw [JoltISA.execProgram_instr_run_retire
    (instr := assertInstr)
    (rest := _)
    (js := js)
    (js' := js)
    (h := LH_main.lh_virtual_assert_halfword_alignment_run
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h)
      (hAlign := hAlign))]

  let jsAlign := stateAfterVRegWrite js (Vreg 41)
    (jolt_virtual_align_addr_value h.rs1_val imm)
  let alignInstr : JoltISA.Instr :=
    JoltISA.Encoded.VirtualAlignAddr (.vreg (Vreg 41)) (.xreg rs1) imm
  rw [JoltISA.execProgram_instr_run_retire
    (instr := alignInstr)
    (rest := _)
    (js := js)
    (js' := jsAlign)
    (h := LW_main.lw_virtual_align_addr_run
      (addrVReg := Vreg 41)
      (hWritable := hv41)
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h))]

  let facts := h.dwordWindowFacts
  let daddr := compute_aligned_dword_base_address h.rs1_val imm
  let dval := loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
  let jsLoad := stateAfterVRegWrite jsAlign (Vreg 41) dval
  let ldInstr : JoltISA.Instr :=
    JoltISA.Encoded.LD .normal (.vreg (Vreg 41)) (.vreg (Vreg 41)) (0 : BitVec 12)
  rw [JoltISA.execProgram_instr_run_retire
    (instr := ldInstr)
    (rest := _)
    (js := jsAlign)
    (js' := jsLoad)
    (h := LW_main.lw_ld_run
      (dwordVReg := Vreg 41)
      (hWritable := hv41)
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h))]

  let maskValue := jolt_virtual_window_mask_h_value h.rs1_val imm
  let jsMask := stateAfterVRegWrite jsLoad (Vreg 40) maskValue
  let maskInstr : JoltISA.Instr :=
    JoltISA.Encoded.VirtualWindowMaskH (.vreg (Vreg 40)) (.xreg rs1) imm
  rw [JoltISA.execProgram_instr_run_retire
    (instr := maskInstr)
    (rest := _)
    (js := jsLoad)
    (js' := jsMask)
    (h := LH_main.lh_virtual_window_mask_h_run
      (dwordVReg := Vreg 41)
      (maskVReg := Vreg 40)
      (hWritable := hv40)
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h))]

  let pextValue := jolt_virtual_pext_value dval maskValue
  let jsPext :=
    { jsMask with sail := stateAfterWrite jsMask.sail rd pextValue }
  let pextInstr : JoltISA.Instr :=
    .VirtualPext (.xreg rd) (.vreg (Vreg 41)) (.vreg (Vreg 40))
  rw [JoltISA.execProgram_instr_run_retire
    (instr := pextInstr)
    (rest := _)
    (js := jsMask)
    (js' := jsPext)
    (h := lhu_virtual_pext_rd_run
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h))]
  simp only [JoltISA.execProgram, pure, EStateM.pure, EStateM.run]
  rfl

/-- The aligned path through the non-`x0` LHU branch. -/
theorem lhuProgram_eq_sail_nonzero_aligned
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0)
    (hx0 : JoltISA.isX0 rd ≠ true) :
    lhuProgramEqSailStatement imm rs1 rd js h := by
  unfold lhuProgramEqSailStatement
  let jsAlign := stateAfterVRegWrite js (Vreg 41)
    (jolt_virtual_align_addr_value h.rs1_val imm)
  let facts := h.dwordWindowFacts
  let daddr := compute_aligned_dword_base_address h.rs1_val imm
  let dval := loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
  let jsLoad := stateAfterVRegWrite jsAlign (Vreg 41) dval
  let maskValue := jolt_virtual_window_mask_h_value h.rs1_val imm
  let jsMask := stateAfterVRegWrite jsLoad (Vreg 40) maskValue
  let pextValue := jolt_virtual_pext_value dval maskValue
  let jsPext :=
    { jsMask with sail := stateAfterWrite jsMask.sail rd pextValue }
  have hjolt :
      (JoltISA.execProgram (JoltISA.lhuProgramAuto rd rs1 imm)).run js =
        .ok RETIRE_SUCCESS jsPext := by
    exact lhuProgramAuto_nonzero_run
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hAlign := hAlign)
      (hx0 := hx0)
  have hFinalSail :
      jsPext.sail = stateAfterWrite js.sail rd pextValue := by
    rfl
  have hProject : System.systemProject jsPext = jsPext.sail :=
    lhuProgramAuto_systemProject_eq_sail
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (js' := jsPext)
      (value := pextValue)
      (hlinked := h.linkedCSRs)
      (hrun := hjolt)
      (hsail := hFinalSail)

  rw [hjolt]
  rw [LH_SailSide.execute_LHU_reduces
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)
    (hAlign := hAlign)]
  rw [LH_SailSide.stateAfterWrite_writeValueUnsigned_eq_dword_halfword
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)
    (hAlign := hAlign)]

  -- NOTE: Math lemma
  rw [← pext_halfword_window
    (dval := dval)
    (base := h.rs1_val)
    (imm := imm)
    (hAlign := hAlign)]
  simp only [System.systemProjectResult]
  rw [hProject, hFinalSail]

/-- A misaligned generated LHU expansion stops at its first instruction with
the load-address-alignment exception, independently of its destination. -/
theorem lhuProgramAuto_misaligned_run
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hMisaligned :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram (JoltISA.lhuProgramAuto rd rs1 imm)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address h.rs1_val imm),
          ExceptionType.E_Load_Addr_Align ())) js := by
  unfold JoltISA.lhuProgramAuto
  split <;>
    exact LH_SailSide.assertHalfwordBlockMisaligned
      (tail := _)
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (val := h.rs1_val)
      (hrx := h.rs1_read)
      (hmis := hMisaligned)

/-- The misaligned LHU path is common to both destination branches. -/
theorem lhuProgram_eq_sail_misaligned
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hMisaligned :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) ≠ 0) :
    lhuProgramEqSailStatement imm rs1 rd js h := by
  unfold lhuProgramEqSailStatement
  have hjolt := lhuProgramAuto_misaligned_run
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)
    (hMisaligned := hMisaligned)
  have hsail := LH_SailSide.execute_LHU_misaligned
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)
    (hMisaligned := hMisaligned)
  have hProject : System.systemProject js = js.sail :=
    Projection.systemProject_eq_sail_of_compatible
      (js := js)
      (h := h.linkedCSRs)
  rw [hjolt, hsail]
  simp only [System.systemProjectResult]
  rw [hProject]

/-- The complete non-`x0` branch of the main LHU program theorem. -/
theorem lhuProgram_eq_sail_nonzero
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hx0 : JoltISA.isX0 rd ≠ true) :
    lhuProgramEqSailStatement imm rs1 rd js h := by
  by_cases hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0
  · exact lhuProgram_eq_sail_nonzero_aligned
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hAlign := hAlign)
      (hx0 := hx0)
  · exact lhuProgram_eq_sail_misaligned
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hMisaligned := hAlign)

/-- The aligned `x0` generated LHU expansion runs to its explicit final state.
The first four instruction facts are reused directly from LH/LW. -/
theorem lhuProgramAuto_x0_run
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0)
    (hx0 : JoltISA.isX0 rd = true) :
    let jsAlign := stateAfterVRegWrite js (Vreg 42)
      (jolt_virtual_align_addr_value h.rs1_val imm)
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite jsAlign (Vreg 42) dval
    let maskValue := jolt_virtual_window_mask_h_value h.rs1_val imm
    let jsMask := stateAfterVRegWrite jsLoad (Vreg 41) maskValue
    let pextValue := jolt_virtual_pext_value dval maskValue
    let jsPext := stateAfterVRegWrite jsMask (Vreg 40) pextValue
    (JoltISA.execProgram (JoltISA.lhuProgramAuto rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS jsPext := by
  simp only [JoltISA.lhuProgramAuto, hx0, if_true]
  have hv40 : WritableVReg (Vreg 40) := by
    simp only [WritableVReg, Vreg, LH_main.Vreg, LW_main.Vreg,
      BitVec.toNat_ofNat]
    norm_num
  have hv41 : WritableVReg (Vreg 41) := by
    simp only [WritableVReg, Vreg, LH_main.Vreg, LW_main.Vreg,
      BitVec.toNat_ofNat]
    norm_num
  have hv42 : WritableVReg (Vreg 42) := by
    simp only [WritableVReg, Vreg, LH_main.Vreg, LW_main.Vreg,
      BitVec.toNat_ofNat]
    norm_num

  let assertInstr : JoltISA.Instr :=
    JoltISA.Encoded.VirtualAssertHalfwordAlignment rs1 imm
      (ExceptionType.E_Load_Addr_Align ())
  rw [JoltISA.execProgram_instr_run_retire
    (instr := assertInstr)
    (rest := _)
    (js := js)
    (js' := js)
    (h := LH_main.lh_virtual_assert_halfword_alignment_run
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h)
      (hAlign := hAlign))]

  let jsAlign := stateAfterVRegWrite js (Vreg 42)
    (jolt_virtual_align_addr_value h.rs1_val imm)
  let alignInstr : JoltISA.Instr :=
    JoltISA.Encoded.VirtualAlignAddr (.vreg (Vreg 42)) (.xreg rs1) imm
  rw [JoltISA.execProgram_instr_run_retire
    (instr := alignInstr)
    (rest := _)
    (js := js)
    (js' := jsAlign)
    (h := LW_main.lw_virtual_align_addr_run
      (addrVReg := Vreg 42)
      (hWritable := hv42)
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h))]

  let facts := h.dwordWindowFacts
  let daddr := compute_aligned_dword_base_address h.rs1_val imm
  let dval := loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
  let jsLoad := stateAfterVRegWrite jsAlign (Vreg 42) dval
  let ldInstr : JoltISA.Instr :=
    JoltISA.Encoded.LD .normal (.vreg (Vreg 42)) (.vreg (Vreg 42)) (0 : BitVec 12)
  rw [JoltISA.execProgram_instr_run_retire
    (instr := ldInstr)
    (rest := _)
    (js := jsAlign)
    (js' := jsLoad)
    (h := LW_main.lw_ld_run
      (dwordVReg := Vreg 42)
      (hWritable := hv42)
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h))]

  let maskValue := jolt_virtual_window_mask_h_value h.rs1_val imm
  let jsMask := stateAfterVRegWrite jsLoad (Vreg 41) maskValue
  let maskInstr : JoltISA.Instr :=
    JoltISA.Encoded.VirtualWindowMaskH (.vreg (Vreg 41)) (.xreg rs1) imm
  rw [JoltISA.execProgram_instr_run_retire
    (instr := maskInstr)
    (rest := _)
    (js := jsLoad)
    (js' := jsMask)
    (h := LH_main.lh_virtual_window_mask_h_run
      (dwordVReg := Vreg 42)
      (maskVReg := Vreg 41)
      (hWritable := hv41)
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h))]

  let pextValue := jolt_virtual_pext_value dval maskValue
  let jsPext := stateAfterVRegWrite jsMask (Vreg 40) pextValue
  let pextInstr : JoltISA.Instr :=
    .VirtualPext
      (.vreg (Vreg 40)) (.vreg (Vreg 42)) (.vreg (Vreg 41))
  rw [JoltISA.execProgram_instr_run_retire
    (instr := pextInstr)
    (rest := _)
    (js := jsMask)
    (js' := jsPext)
    (h := lhu_virtual_pext_v40_run
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h))]
  simp only [JoltISA.execProgram, pure, EStateM.pure, EStateM.run]
  rfl

/-- The aligned path through the `x0` LHU branch. -/
theorem lhuProgram_eq_sail_x0_aligned
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0)
    (hx0 : JoltISA.isX0 rd = true) :
    lhuProgramEqSailStatement imm rs1 rd js h := by
  unfold lhuProgramEqSailStatement
  let jsAlign := stateAfterVRegWrite js (Vreg 42)
    (jolt_virtual_align_addr_value h.rs1_val imm)
  let facts := h.dwordWindowFacts
  let daddr := compute_aligned_dword_base_address h.rs1_val imm
  let dval := loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
  let jsLoad := stateAfterVRegWrite jsAlign (Vreg 42) dval
  let maskValue := jolt_virtual_window_mask_h_value h.rs1_val imm
  let jsMask := stateAfterVRegWrite jsLoad (Vreg 41) maskValue
  let pextValue := jolt_virtual_pext_value dval maskValue
  let jsPext := stateAfterVRegWrite jsMask (Vreg 40) pextValue
  have hjolt :
      (JoltISA.execProgram (JoltISA.lhuProgramAuto rd rs1 imm)).run js =
        .ok RETIRE_SUCCESS jsPext := by
    exact lhuProgramAuto_x0_run
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hAlign := hAlign)
      (hx0 := hx0)
  have hFinalSail :
      jsPext.sail = stateAfterWrite js.sail rd pextValue := by
    rw [JoltISA.stateAfterWrite_of_isX0_eq_true
      (rd := rd)
      (h := hx0)
      (s := js.sail)
      (val := pextValue)]
    rfl
  have hProject : System.systemProject jsPext = jsPext.sail :=
    lhuProgramAuto_systemProject_eq_sail
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (js' := jsPext)
      (value := pextValue)
      (hlinked := h.linkedCSRs)
      (hrun := hjolt)
      (hsail := hFinalSail)

  rw [hjolt]
  rw [LH_SailSide.execute_LHU_reduces
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)
    (hAlign := hAlign)]
  rw [LH_SailSide.stateAfterWrite_writeValueUnsigned_eq_dword_halfword
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)
    (hAlign := hAlign)]

  -- NOTE: Math lemma
  rw [← pext_halfword_window
    (dval := dval)
    (base := h.rs1_val)
    (imm := imm)
    (hAlign := hAlign)]
  simp only [System.systemProjectResult]
  rw [hProject, hFinalSail]

/-- The complete `x0` branch of the main LHU program theorem. -/
theorem lhuProgram_eq_sail_x0
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hx0 : JoltISA.isX0 rd = true) :
    lhuProgramEqSailStatement imm rs1 rd js h := by
  by_cases hAlign :
      load_effective_address h.rs1_val imm &&& (1 : BitVec 64) = 0
  · exact lhuProgram_eq_sail_x0_aligned
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hAlign := hAlign)
      (hx0 := hx0)
  · exact lhuProgram_eq_sail_misaligned
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hMisaligned := hAlign)

/-- **Main program theorem for LHU.** The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
theorem lhuProgram_eq_sail
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    lhuProgramEqSailStatement imm rs1 rd js h := by
  by_cases hx0 : JoltISA.isX0 rd = true
  · exact lhuProgram_eq_sail_x0
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hx0 := hx0)
  · exact lhuProgram_eq_sail_nonzero
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hx0 := hx0)

end LHU_main
