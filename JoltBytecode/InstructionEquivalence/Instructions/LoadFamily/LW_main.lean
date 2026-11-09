import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.FloorLoad
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualWindowMask
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Windows
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LW_SailSide
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.ProofSupport.StateLemmas
import Mathlib.Tactic.IntervalCases

open LeanRV64D

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LW_main

abbrev Vreg x := BitVec.ofNat 7 x

/-- **Main program theorem for LW.** The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
def lwProgramEqSailStatement (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : LoadProgramEqSailAssumptions imm rs1 js) : Prop :=
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.lwProgramAuto rd rs1 imm)).run js) =
    (execute_LOAD imm rs1 rd false 4).run js.sail

/-- Signed PEXT with the generated word-window mask extracts the selected word
and sign-extends it to 64 bits. -/
theorem pext_signed_word_window
    (dval : BitVec 64) (base : BitVec 64) (imm : BitVec 12)
    (hAlign :
      load_effective_address base imm &&& (3 : BitVec 64) = 0) :
    jolt_virtual_pext_signed_value dval
        (jolt_virtual_window_mask_w_value base imm) =
      sign_extend (m := 64)
        (word_of_dword dval
          (load_effective_address base imm &&& (7 : BitVec 64)).toNat) := by
  -- We already have a generic lemma that does all the heavy lifting for us.
  exact window_mask_w_pext_signed
    (d := dval)
    (base := base)
    (imm := imm)
    (halign := hAlign)

/-- An LD whose scratch source already holds the aligned address replaces it
with the containing doubleword.
For example, a scratch register containing address 8 receives the word at 8. -/
theorem lw_ld_run
    (dwordVReg : JoltISA.VReg) (hWritable : WritableVReg dwordVReg)
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let facts := h.dwordWindowFacts
    let jsAlign :=
      stateAfterVRegWrite js dwordVReg
        (jolt_virtual_align_addr_value h.rs1_val imm)
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    (JoltISA.execInstr
      (JoltISA.Encoded.LD .normal (.vreg dwordVReg) (.vreg dwordVReg)
        (0 : BitVec 12))).run jsAlign =
      .ok RETIRE_SUCCESS
        (stateAfterVRegWrite jsAlign dwordVReg dval) := by
  apply vreg_LD_run_of_aligned_dword_phys
  · simp only [stateAfterVRegWrite, if_true, jolt_virtual_align_addr_value, JoltISA.addWide_low,
      compute_aligned_dword_base_address, load_effective_address,
      Memory.effectiveAddr12,
      show ~~~(7 : BitVec 64) = (-8 : BitVec 64) by decide]
  · exact h.cur_privilege
  · exact h.mstatus_mprv
  · exact h.dwordWindowFacts.aligned
  · exact h.dwordWindowFacts.load_pmp
  · exact h.dwordWindowFacts.read_mmio
  · exact hWritable
  · exact ⟨h.jolt_ram.below_heap_end⟩

/-- The second LW instruction writes the word-window mask to its chosen
scratch virtual register. -/
theorem lw_virtual_window_mask_w_run
    (dwordVReg maskVReg : JoltISA.VReg)
    (hWritable : WritableVReg maskVReg)
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite js dwordVReg dval
    let maskValue := jolt_virtual_window_mask_w_value h.rs1_val imm
    (JoltISA.execInstr
      (JoltISA.Encoded.VirtualWindowMaskW (.vreg maskVReg) (.xreg rs1) imm)).run jsLoad =
      .ok RETIRE_SUCCESS
        (stateAfterVRegWrite jsLoad maskVReg maskValue) := by
  apply JoltISA.virtual_window_mask_w_run_vreg_xreg
  · simpa only [stateAfterVRegWrite] using h.rs1_read
  · exact hWritable

/-- The final instruction of the non-`x0` LW expansion writes the signed
parallel-extract result to the architectural destination register. -/
theorem lw_virtual_pext_signed_rd_run
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite js (Vreg 40) dval
    let maskValue := jolt_virtual_window_mask_w_value h.rs1_val imm
    let jsMask := stateAfterVRegWrite jsLoad (Vreg 41) maskValue
    let pextValue := jolt_virtual_pext_signed_value dval maskValue
    (JoltISA.execInstr
      (.VirtualPextSigned
        (.xreg rd) (.vreg (Vreg 40)) (.vreg (Vreg 41)))).run jsMask =
      .ok RETIRE_SUCCESS
        { jsMask with
          sail := stateAfterWrite jsMask.sail rd pextValue } := by
  apply JoltISA.virtual_pext_signed_run_xreg_vreg_vreg
  simpa only [stateAfterVRegWrite, Vreg, BitVec.reduceEq, ↓reduceIte] using
    wX_bits_stateAfterWrite
      (rd := rd)
      (v := _)
      (s := js.sail)

/-- The final instruction of the `x0` LW expansion writes the signed
parallel-extract result to virtual register 40. -/
theorem lw_virtual_pext_signed_v40_run
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite js (Vreg 41) dval
    let maskValue := jolt_virtual_window_mask_w_value h.rs1_val imm
    let jsMask := stateAfterVRegWrite jsLoad (Vreg 42) maskValue
    let pextValue := jolt_virtual_pext_signed_value dval maskValue
    (JoltISA.execInstr
      (.VirtualPextSigned
        (.vreg (Vreg 40)) (.vreg (Vreg 41)) (.vreg (Vreg 42)))).run jsMask =
      .ok RETIRE_SUCCESS
        (stateAfterVRegWrite jsMask (Vreg 40) pextValue) := by
  apply JoltISA.virtual_pext_signed_run_vreg_vreg_vreg
  simp only [WritableVReg, Vreg, BitVec.toNat_ofNat]
  norm_num

/-- The generated `LW` expansion writes only instruction-local scratch vregs. -/
theorem lwProgramAuto_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.lwProgramAuto rd rs1 imm)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.lwProgramAuto rd rs1 imm) := by
    unfold JoltISA.lwProgramAuto
    split <;>
      simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
        and_true] <;>
      norm_num [JoltISA.IsProtectedJoltRegister, JoltISA.joltRegisterSlot,
        JoltISA.JoltRegisterSlot.isProtected]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- After the aligned non-`x0` generated `LW` branch runs, `systemProject`
agrees with the embedded Sail state. -/
theorem lwProgramAuto_systemProject_eq_sail
    (imm : BitVec 12) (rs1 rd : regidx)
    (js js' : SailJoltState) (value : BitVec 64)
    (hlinked : LinkedCSRs js)
    (hrun : (JoltISA.execProgram (JoltISA.lwProgramAuto rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS js')
    (hsail : js'.sail = stateAfterWrite js.sail rd value) :
    System.systemProject js' = js'.sail := by
  have hprojected : Projection.ProjectedVRegsPreserved js js' :=
    lwProgramAuto_preserves_projected_vregs
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

/-- The aligned non-`x0` generated expansion runs through its five
instructions to the explicit final state used by the equivalence proof. -/
theorem lwProgramAuto_nonzero_run
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (3 : BitVec 64) = 0)
    (hx0 : JoltISA.isX0 rd ≠ true) :
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite js (Vreg 40) dval
    let maskValue := jolt_virtual_window_mask_w_value h.rs1_val imm
    let jsMask := stateAfterVRegWrite jsLoad (Vreg 41) maskValue
    let pextValue := jolt_virtual_pext_signed_value dval maskValue
    let jsPext :=
      { jsMask with sail := stateAfterWrite jsMask.sail rd pextValue }
    (JoltISA.execProgram (JoltISA.lwProgramAuto rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS jsPext := by
  simp only [JoltISA.lwProgramAuto, if_neg hx0]
  change JoltISA.Program.Run
    (JoltISA.laneWindowOpen .word (.vreg (Vreg 40)) (.vreg (Vreg 41))
      (.xreg rs1) (sign_extend (m := 64) imm) .normal (ExceptionType.E_Load_Addr_Align ())
      (JoltISA.laneWindowExtract (.vreg (Vreg 40)) (.vreg (Vreg 41)) (.xreg rd) true
        (.done RETIRE_SUCCESS))) js _
  exact LoadFamily.threeRows_run
    (LoadFamily.floorLoad_of_assumptions .word (Vreg 40)
      (by unfold WritableVReg; decide) imm rs1 js h hAlign)
    (lw_virtual_window_mask_w_run (Vreg 40) (Vreg 41) (by unfold WritableVReg; decide) imm rs1 js h)
    (lw_virtual_pext_signed_rd_run imm rs1 rd js h)

/-- The aligned path through the non-`x0` branch of the main LW program
theorem. -/
theorem lwProgram_eq_sail_nonzero_aligned
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (3 : BitVec 64) = 0)
    (hx0 : JoltISA.isX0 rd ≠ true) :
    lwProgramEqSailStatement imm rs1 rd js h := by
  unfold lwProgramEqSailStatement
  let facts := h.dwordWindowFacts
  let daddr := compute_aligned_dword_base_address h.rs1_val imm
  let dval := loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
  let jsLoad := stateAfterVRegWrite js (Vreg 40) dval
  let maskValue := jolt_virtual_window_mask_w_value h.rs1_val imm
  let jsMask := stateAfterVRegWrite jsLoad (Vreg 41) maskValue
  let pextValue := jolt_virtual_pext_signed_value dval maskValue
  let jsPext :=
    { jsMask with sail := stateAfterWrite jsMask.sail rd pextValue }
  have hjolt :
      (JoltISA.execProgram (JoltISA.lwProgramAuto rd rs1 imm)).run js =
        .ok RETIRE_SUCCESS jsPext := by
    exact lwProgramAuto_nonzero_run
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
    lwProgramAuto_systemProject_eq_sail
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
  rw [LW_SailSide.execute_LW_reduces
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)
    (hAlign := hAlign)]
  rw [LW_SailSide.stateAfterWrite_writeValue_eq_dword_word
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)
    (hAlign := hAlign)]

  -- NOTE: Math lemma
  rw [← pext_signed_word_window
    (dval := dval)
    (base := h.rs1_val)
    (imm := imm)
    (hAlign := hAlign)]
  simp only [System.systemProjectResult]
  rw [hProject, hFinalSail]

/-- A misaligned generated LW expansion stops at its first instruction with
the load-address-alignment exception, independently of its destination. -/
theorem lwProgramAuto_misaligned_run
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hMisaligned :
      load_effective_address h.rs1_val imm &&& (3 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram (JoltISA.lwProgramAuto rd rs1 imm)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address h.rs1_val imm),
          ExceptionType.E_Load_Addr_Align ())) js := by
  unfold JoltISA.lwProgramAuto
  split <;>
    exact LoadFamily.floorLoadBlock_misaligned .word _ _ rs1 _ h.rs1_val
      .normal (ExceptionType.E_Load_Addr_Align ()) js h.rs1_read hMisaligned

/-- The misaligned path through the non-`x0` branch of the main LW program
theorem. -/
theorem lwProgram_eq_sail_nonzero_misaligned
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hMisaligned :
      load_effective_address h.rs1_val imm &&& (3 : BitVec 64) ≠ 0)
    (hx0 : JoltISA.isX0 rd ≠ true) :
    lwProgramEqSailStatement imm rs1 rd js h := by
  unfold lwProgramEqSailStatement
  have hjolt := lwProgramAuto_misaligned_run
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)
    (hMisaligned := hMisaligned)
  have hsail := LW_SailSide.execute_LW_misaligned
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

/-- The complete non-`x0` branch of the main LW program theorem. -/
theorem lwProgram_eq_sail_nonzero
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hx0 : JoltISA.isX0 rd ≠ true) :
    lwProgramEqSailStatement imm rs1 rd js h := by
  by_cases hAlign :
      load_effective_address h.rs1_val imm &&& (3 : BitVec 64) = 0
  · exact lwProgram_eq_sail_nonzero_aligned
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hAlign := hAlign)
      (hx0 := hx0)
  · exact lwProgram_eq_sail_nonzero_misaligned
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hMisaligned := hAlign)
      (hx0 := hx0)

/-- The aligned `x0` generated expansion runs through its three instructions
to the explicit final state used by the equivalence proof. -/
theorem lwProgramAuto_x0_run
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (3 : BitVec 64) = 0)
    (hx0 : JoltISA.isX0 rd = true) :
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite js (Vreg 41) dval
    let maskValue := jolt_virtual_window_mask_w_value h.rs1_val imm
    let jsMask := stateAfterVRegWrite jsLoad (Vreg 42) maskValue
    let pextValue := jolt_virtual_pext_signed_value dval maskValue
    let jsPext := stateAfterVRegWrite jsMask (Vreg 40) pextValue
    (JoltISA.execProgram (JoltISA.lwProgramAuto rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS jsPext := by
  simp only [JoltISA.lwProgramAuto, hx0, if_true]
  change JoltISA.Program.Run
    (JoltISA.laneWindowOpen .word (.vreg (Vreg 41)) (.vreg (Vreg 42))
      (.xreg rs1) (sign_extend (m := 64) imm) .normal (ExceptionType.E_Load_Addr_Align ())
      (JoltISA.laneWindowExtract (.vreg (Vreg 41)) (.vreg (Vreg 42)) (.vreg (Vreg 40)) true
        (.done RETIRE_SUCCESS))) js _
  exact LoadFamily.threeRows_run
    (LoadFamily.floorLoad_of_assumptions .word (Vreg 41)
      (by unfold WritableVReg; decide) imm rs1 js h hAlign)
    (lw_virtual_window_mask_w_run (Vreg 41) (Vreg 42) (by unfold WritableVReg; decide) imm rs1 js h)
    (lw_virtual_pext_signed_v40_run imm rs1 js h)

/-- The aligned path through the `x0` branch of the main LW program theorem. -/
theorem lwProgram_eq_sail_x0_aligned
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hAlign :
      load_effective_address h.rs1_val imm &&& (3 : BitVec 64) = 0)
    (hx0 : JoltISA.isX0 rd = true) :
    lwProgramEqSailStatement imm rs1 rd js h := by
  unfold lwProgramEqSailStatement
  let facts := h.dwordWindowFacts
  let daddr := compute_aligned_dword_base_address h.rs1_val imm
  let dval := loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
  let jsLoad := stateAfterVRegWrite js (Vreg 41) dval
  let maskValue := jolt_virtual_window_mask_w_value h.rs1_val imm
  let jsMask := stateAfterVRegWrite jsLoad (Vreg 42) maskValue
  let pextValue := jolt_virtual_pext_signed_value dval maskValue
  let jsPext := stateAfterVRegWrite jsMask (Vreg 40) pextValue
  have hjolt :
      (JoltISA.execProgram (JoltISA.lwProgramAuto rd rs1 imm)).run js =
        .ok RETIRE_SUCCESS jsPext := by
    exact lwProgramAuto_x0_run
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
    lwProgramAuto_systemProject_eq_sail
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
  rw [LW_SailSide.execute_LW_reduces
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)
    (hAlign := hAlign)]
  rw [LW_SailSide.stateAfterWrite_writeValue_eq_dword_word
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)
    (hAlign := hAlign)]

  -- NOTE: Math lemma
  rw [← pext_signed_word_window
    (dval := dval)
    (base := h.rs1_val)
    (imm := imm)
    (hAlign := hAlign)]
  simp only [System.systemProjectResult]
  rw [hProject, hFinalSail]

/-- The misaligned path through the `x0` branch of the main LW program
theorem. -/
theorem lwProgram_eq_sail_x0_misaligned
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hMisaligned :
      load_effective_address h.rs1_val imm &&& (3 : BitVec 64) ≠ 0)
    (hx0 : JoltISA.isX0 rd = true) :
    lwProgramEqSailStatement imm rs1 rd js h := by
  unfold lwProgramEqSailStatement
  have hjolt := lwProgramAuto_misaligned_run
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)
    (hMisaligned := hMisaligned)
  have hsail := LW_SailSide.execute_LW_misaligned
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

/-- The complete `x0` branch of the main LW program theorem. -/
theorem lwProgram_eq_sail_x0
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hx0 : JoltISA.isX0 rd = true) :
    lwProgramEqSailStatement imm rs1 rd js h := by
  by_cases hAlign :
      load_effective_address h.rs1_val imm &&& (3 : BitVec 64) = 0
  · exact lwProgram_eq_sail_x0_aligned
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hAlign := hAlign)
      (hx0 := hx0)
  · exact lwProgram_eq_sail_x0_misaligned
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hMisaligned := hAlign)
      (hx0 := hx0)

/-- **Main program theorem for LW.** The structured Jolt-ISA expansion matches
Sail after materializing Jolt's persistent CSR virtual registers. -/
theorem lwProgram_eq_sail
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    lwProgramEqSailStatement imm rs1 rd js h := by
  by_cases hx0 : JoltISA.isX0 rd = true
  · exact lwProgram_eq_sail_x0
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hx0 := hx0)
  · exact lwProgram_eq_sail_nonzero
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hx0 := hx0)

end LW_main
