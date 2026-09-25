import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.JoltISA.ExpansionsAutomated
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Windows
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.LB_SailSide
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.ProofSupport.StateLemmas
import Mathlib.Tactic.IntervalCases

set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace LB_main

abbrev Vreg x := BitVec.ofNat 7 x

/-- **Main program theorem for LB.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
def lbProgramEqSailStatement (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : LoadProgramEqSailAssumptions imm rs1 js) : Prop :=
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.lbProgramAuto rd rs1 imm)).run js) =
    (execute_LOAD imm rs1 rd false 1).run js.sail

/-- The byte-window mask used by the pext instruction 
comes in two forms. 
This lemma helps use the version that makes proofs more ergonomic.
-/
theorem byte_window_mask_eq_contiguous (byteOffset : Nat) :
    BitVec.ofNat 64 (0xFF <<< (8 * byteOffset)) =
    BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ (8 * byteOffset)) := by
  simp only [Nat.shiftLeft_eq]
  norm_num

/-- Signed PEXT with an eight-bit window mask extracts the selected byte and
sign-extends it to 64 bits. -/
theorem pext_signed_byte_window
    (dval : BitVec 64) (byteOffset : Nat)
    (hOffset : byteOffset < 8) :
    jolt_virtual_pext_signed_value dval
      (BitVec.ofNat 64 (0xFF <<< (8 * byteOffset))) =
    sign_extend (m := 64) (byte_of_dword dval byteOffset) := by
  rw [byte_window_mask_eq_contiguous]
  -- We already have a generic lemma that does all the heavy 
  -- lifting for us
  rw [JoltISA.pext_signed_value_contiguous
    (x := dval)
    (offset := 8 * byteOffset)
    (width := 8)
    (hwidth := by omega)
    (hfit := by omega)]
  rfl

/-- The first LB instruction writes the aligned dword address to its chosen
scratch virtual register and leaves the Sail state unchanged. -/
theorem lb_virtual_align_addr_run
    (addrVReg : JoltISA.VReg) (hWritable : WritableVReg addrVReg)
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    (JoltISA.execInstr
      (.VirtualAlignAddr (.vreg addrVReg) (.xreg rs1) imm)).run js =
      .ok RETIRE_SUCCESS
        (stateAfterVRegWrite js addrVReg
          (jolt_virtual_align_addr_value h.rs1_val imm)) := by
  simpa only [stateAfterVRegWrite] using
    JoltISA.virtual_align_addr_run_vreg_xreg
      (vd := addrVReg)
      (rs := rs1)
      (imm := imm)
      (js := js)
      (x := h.rs1_val)
      (hread := h.rs1_read)
      (hvd := hWritable)

/-- The second LB instruction loads the aligned dword into the chosen scratch
virtual register. -/
theorem lb_ld_run
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
      (.LD .normal (.vreg dwordVReg) (.vreg dwordVReg)
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

/-- The third LB instruction writes the byte-window mask to its chosen scratch
virtual register. -/
theorem lb_virtual_window_mask_b_run
    (dwordVReg maskVReg : JoltISA.VReg)
    (hWritable : WritableVReg maskVReg)
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let jsAlign := stateAfterVRegWrite js dwordVReg
      (jolt_virtual_align_addr_value h.rs1_val imm)
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite jsAlign dwordVReg dval
    let maskValue := jolt_virtual_window_mask_b_value h.rs1_val imm
    (JoltISA.execInstr
      (.VirtualWindowMaskB (.vreg maskVReg) (.xreg rs1) imm)).run jsLoad =
      .ok RETIRE_SUCCESS
        (stateAfterVRegWrite jsLoad maskVReg maskValue) := by
  apply JoltISA.virtual_window_mask_b_run_vreg_xreg
  · simpa only [stateAfterVRegWrite] using h.rs1_read
  · exact hWritable

/-- The final instruction of the non-`x0` LB expansion writes the signed
parallel-extract result to the architectural destination register. -/
theorem lb_virtual_pext_signed_rd_run
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let jsAlign := stateAfterVRegWrite js (Vreg 41)
      (jolt_virtual_align_addr_value h.rs1_val imm)
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite jsAlign (Vreg 41) dval
    let maskValue := jolt_virtual_window_mask_b_value h.rs1_val imm
    let jsMask := stateAfterVRegWrite jsLoad (Vreg 40) maskValue
    let pextValue := jolt_virtual_pext_signed_value dval maskValue
    (JoltISA.execInstr
      (.VirtualPextSigned
        (.xreg rd) (.vreg (Vreg 41)) (.vreg (Vreg 40)))).run jsMask =
      .ok RETIRE_SUCCESS
        { jsMask with
          sail := stateAfterWrite jsMask.sail rd pextValue } := by
  apply JoltISA.virtual_pext_signed_run_xreg_vreg_vreg
  simpa only [stateAfterVRegWrite, Vreg, BitVec.reduceEq, ↓reduceIte] using
    wX_bits_stateAfterWrite
      (rd := rd)
      (v := _)
      (s := js.sail)

/-- The final instruction of the `x0` LB expansion writes the signed
parallel-extract result to virtual register 40. -/
theorem lb_virtual_pext_signed_v40_run
    (imm : BitVec 12) (rs1 : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let jsAlign := stateAfterVRegWrite js (Vreg 42)
      (jolt_virtual_align_addr_value h.rs1_val imm)
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite jsAlign (Vreg 42) dval
    let maskValue := jolt_virtual_window_mask_b_value h.rs1_val imm
    let jsMask := stateAfterVRegWrite jsLoad (Vreg 41) maskValue
    let pextValue := jolt_virtual_pext_signed_value dval maskValue
    (JoltISA.execInstr
      (.VirtualPextSigned
        (.vreg (Vreg 40)) (.vreg (Vreg 42)) (.vreg (Vreg 41)))).run jsMask =
      .ok RETIRE_SUCCESS
        (stateAfterVRegWrite jsMask (Vreg 40) pextValue) := by
  apply JoltISA.virtual_pext_signed_run_vreg_vreg_vreg
  simp only [WritableVReg, Vreg, BitVec.toNat_ofNat]
  norm_num

/-- The generated `LB` expansion writes only instruction-local scratch vregs. -/
theorem lbProgramAuto_preserves_projected_vregs
    (imm : BitVec 12) (rs1 rd : regidx)
    {js js' : SailJoltState} {result : ExecutionResult}
    (hrun : (JoltISA.execProgram (JoltISA.lbProgramAuto rd rs1 imm)).run js =
      .ok result js') :
    Projection.ProjectedVRegsPreserved js js' := by
  have hsafe : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.lbProgramAuto rd rs1 imm) := by
    unfold JoltISA.lbProgramAuto
    split <;>
      simp only [JoltISA.ProgramWritesNoProtectedVReg,
        JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
        JoltISA.sideEffectingDst, and_true] <;>
      norm_num [JoltISA.IsProtectedJoltRegister, JoltISA.joltRegisterSlot,
        JoltISA.JoltRegisterSlot.isProtected]
  exact Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
    hsafe hrun

/-- After either generated `LB` branch runs, `systemProject` agrees with the
embedded Sail state. -/
theorem lbProgramAuto_systemProject_eq_sail
    (imm : BitVec 12) (rs1 rd : regidx)
    (js js' : SailJoltState) (value : BitVec 64)
    (hlinked : LinkedCSRs js)
    (hrun : (JoltISA.execProgram (JoltISA.lbProgramAuto rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS js')
    (hsail : js'.sail = stateAfterWrite js.sail rd value) :
    System.systemProject js' = js'.sail := by
  have hprojected : Projection.ProjectedVRegsPreserved js js' :=
    lbProgramAuto_preserves_projected_vregs
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

/-- The non-`x0` generated expansion runs through its four instructions to the
explicit final state used by the equivalence proof. -/
theorem lbProgramAuto_nonzero_run
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hx0 : JoltISA.isX0 rd ≠ true) :
    let jsAlign := stateAfterVRegWrite js (Vreg 41)
      (jolt_virtual_align_addr_value h.rs1_val imm)
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite jsAlign (Vreg 41) dval
    let maskValue := jolt_virtual_window_mask_b_value h.rs1_val imm
    let jsMask := stateAfterVRegWrite jsLoad (Vreg 40) maskValue
    let pextValue := jolt_virtual_pext_signed_value dval maskValue
    let jsPext :=
      { jsMask with sail := stateAfterWrite jsMask.sail rd pextValue }
    (JoltISA.execProgram (JoltISA.lbProgramAuto rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS jsPext := by
  simp only [JoltISA.lbProgramAuto, if_neg hx0]
  have hv40 : WritableVReg (Vreg 40) := by
    simp only [WritableVReg, BitVec.toNat_ofNat]
    norm_num
  have hv41 : WritableVReg (Vreg 41) := by
    simp only [WritableVReg, BitVec.toNat_ofNat]
    norm_num

  let jsAlign := stateAfterVRegWrite js (Vreg 41)
    (jolt_virtual_align_addr_value h.rs1_val imm)
  let alignInstr : JoltISA.Instr :=
    .VirtualAlignAddr (.vreg (Vreg 41)) (.xreg rs1) imm
  rw [JoltISA.execProgram_instr_run_retire
    (instr := alignInstr)
    (rest := _)
    (js := js)
    (js' := jsAlign)
    (h := lb_virtual_align_addr_run
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
    .LD .normal (.vreg (Vreg 41)) (.vreg (Vreg 41)) (0 : BitVec 12)
  rw [JoltISA.execProgram_instr_run_retire
    (instr := ldInstr)
    (rest := _)
    (js := jsAlign)
    (js' := jsLoad)
    (h := lb_ld_run
      (dwordVReg := Vreg 41)
      (hWritable := hv41)
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h))]

  let maskValue := jolt_virtual_window_mask_b_value h.rs1_val imm
  let jsMask := stateAfterVRegWrite jsLoad (Vreg 40) maskValue
  let maskInstr : JoltISA.Instr :=
    .VirtualWindowMaskB (.vreg (Vreg 40)) (.xreg rs1) imm
  rw [JoltISA.execProgram_instr_run_retire
    (instr := maskInstr)
    (rest := _)
    (js := jsLoad)
    (js' := jsMask)
    (h := lb_virtual_window_mask_b_run
      (dwordVReg := Vreg 41)
      (maskVReg := Vreg 40)
      (hWritable := hv40)
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h))]

  let pextValue := jolt_virtual_pext_signed_value dval maskValue
  let jsPext :=
    { jsMask with sail := stateAfterWrite jsMask.sail rd pextValue }
  let pextInstr : JoltISA.Instr :=
    .VirtualPextSigned
      (.xreg rd) (.vreg (Vreg 41)) (.vreg (Vreg 40))
  rw [JoltISA.execProgram_instr_run_retire
    (instr := pextInstr)
    (rest := _)
    (js := jsMask)
    (js' := jsPext)
    (h := lb_virtual_pext_signed_rd_run
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h))]
  simp only [JoltISA.execProgram, pure, EStateM.pure, EStateM.run]
  rfl


/-- The non-`x0` branch of the main LB program theorem. -/
theorem lbProgram_eq_sail_nonzero (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hx0 : JoltISA.isX0 rd ≠ true) :
    lbProgramEqSailStatement imm rs1 rd js h := by
  unfold lbProgramEqSailStatement
  let jsAlign := stateAfterVRegWrite js (Vreg 41)
    (jolt_virtual_align_addr_value h.rs1_val imm)
  let facts := h.dwordWindowFacts
  let daddr := compute_aligned_dword_base_address h.rs1_val imm
  let dval := loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
  let jsLoad := stateAfterVRegWrite jsAlign (Vreg 41) dval
  let maskValue := jolt_virtual_window_mask_b_value h.rs1_val imm
  let jsMask := stateAfterVRegWrite jsLoad (Vreg 40) maskValue
  let pextValue := jolt_virtual_pext_signed_value dval maskValue
  let jsPext :=
    { jsMask with sail := stateAfterWrite jsMask.sail rd pextValue }
  have hjolt :
      (JoltISA.execProgram (JoltISA.lbProgramAuto rd rs1 imm)).run js =
        .ok RETIRE_SUCCESS jsPext := by
    exact lbProgramAuto_nonzero_run
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hx0 := hx0)
  have hFinalSail :
      jsPext.sail = stateAfterWrite js.sail rd pextValue := by
    rfl
  have hProject : System.systemProject jsPext = jsPext.sail :=
    lbProgramAuto_systemProject_eq_sail
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
  rw [LB_SailSide.execute_LB_reduces
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)]
  rw [LB_SailSide.stateAfterWrite_writeValue_eq_dword_byte
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)]

  -- NOTE: Math lemma
  rw [← pext_signed_byte_window
    (dval := dval)
    (byteOffset :=
      (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat)
    (hOffset :=
      addr_and_seven_lt_eight (load_effective_address h.rs1_val imm))]
  simp only [System.systemProjectResult]
  rw [hProject, hFinalSail]
  rfl

/-- The `x0` generated expansion runs through its four instructions to the
explicit final state used by the equivalence proof. -/
theorem lbProgramAuto_x0_run
    (imm : BitVec 12) (rs1 rd : regidx) (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hx0 : JoltISA.isX0 rd = true) :
    let jsAlign := stateAfterVRegWrite js (Vreg 42)
      (jolt_virtual_align_addr_value h.rs1_val imm)
    let facts := h.dwordWindowFacts
    let daddr := compute_aligned_dword_base_address h.rs1_val imm
    let dval :=
      loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
    let jsLoad := stateAfterVRegWrite jsAlign (Vreg 42) dval
    let maskValue := jolt_virtual_window_mask_b_value h.rs1_val imm
    let jsMask := stateAfterVRegWrite jsLoad (Vreg 41) maskValue
    let pextValue := jolt_virtual_pext_signed_value dval maskValue
    let jsPext := stateAfterVRegWrite jsMask (Vreg 40) pextValue
    (JoltISA.execProgram (JoltISA.lbProgramAuto rd rs1 imm)).run js =
      .ok RETIRE_SUCCESS jsPext := by
  simp only [JoltISA.lbProgramAuto, hx0, if_true]
  have hv41 : WritableVReg (Vreg 41) := by
    simp only [WritableVReg, BitVec.toNat_ofNat]
    norm_num
  have hv42 : WritableVReg (Vreg 42) := by
    simp only [WritableVReg, BitVec.toNat_ofNat]
    norm_num

  let jsAlign := stateAfterVRegWrite js (Vreg 42)
    (jolt_virtual_align_addr_value h.rs1_val imm)
  let alignInstr : JoltISA.Instr :=
    .VirtualAlignAddr (.vreg (Vreg 42)) (.xreg rs1) imm
  rw [JoltISA.execProgram_instr_run_retire
    (instr := alignInstr)
    (rest := _)
    (js := js)
    (js' := jsAlign)
    (h := lb_virtual_align_addr_run
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
    .LD .normal (.vreg (Vreg 42)) (.vreg (Vreg 42)) (0 : BitVec 12)
  rw [JoltISA.execProgram_instr_run_retire
    (instr := ldInstr)
    (rest := _)
    (js := jsAlign)
    (js' := jsLoad)
    (h := lb_ld_run
      (dwordVReg := Vreg 42)
      (hWritable := hv42)
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h))]

  let maskValue := jolt_virtual_window_mask_b_value h.rs1_val imm
  let jsMask := stateAfterVRegWrite jsLoad (Vreg 41) maskValue
  let maskInstr : JoltISA.Instr :=
    .VirtualWindowMaskB (.vreg (Vreg 41)) (.xreg rs1) imm
  rw [JoltISA.execProgram_instr_run_retire
    (instr := maskInstr)
    (rest := _)
    (js := jsLoad)
    (js' := jsMask)
    (h := lb_virtual_window_mask_b_run
      (dwordVReg := Vreg 42)
      (maskVReg := Vreg 41)
      (hWritable := hv41)
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h))]

  let pextValue := jolt_virtual_pext_signed_value dval maskValue
  let jsPext := stateAfterVRegWrite jsMask (Vreg 40) pextValue
  let pextInstr : JoltISA.Instr :=
    .VirtualPextSigned
      (.vreg (Vreg 40)) (.vreg (Vreg 42)) (.vreg (Vreg 41))
  rw [JoltISA.execProgram_instr_run_retire
    (instr := pextInstr)
    (rest := _)
    (js := jsMask)
    (js' := jsPext)
    (h := lb_virtual_pext_signed_v40_run
      (imm := imm)
      (rs1 := rs1)
      (js := js)
      (h := h))]
  simp only [JoltISA.execProgram, pure, EStateM.pure, EStateM.run]
  rfl

/-- The `x0` branch of the main LB program theorem. -/
theorem lbProgram_eq_sail_x0 (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js)
    (hx0 : JoltISA.isX0 rd = true) :
    lbProgramEqSailStatement imm rs1 rd js h := by
  unfold lbProgramEqSailStatement
  let jsAlign := stateAfterVRegWrite js (Vreg 42)
    (jolt_virtual_align_addr_value h.rs1_val imm)
  let facts := h.dwordWindowFacts
  let daddr := compute_aligned_dword_base_address h.rs1_val imm
  let dval := loaded_dword_at js.sail daddr facts.bytes facts.aligned.no_ovf
  let jsLoad := stateAfterVRegWrite jsAlign (Vreg 42) dval
  let maskValue := jolt_virtual_window_mask_b_value h.rs1_val imm
  let jsMask := stateAfterVRegWrite jsLoad (Vreg 41) maskValue
  let pextValue := jolt_virtual_pext_signed_value dval maskValue
  let jsPext := stateAfterVRegWrite jsMask (Vreg 40) pextValue
  have hjolt :
      (JoltISA.execProgram (JoltISA.lbProgramAuto rd rs1 imm)).run js =
        .ok RETIRE_SUCCESS jsPext := by
    exact lbProgramAuto_x0_run
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
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
    lbProgramAuto_systemProject_eq_sail
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
  rw [LB_SailSide.execute_LB_reduces
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)]
  rw [LB_SailSide.stateAfterWrite_writeValue_eq_dword_byte
    (imm := imm)
    (rs1 := rs1)
    (rd := rd)
    (js := js)
    (h := h)]

  -- NOTE: Math lemma
  rw [← pext_signed_byte_window
    (dval := dval)
    (byteOffset :=
      (load_effective_address h.rs1_val imm &&& (7 : BitVec 64)).toNat)
    (hOffset :=
      addr_and_seven_lt_eight (load_effective_address h.rs1_val imm))]
  simp only [System.systemProjectResult]
  rw [hProject, hFinalSail]
  rfl

/-- **Main program theorem for LB.**  The structured Jolt-ISA expansion
matches Sail after materializing Jolt's persistent CSR virtual registers. -/
theorem lbProgram_eq_sail (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    lbProgramEqSailStatement imm rs1 rd js h := by
  by_cases hx0 : JoltISA.isX0 rd = true
  · exact lbProgram_eq_sail_x0
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hx0 := hx0)
  · exact lbProgram_eq_sail_nonzero
      (imm := imm)
      (rs1 := rs1)
      (rd := rd)
      (js := js)
      (h := h)
      (hx0 := hx0)
end LB_main
