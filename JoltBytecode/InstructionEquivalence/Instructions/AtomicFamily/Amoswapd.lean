import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Dword
import JoltBytecode.JoltISA.ExpansionsAutomated

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

theorem amoswapdProgram_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amoswapdProgramAuto rd rs1 rs2) := by
  unfold JoltISA.amoswapdProgramAuto
  split <;>
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      true_and, and_true] <;>
    repeat' apply And.intro
  all_goals exact JoltISA.not_protected_of_instructionTmp rfl


/-- Main public theorem for `AMOSWAP.D`.

The theorem takes one primitive-only atomic bundle. Exact memory facts are
derived internally from that bundle. -/
private theorem amoswapdProgramAuto_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js) :
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.amoswapdProgramAuto rd rs1 rs2)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 8 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  have hbytes : MemBytesPresentAt js.sail addr 8 := by
    simpa [addr] using Assumptions.DwordPresent.memBytesPresentAt h.dword_present
  have hload_pmp : Assumptions.LoadPmpOk addr 8 js.sail := by
    simpa [addr] using h.load_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hstore_pmp : Assumptions.StorePmpOk addr 8 js.sail := by
    simpa [addr] using h.store_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hatomic_pmp : Assumptions.AtomicPmpOk amoop.AMOSWAP addr 8 js.sail := by
    simpa [addr] using h.atomic_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hread_mmio : Assumptions.NotReadableMmio addr 8 js.sail := by
    simpa [addr] using h.not_readable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega)
  have hwrite_mmio : Assumptions.NotWritableMmio addr 8 js.sail := by
    simpa [addr] using h.not_writable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega)
  by_cases h_align : addr &&& (7 : BitVec 64) = 0
  · let old :=
      loaded_dword_at js.sail addr hbytes
        (amo_dword_aligned_no_ovf addr h_align)
    let oldReg := JoltISA.amoOldVRegFor rd
    obtain ⟨js_afterLoad, hld, hld_sail, hld_old⟩ :=
      amo_dword_load_old_aligned_run_into oldReg
        rs1 js h.cur_privilege h.mstatus_mprv addr h.rs1_read
        hbytes hload_pmp hread_mmio h_align
        (JoltISA.amoOldVRegFor_writable rd)
    obtain ⟨js_afterStore, hsd, hsd_sail, hsd_vregs⟩ :=
      amo_dword_store_xreg_result_after_load_aligned_run
        rs2 rs1 js js_afterLoad h.cur_privilege h.mstatus_mprv
        addr rs2Val h.rs1_read h.rs2_read hstore_pmp hwrite_mmio
        h_align hld_sail
    obtain ⟨js_afterWrite, haddi, haddi_sail⟩ :=
      amo_dword_writeback_after_store_run_from oldReg
        rd js_afterLoad js_afterStore addr old hsd_vregs hld_old
    have hjolt :
        (JoltISA.execProgram (JoltISA.amoswapdProgramAuto rd rs1 rs2)).run js =
          .ok RETIRE_SUCCESS js_afterWrite := by
      unfold JoltISA.amoswapdProgramAuto
      cases hrd : JoltISA.isX0 rd
      all_goals
        simp only [hrd, Bool.false_eq_true, if_false, if_true,
          oldReg, JoltISA.amoOldVRegFor, JoltISA.amoVRegFor,
          JoltISA.inlineTmp, JoltISA.inlineRegisterBase,
          JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
          JoltISA.numReservedVirtualRegisters,
          JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst,
          JoltISA.rdZeroRewriteVReg] at hld haddi ⊢
        rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterLoad hld]
        rw [JoltISA.execProgram_instr_run_retire _ _ js_afterLoad js_afterStore hsd]
        rw [JoltISA.execProgram_instr_run_retire _ _ js_afterStore js_afterWrite haddi]
        rfl
    have hsail :=
      execute_AMO_dword_non_cas_aligned
        amoop.AMOSWAP rs2 rs1 rd js h.cur_privilege h.mstatus_mprv
        addr rs2Val rs2Val h.rs1_read h.rs2_read h.rdReadable.exists_value
        hbytes hatomic_pmp hread_mmio hwrite_mmio h_align (by decide)
        (by
          unfold amoDwordSailResult
          unfold trunc Sail.BitVec.truncate
          rfl)
    have hjolt_sail :
        js_afterWrite.sail =
          amoDwordFinalSailState rd js.sail addr rs2Val old := by
      rw [haddi_sail, hsd_sail, hld_sail]
    have hprojected : Projection.ProjectedVRegsPreserved js js_afterWrite :=
      Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
        (amoswapdProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hjolt
    have hprojectFinal :
        System.systemProject js_afterWrite = js_afterWrite.sail := by
      exact Projection.systemProject_eq_sail_of_memory_update_then_write
        js js_afterWrite (state_after_dword_store js.sail addr rs2Val) rd old
        hjolt_sail rfl hprojected h.linkedCSRs
    rw [hjolt]
    rw [hsail]
    simp only [System.systemProjectResult]
    rw [hprojectFinal, hjolt_sail]
  · let rest : JoltISA.Program :=
      .instr (.SD (.xreg rs1) (.xreg rs2) (0 : BitVec 12)) <|
      .instr (.ADDI (JoltISA.amoDstFor rd) (.vreg (JoltISA.amoOldVRegFor rd))
        (0 : BitVec 12)) <|
      .done RETIRE_SUCCESS
    let oldReg := JoltISA.amoOldVRegFor rd
    let e := (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())
    have hld :
        (JoltISA.execInstr
          (.LD .amo (.vreg oldReg) (.xreg rs1) (0 : BitVec 12))).run js =
        .ok (ExecutionResult.Memory_Exception e) js := by
      exact
        amo_dword_ld_xreg_misaligned_run
          oldReg rs1 js addr h.rs1_read h_align
    have hjolt :
        (JoltISA.execProgram (JoltISA.amoswapdProgramAuto rd rs1 rs2)).run js =
          .ok (ExecutionResult.Memory_Exception e) js := by
      cases hrd : JoltISA.isX0 rd
      all_goals
        simpa only [JoltISA.amoswapdProgramAuto, hrd,
          Bool.false_eq_true, if_false, if_true,
          oldReg, rest, JoltISA.amoOldVRegFor, JoltISA.amoVRegFor,
          JoltISA.inlineTmp, JoltISA.inlineRegisterBase,
          JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
          JoltISA.numReservedVirtualRegisters,
          JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst,
          JoltISA.rdZeroRewriteVReg] using
          (JoltISA.execProgram_instr_run_memory_exception
            (.LD .amo (.vreg oldReg) (.xreg rs1) (0 : BitVec 12))
            rest js js e hld)
    have hsail :=
      execute_AMO_dword_misaligned
        amoop.AMOSWAP rs2 rs1 rd js addr rs2Val h.rs1_read h.rs2_read h_align
    rw [hjolt]
    rw [hsail]
    simp only [System.systemProjectResult]
    congr 1
    exact Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs

/-- Main public theorem for `AMOSWAP.D`. -/
def amoswapdProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoDwordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.amoswapdProgramAuto rd rs1 rs2)).run js) =
    (execute_AMO amoop.AMOSWAP false false rs2 rs1 8 rd).run js.sail

theorem amoswapdProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoDwordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js) :
    amoswapdProgramEqSailStatement rs2 rs1 rd js h := by
  unfold amoswapdProgramEqSailStatement
  exact amoswapdProgramAuto_eq_sail rs2 rs1 rd js h

end AtomicFamily

end
