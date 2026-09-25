import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.LoadFamily.DwordArithmetic
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Windows
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace Natives

private theorem sign_extend_64_eq_self (value : BitVec 64) :
    sign_extend (m := 64) value = value := by
  unfold sign_extend Sail.BitVec.signExtend
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi_bool : (i <b 64) = true := by
    simpa only [Nat.blt_eq, decide_eq_true_eq] using hi
  simp (disch := omega) only [BitVec.getLsbD_signExtend, hi_bool,
    Bool.true_and, if_pos]

private theorem vmem_read_dword_reduces (imm : BitVec 12) (rs1 : regidx)
    (s : SailState)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (val : BitVec 64) (hrx : rX_bits rs1 s = .ok val s)
    (haligned : AlignedDwordAccess (load_effective_address val imm))
    (hbytes : MemBytesPresentAt s (load_effective_address val imm) 8)
    (hload_pmp : Assumptions.LoadPmpOk (load_effective_address val imm) 8 s)
    (hread_mmio : Assumptions.NotReadableMmio (load_effective_address val imm) 8 s) :
    vmem_read rs1 (sign_extend (m := 64) imm) 8 (Load Data) false false false s =
    .ok (Ok (loaded_dword_at s (load_effective_address val imm)
      hbytes haligned.no_ovf)) s := by
  have haddr :=
    aligned_dword_vmem_read_reduces (load_effective_address val imm) s
      hpriv hmprv haligned hbytes hload_pmp hread_mmio
  have haddr_offset :
      vmem_read_addr (Virtaddr (val + sign_extend (m := 64) imm))
        (sign_extend (m := 64) imm) 8 (Load Data) false false false s =
      .ok (Ok (loaded_dword_at s (load_effective_address val imm)
        hbytes haligned.no_ovf)) s := by
    simpa [load_effective_address, Memory.effectiveAddr12] using haddr
  unfold vmem_read
  unfold SailME.run PreSail.PreSailME.run
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map,
    ext_data_get_addr, hrx, load_effective_address, Memory.effectiveAddr12,
    haddr_offset]

private theorem execute_LD_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (haligned : AlignedDwordAccess (load_effective_address val imm))
    (hbytes : MemBytesPresentAt js.sail (load_effective_address val imm) 8)
    (hload_pmp : Assumptions.LoadPmpOk (load_effective_address val imm) 8 js.sail)
    (hread_mmio : Assumptions.NotReadableMmio
      (load_effective_address val imm) 8 js.sail) :
    (execute_LOAD imm rs1 rd false 8).run js.sail =
    .ok RETIRE_SUCCESS
      (stateAfterWrite js.sail rd
        (loaded_dword_at js.sail (load_effective_address val imm)
          hbytes haligned.no_ovf)) := by
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind,
    pure, EStateM.pure, EStateM.run, if_true]
  rw [vmem_read_dword_reduces imm rs1 js.sail hpriv hmprv val hrx
    haligned hbytes hload_pmp hread_mmio]
  simp only [extend_value, Bool.false_eq_true, if_false, EStateM.bind,
    EStateM.pure]
  rw [sign_extend_64_eq_self]
  rw [wX_bits_stateAfterWrite]

private theorem execute_LD_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64) (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& (7 : BitVec 64) ≠ 0) :
    (execute_LOAD imm rs1 rd false 8).run js.sail =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ()))
        js.sail := by
  let ea := load_effective_address val imm
  unfold execute_LOAD
  simp only [bind, pure]
  unfold Sail.assert LeanRV64D.Functions.xlen_bytes
  simp (config := { decide := true }) only []
  simp (config := { decide := true }) only [PreSail.assert, EStateM.bind,
    pure, EStateM.pure, EStateM.run, if_true]
  unfold vmem_read
  unfold SailME.run PreSail.PreSailME.run
  have hmis :
      access_causes_misaligned_exception (Virtaddr ea) 8 false = true := by
    simpa [ea] using access_misaligned_8_unaligned_true ea h_align
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.map,
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont,
    ExceptT.pure, ExceptT.lift,
    MonadLift.monadLift, liftM, monadLift, Functor.map,
    ext_data_get_addr, hrx, vmem_read_addr, hmis, ea]
  rfl

private theorem ldJolt_aligned_reduces (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val loaded : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& (7 : BitVec 64) = 0)
    (hread :
      vmem_read_addr (Virtaddr (load_effective_address val imm)) 0 8
        (Load Data) false false false js.sail =
        .ok (Ok loaded) js.sail)
    (hlinked : LinkedCSRs js)
    (h_ram : JoltISA.ramStartAddress ≤ (load_effective_address val imm).toNat) :
    System.systemProjectResult
      ((JoltISA.execInstr (JoltISA.Encoded.LD .normal (.xreg rd) (.xreg rs1) imm)).run js) =
    .ok RETIRE_SUCCESS (stateAfterWrite js.sail rd loaded) := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst liftSail
  simp only [bind, EStateM.bind, pure, EStateM.run, hrx]
  rw [if_pos (by
    simpa [load_effective_address, Memory.effectiveAddr12] using h_align)]
  rw [JoltISA.readMemoryWord_ram _ h_ram]
  unfold liftSail
  simp only [hread, EStateM.bind]
  by_cases hx0 : JoltISA.isX0 rd = true
  · have hdst :
        JoltISA.sideEffectingDst (JoltISA.Dst.xreg rd) =
          JoltISA.Dst.vreg JoltISA.rdZeroRewriteVReg := by
      simp [JoltISA.sideEffectingDst, JoltISA.sideEffectingRdZeroDst, hx0]
    let js' : SailJoltState :=
      { js with
        vregs := fun r =>
          if r = JoltISA.rdZeroRewriteVReg then loaded else js.vregs r }
    have hprojected : Projection.ProjectedVRegsPreserved js js' := by
      unfold Projection.ProjectedVRegsPreserved js'
      simp [JoltISA.rdZeroRewriteVReg, JoltISA.inlineTmp,
        JoltISA.inlineRegisterBase, JoltISA.riscvRegisterBase,
        JoltISA.riscvRegisterCount, JoltISA.numReservedVirtualRegisters,
        JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
        JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.mstatusVReg]
    have hproject : System.systemProject js' = js.sail := by
      have hregs : js'.sail.regs = js.sail.regs := rfl
      exact
        Projection.systemProject_eq_sail_of_projected_vregs_preserved_of_sail_regs_eq
          js js' hregs hprojected hlinked
    have hwrite_vreg :
        writeVReg JoltISA.rdZeroRewriteVReg loaded
          ({ js with vregs := js.vregs } : SailJoltState) =
        .ok () js' := by
      unfold writeVReg js' JoltISA.rdZeroRewriteVReg JoltISA.inlineTmp
        JoltISA.inlineRegisterBase JoltISA.riscvRegisterBase
        JoltISA.riscvRegisterCount JoltISA.numReservedVirtualRegisters
      simp [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
    simp only [hdst]
    rw [hwrite_vreg]
    simp only [EStateM.pure, System.systemProjectResult]
    rw [hproject]
    rw [JoltISA.stateAfterWrite_of_isX0_eq_true hx0 js.sail loaded]
  · have hdst :
        JoltISA.sideEffectingDst (JoltISA.Dst.xreg rd) =
          JoltISA.Dst.xreg rd := by
      have hx0_false : JoltISA.isX0 rd = false := by
        cases hcase : JoltISA.isX0 rd <;> simp [hcase] at hx0 ⊢
      simp [JoltISA.sideEffectingDst, JoltISA.sideEffectingRdZeroDst, hx0_false]
    simp only [hdst]
    obtain ⟨s', hwrite⟩ := wX_shape rd loaded js.sail
    rw [hwrite]
    simp only [EStateM.pure]
    have hproject :=
      Projection.systemProjectResult_pure_retire_after_xreg_write
        rd js s' loaded hlinked hwrite
    simp only [pure, EStateM.pure] at hproject
    rw [hproject]
    rw [wX_bits_eq_stateAfterWrite rd loaded js.sail s' hwrite]

private theorem ldJolt_misaligned (imm : BitVec 12) (rs1 rd : regidx)
    (js : SailJoltState)
    (val : BitVec 64)
    (hrx : rX_bits rs1 js.sail = .ok val js.sail)
    (h_align : load_effective_address val imm &&& (7 : BitVec 64) ≠ 0)
    (hlinked : LinkedCSRs js) :
    System.systemProjectResult
      ((JoltISA.execInstr (JoltISA.Encoded.LD .normal (.xreg rd) (.xreg rs1) imm)).run js) =
    .ok (ExecutionResult.Memory_Exception
      (Virtaddr (load_effective_address val imm), ExceptionType.E_Load_Addr_Align ()))
      js.sail := by
  unfold JoltISA.execInstr JoltISA.readSrc liftSail
  simp only [bind, EStateM.bind, pure, EStateM.run, hrx]
  rw [if_neg (by
    simpa [load_effective_address, Memory.effectiveAddr12] using h_align)]
  simp only [JoltISA.LoadFaultClass.alignFault, EStateM.pure,
    System.systemProjectResult]
  rw [Projection.systemProject_eq_sail_of_compatible js hlinked]

/-- Main native `LD` equivalence statement. -/
def ldInstrEqSailStatement
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (_h : LoadProgramEqSailAssumptions imm rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (JoltISA.Encoded.LD .normal (.xreg rd) (.xreg rs1) imm)).run js) =
    ((execute_LOAD imm rs1 rd false 8).run js.sail)

theorem ldInstr_eq_sail
    (imm : BitVec 12)
    (rs1 rd : regidx)
    (js : SailJoltState)
    (h : LoadProgramEqSailAssumptions imm rs1 js) :
    ldInstrEqSailStatement imm rs1 rd js h := by
  unfold ldInstrEqSailStatement
  let ea := load_effective_address h.rs1_val imm
  let base := compute_aligned_dword_base_address h.rs1_val imm
  let offset := (ea &&& (7 : BitVec 64)).toNat
  have h_base_aligned : AlignedDwordAccess base := by
    simpa [base, compute_aligned_dword_base_address, aligned_dword_addr_eq,
      load_effective_address] using
      aligned_dword_addr_is_aligned_dword_access h.rs1_val imm
  have hbytes_base : MemBytesPresentAt js.sail base 8 := by
    simpa [base] using h.dword_present.memBytesPresentAt
  have haddr : base + BitVec.ofNat 64 offset = ea := by
    simpa [base, ea, offset, compute_aligned_dword_base_address] using
      addr_split_aligned_offset ea
  by_cases h_align : ea &&& (7 : BitVec 64) = 0
  · have hoff_eq : offset = 0 := by
      simpa [offset] using congrArg BitVec.toNat h_align
    have hoff : offset + 8 ≤ 8 := by
      omega
    have haligned : AlignedDwordAccess ea :=
      { misalign := access_misaligned_8_aligned_false ea h_align
        split := split_misaligned_aligned_8 ea h_align
        align := h_align
        no_ovf := aligned_addr_no_ovf_of_align ea h_align }
    have hbytes : MemBytesPresentAt js.sail ea 8 := by
      have hsub : MemBytesPresentAt js.sail (base + BitVec.ofNat 64 offset) 8 :=
        memBytesPresentAt_subaccess (s := js.sail) (base := base) (baseWidth := 8)
          (offset := offset) (accessWidth := 8) hbytes_base hoff (by
            have hbase_no_ovf := h_base_aligned.no_ovf
            omega)
      simpa [haddr] using hsub
    have hload_pmp : Assumptions.LoadPmpOk ea 8 js.sail := by
      have hsub : Assumptions.LoadPmpOk (base + BitVec.ofNat 64 offset) 8 js.sail :=
        h.load_pmp.subaccess (offset := offset) (accessWidth := 8) hoff
      simpa [base, haddr] using hsub
    have hread_mmio : Assumptions.NotReadableMmio ea 8 js.sail := by
      have hsub :
          Assumptions.NotReadableMmio (base + BitVec.ofNat 64 offset) 8 js.sail :=
        h.not_readable_mmio.subaccess (offset := offset) (accessWidth := 8) hoff
      simpa [base, haddr] using hsub
    have hread :
        vmem_read_addr (Virtaddr ea) 0 8 (Load Data) false false false js.sail =
        .ok (Ok (loaded_dword_at js.sail ea hbytes haligned.no_ovf)) js.sail :=
      aligned_dword_vmem_read_reduces ea js.sail h.cur_privilege h.mstatus_mprv
        haligned hbytes hload_pmp hread_mmio
    rw [ldJolt_aligned_reduces imm rs1 rd js h.rs1_val
      (loaded_dword_at js.sail ea hbytes haligned.no_ovf)
      h.rs1_read (by simpa [ea] using h_align)
      (by simpa [ea] using hread) h.linkedCSRs hread_mmio.ram]
    rw [execute_LD_reduces imm rs1 rd js h.cur_privilege h.mstatus_mprv
      h.rs1_val h.rs1_read (by simpa [ea] using haligned)
      (by simpa [ea] using hbytes)
      (by simpa [ea] using hload_pmp)
      (by simpa [ea] using hread_mmio)]
  · rw [ldJolt_misaligned imm rs1 rd js h.rs1_val h.rs1_read
      (by simpa [ea] using h_align) h.linkedCSRs]
    rw [execute_LD_misaligned imm rs1 rd js h.rs1_val h.rs1_read
      (by simpa [ea] using h_align)]

end Natives

end
