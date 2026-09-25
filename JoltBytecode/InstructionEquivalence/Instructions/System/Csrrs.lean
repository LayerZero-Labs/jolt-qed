import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.System.Common

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-! ## Jolt-side CSRRS helpers -/

private theorem isX0_eq_true_of_beq_zreg_true {r : regidx}
    (h : (r == zreg) = true) :
    JoltISA.isX0 r = true := by
  cases r with
  | Regidx bits =>
      unfold zreg at h
      unfold JoltISA.isX0
      change (bits == zero_extend (m := 5) 0b00#2) = true at h
      have hBits : bits = zero_extend (m := 5) 0b00#2 := LawfulBEq.eq_of_beq h
      rw [hBits]
      decide

private theorem isX0_eq_false_of_beq_zreg_false {r : regidx}
    (h : (r == zreg) = false) :
    JoltISA.isX0 r = false := by
  cases r with
  | Regidx bits =>
      unfold zreg at h
      unfold JoltISA.isX0
      change (bits == zero_extend (m := 5) 0b00#2) = false at h
      apply decide_eq_false
      intro hNat
      have hBits : bits = zero_extend (m := 5) 0b00#2 := by
        apply BitVec.eq_of_toNat_eq
        rw [hNat]
        decide
      rw [hBits] at h
      have hSelf :
          (zero_extend (m := 5) 0b00#2 == zero_extend (m := 5) 0b00#2) =
            true := by
        decide
      have hContra : true = false := hSelf.symm.trans h
      cases hContra

private theorem stateAfterWrite_of_beq_zreg_true {rd : regidx}
    (h : (rd == zreg) = true) (s : SailState) (value : BitVec 64) :
    stateAfterWrite s rd value = s := by
  cases rd with
  | Regidx bits =>
      unfold zreg at h
      change (bits == zero_extend (m := 5) 0b00#2) = true at h
      have hBits : bits = zero_extend (m := 5) 0b00#2 := LawfulBEq.eq_of_beq h
      rw [hBits]
      exact stateAfterWrite_regidx_zero s value

private theorem stateAfterWrite_of_isX0_true {rd : regidx}
    (h : JoltISA.isX0 rd = true) (s : SailState) (value : BitVec 64) :
    stateAfterWrite s rd value = s := by
  cases rd with
  | Regidx bits =>
      unfold JoltISA.isX0 at h
      have hBits : bits = 0 := BitVec.eq_of_toNat_eq (of_decide_eq_true h)
      rw [hBits]
      exact stateAfterWrite_regidx_zero s value

private theorem ne_of_sameXReg_eq_false {rd rs : regidx}
    (h : JoltISA.sameXReg rd rs = false) :
    rd ≠ rs := by
  cases rd with
  | Regidx rdBits =>
      cases rs with
      | Regidx rsBits =>
          intro heq
          cases heq
          unfold JoltISA.sameXReg at h
          simp at h

private theorem systemCSR_vreg_writable (csr : JoltISA.SystemCSR) :
    WritableVReg (JoltISA.SystemCSR.vreg csr) := by
  cases csr <;>
    unfold JoltISA.SystemCSR.vreg WritableVReg
      JoltISA.mstatusVReg JoltISA.trapHandlerVReg JoltISA.mscratchVReg
      JoltISA.mepcVReg JoltISA.mcauseVReg JoltISA.mtvalVReg
      JoltISA.riscvRegisterBase JoltISA.riscvRegisterCount <;>
    decide

private theorem systemScratch_vreg_writable :
    WritableVReg JoltISA.systemScratchVReg := by
  unfold JoltISA.systemScratchVReg JoltISA.inlineTmp0 JoltISA.inlineTmp
    WritableVReg JoltISA.inlineRegisterBase JoltISA.riscvRegisterBase
    JoltISA.riscvRegisterCount JoltISA.numReservedVirtualRegisters
  decide

private theorem systemCSR_vreg_ne_scratch (csr : JoltISA.SystemCSR) :
    JoltISA.SystemCSR.vreg csr ≠ JoltISA.systemScratchVReg := by
  cases csr <;>
    unfold JoltISA.SystemCSR.vreg JoltISA.systemScratchVReg
      JoltISA.mstatusVReg JoltISA.trapHandlerVReg JoltISA.mscratchVReg
      JoltISA.mepcVReg JoltISA.mcauseVReg JoltISA.mtvalVReg
      JoltISA.inlineTmp0 JoltISA.inlineTmp JoltISA.inlineRegisterBase
      JoltISA.riscvRegisterBase JoltISA.riscvRegisterCount
      JoltISA.numReservedVirtualRegisters <;>
    decide

private theorem or_run_vreg_vreg_xreg
    (vd lhs : JoltISA.VReg) (rhs : regidx) (js : SailJoltState) (rhsVal : BitVec 64)
    (hRhs : rX_bits rhs js.sail = .ok rhsVal js.sail)
    (hvd : WritableVReg vd) :
    (JoltISA.execInstr (.OR (.vreg vd) (.vreg lhs) (.xreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then js.vregs lhs ||| rhsVal else js.vregs r } := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg liftSail
  simp only [hRhs, bind, EStateM.bind, pure, EStateM.pure, EStateM.run, get, getThe,
    MonadStateOf.get, EStateM.get]
  exact JoltISA.writeVReg_retire_run_of_writable vd
    (js.vregs lhs ||| rhsVal) js hvd

private theorem or_run_vreg_vreg_vreg
    (vd lhs rhs : JoltISA.VReg) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (JoltISA.execInstr (.OR (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then js.vregs lhs ||| js.vregs rhs else js.vregs r } := by
  unfold JoltISA.execInstr JoltISA.readSrc JoltISA.writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run, get, getThe,
    MonadStateOf.get, EStateM.get]
  exact JoltISA.writeVReg_retire_run_of_writable vd
    (js.vregs lhs ||| js.vregs rhs) js hvd

private def csrrsWriteValue
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1Val : BitVec 64) :
    BitVec 64 :=
  js.vregs (JoltISA.SystemCSR.vreg csr) ||| rs1Val

/-- Final CSRRS state for the `rs1 = x0` read-only case. -/
private def csrrsAfterReadOnly
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx) :
    SailJoltState :=
  { js with
    sail := stateAfterWrite js.sail rd (js.vregs (JoltISA.SystemCSR.vreg csr)) }

/-- Final CSRRS state for the `rs1 != x0, rd = x0` set-only case. -/
private def csrrsAfterCsrSet
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1Val : BitVec 64) :
    SailJoltState :=
  joltSetVReg js (JoltISA.SystemCSR.vreg csr) (csrrsWriteValue js csr rs1Val)

/-- Final CSRRS state after `rd` receives the old CSR value and the virtual CSR
receives `old CSR | rs1`. -/
private def csrrsAfterReadSet
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx)
    (oldCsr rs1Val : BitVec 64) : SailJoltState :=
  { csrrsAfterCsrSet js csr rs1Val with
    sail := stateAfterWrite js.sail rd oldCsr }

/-- Final CSRRS state for the `rd = rs1` branch: preserve `rs1` in scratch, read
the old CSR into `rd`, then set the CSR from the preserved source value. -/
private def csrrsAfterSameReg
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx)
    (oldCsr rs1Val : BitVec 64) : SailJoltState :=
  joltSetVReg
    { joltSetVReg js JoltISA.systemScratchVReg rs1Val with
      sail := stateAfterWrite js.sail rd oldCsr }
    (JoltISA.SystemCSR.vreg csr) (oldCsr ||| rs1Val)

/-- The concrete final Jolt state selected by Rust's CSRRS expansion branches. -/
private def csrrsJoltFinal
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (rs1Val : BitVec 64) : SailJoltState :=
  if JoltISA.isX0 rs1 then
    csrrsAfterReadOnly js csr rd
  else if JoltISA.isX0 rd then
    csrrsAfterCsrSet js csr rs1Val
  else if JoltISA.sameXReg rd rs1 then
    csrrsAfterSameReg js csr rd
      (js.vregs (JoltISA.SystemCSR.vreg csr)) rs1Val
  else
    csrrsAfterReadSet js csr rd
      (js.vregs (JoltISA.SystemCSR.vreg csr)) rs1Val

private theorem csrrsProgram_project_run
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (rs1Val : BitVec 64)
    (hSource : rX_bits rs1 js.sail = .ok rs1Val js.sail) :
    systemProjectResult
        ((JoltISA.execProgram
          (JoltISA.csrrsProgram csr rs1 rd)).run js) =
      .ok RETIRE_SUCCESS
        (systemProject
          (csrrsJoltFinal js csr rs1 rd rs1Val)) := by
  unfold JoltISA.csrrsProgram csrrsJoltFinal
  cases hRs1 : JoltISA.isX0 rs1
  · simp only [Bool.false_and, Bool.false_eq_true, if_false]
    cases hRd : JoltISA.isX0 rd
    · simp only [Bool.false_eq_true, if_false]
      cases hSame : JoltISA.sameXReg rd rs1
      · simp only [Bool.false_eq_true, if_false]
        let oldCsr := js.vregs (JoltISA.SystemCSR.vreg csr)
        let jsAfterRd : SailJoltState :=
          { js with sail := stateAfterWrite js.sail rd oldCsr }
        have hRdRun :
            (JoltISA.execInstr
                (JoltISA.Encoded.ADDI (.xreg rd) (.vreg (JoltISA.SystemCSR.vreg csr))
                  (0 : BitVec 12))).run js =
              .ok RETIRE_SUCCESS jsAfterRd := by
          have hWrite :
              wX_bits rd
                  (js.vregs (JoltISA.SystemCSR.vreg csr) +
                    sign_extend (m := 64) (0 : BitVec 12))
                  js.sail =
                .ok () (stateAfterWrite js.sail rd oldCsr) := by
            rw [addi_zero_value]
            exact wX_bits_stateAfterWrite rd oldCsr js.sail
          simpa [jsAfterRd, oldCsr] using
            JoltISA.addi_run_xreg_vreg rd (JoltISA.SystemCSR.vreg csr)
              (0 : BitVec 12) js (stateAfterWrite js.sail rd oldCsr) hWrite
        have hSourceAfter :
            rX_bits rs1 jsAfterRd.sail = .ok rs1Val jsAfterRd.sail := by
          exact rX_bits_stateAfterWrite_of_ne rd rs1 oldCsr rs1Val js.sail
            (ne_of_sameXReg_eq_false hSame) hSource
        have hCsrRun :
            (JoltISA.execInstr
                (.OR (.vreg (JoltISA.SystemCSR.vreg csr))
                  (.vreg (JoltISA.SystemCSR.vreg csr)) (.xreg rs1))).run
                jsAfterRd =
              .ok RETIRE_SUCCESS
                (csrrsAfterReadSet js csr rd oldCsr rs1Val) := by
          have hRun :=
            or_run_vreg_vreg_xreg (JoltISA.SystemCSR.vreg csr)
              (JoltISA.SystemCSR.vreg csr) rs1 jsAfterRd rs1Val hSourceAfter
              (systemCSR_vreg_writable csr)
          simpa [csrrsAfterReadSet, csrrsAfterCsrSet, csrrsWriteValue,
            joltSetVReg, vregWrite, jsAfterRd, oldCsr] using hRun
        rw [JoltISA.execProgram_instr_run_retire _ _ js jsAfterRd hRdRun]
        rw [JoltISA.execProgram_instr_run_retire _ _ jsAfterRd
          (csrrsAfterReadSet js csr rd oldCsr rs1Val) hCsrRun]
        simp only [oldCsr, JoltISA.execProgram_done, EStateM.run, pure,
          EStateM.pure, systemProjectResult]
      · simp only [if_true]
        let oldCsr := js.vregs (JoltISA.SystemCSR.vreg csr)
        let jsScratch : SailJoltState :=
          joltSetVReg js JoltISA.systemScratchVReg rs1Val
        let jsAfterRd : SailJoltState :=
          { jsScratch with sail := stateAfterWrite jsScratch.sail rd oldCsr }
        have hScratchRun :
            (JoltISA.execInstr
                (JoltISA.Encoded.ADDI (.vreg JoltISA.systemScratchVReg) (.xreg rs1)
                  (0 : BitVec 12))).run js =
              .ok RETIRE_SUCCESS jsScratch := by
          have hRun :=
            JoltISA.addi_run_vreg_xreg JoltISA.systemScratchVReg rs1
              (0 : BitVec 12) js rs1Val hSource systemScratch_vreg_writable
          rw [addi_zero_value] at hRun
          simpa [jsScratch, joltSetVReg, vregWrite] using hRun
        have hScratchCsr :
            jsScratch.vregs (JoltISA.SystemCSR.vreg csr) = oldCsr := by
          simpa [jsScratch, joltSetVReg, oldCsr] using
            vregWrite_other js.vregs JoltISA.systemScratchVReg
              (JoltISA.SystemCSR.vreg csr) rs1Val
              (systemCSR_vreg_ne_scratch csr)
        have hRdRun :
            (JoltISA.execInstr
                (JoltISA.Encoded.ADDI (.xreg rd) (.vreg (JoltISA.SystemCSR.vreg csr))
                  (0 : BitVec 12))).run jsScratch =
              .ok RETIRE_SUCCESS jsAfterRd := by
          have hWrite :
              wX_bits rd
                  (jsScratch.vregs (JoltISA.SystemCSR.vreg csr) +
                    sign_extend (m := 64) (0 : BitVec 12))
                  jsScratch.sail =
                .ok () (stateAfterWrite jsScratch.sail rd oldCsr) := by
            rw [hScratchCsr, addi_zero_value]
            exact wX_bits_stateAfterWrite rd oldCsr jsScratch.sail
          simpa [jsAfterRd, oldCsr] using
            JoltISA.addi_run_xreg_vreg rd (JoltISA.SystemCSR.vreg csr)
              (0 : BitVec 12) jsScratch
              (stateAfterWrite jsScratch.sail rd oldCsr) hWrite
        have hScratchVal :
            jsAfterRd.vregs JoltISA.systemScratchVReg = rs1Val := by
          simp [jsAfterRd, jsScratch, joltSetVReg, vregWrite_self]
        have hCsrRun :
            (JoltISA.execInstr
                (.OR (.vreg (JoltISA.SystemCSR.vreg csr))
                  (.vreg (JoltISA.SystemCSR.vreg csr))
                  (.vreg JoltISA.systemScratchVReg))).run jsAfterRd =
              .ok RETIRE_SUCCESS
                (csrrsAfterSameReg js csr rd oldCsr rs1Val) := by
          have hRun :=
            or_run_vreg_vreg_vreg (JoltISA.SystemCSR.vreg csr)
              (JoltISA.SystemCSR.vreg csr) JoltISA.systemScratchVReg
              jsAfterRd (systemCSR_vreg_writable csr)
          simpa [csrrsAfterSameReg, joltSetVReg, vregWrite, jsAfterRd,
            jsScratch, oldCsr, hScratchVal, hScratchCsr,
            systemCSR_vreg_ne_scratch csr] using hRun
        rw [JoltISA.execProgram_instr_run_retire _ _ js jsScratch hScratchRun]
        rw [JoltISA.execProgram_instr_run_retire _ _ jsScratch jsAfterRd hRdRun]
        rw [JoltISA.execProgram_instr_run_retire _ _ jsAfterRd
          (csrrsAfterSameReg js csr rd oldCsr rs1Val) hCsrRun]
        simp only [oldCsr, JoltISA.execProgram_done, EStateM.run, pure,
          EStateM.pure, systemProjectResult]
    · simp only [if_true]
      have hCsrRun :
          (JoltISA.execInstr
              (.OR (.vreg (JoltISA.SystemCSR.vreg csr))
                (.vreg (JoltISA.SystemCSR.vreg csr)) (.xreg rs1))).run js =
            .ok RETIRE_SUCCESS (csrrsAfterCsrSet js csr rs1Val) := by
        have hRun :=
          or_run_vreg_vreg_xreg (JoltISA.SystemCSR.vreg csr)
            (JoltISA.SystemCSR.vreg csr) rs1 js rs1Val hSource
            (systemCSR_vreg_writable csr)
        simpa [csrrsAfterCsrSet, csrrsWriteValue, joltSetVReg, vregWrite] using
          hRun
      rw [JoltISA.execProgram_instr_run_retire _ _ js
        (csrrsAfterCsrSet js csr rs1Val) hCsrRun]
      simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure,
        systemProjectResult]
  · cases hRd : JoltISA.isX0 rd
    · simp only [Bool.true_and, Bool.false_eq_true, if_false, if_true]
      have hReadRun :
          (JoltISA.execInstr
              (JoltISA.Encoded.ADDI (.xreg rd) (.vreg (JoltISA.SystemCSR.vreg csr))
                (0 : BitVec 12))).run js =
            .ok RETIRE_SUCCESS (csrrsAfterReadOnly js csr rd) := by
        have hWrite :
            wX_bits rd
                (js.vregs (JoltISA.SystemCSR.vreg csr) +
                  sign_extend (m := 64) (0 : BitVec 12))
                js.sail =
              .ok () (stateAfterWrite js.sail (rd) (js.vregs (JoltISA.SystemCSR.vreg csr))) := by
          rw [addi_zero_value]
          exact wX_bits_stateAfterWrite rd (js.vregs (JoltISA.SystemCSR.vreg csr))
            js.sail
        simpa [csrrsAfterReadOnly] using
          JoltISA.addi_run_xreg_vreg rd (JoltISA.SystemCSR.vreg csr)
            (0 : BitVec 12) js
            (stateAfterWrite js.sail rd (js.vregs (JoltISA.SystemCSR.vreg csr)))
            hWrite
      rw [JoltISA.execProgram_instr_run_retire _ _ js
        (csrrsAfterReadOnly js csr rd) hReadRun]
      simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure,
        systemProjectResult]
    · -- Rust emits the canonical no-op when both registers are x0. The
      -- read-only final state is unchanged because the write to x0 is discarded.
      simp only [Bool.and_self, if_true]
      rw [JoltISA.pureWritebackRdZeroProgram_run js]
      simp only [csrrsAfterReadOnly, stateAfterWrite_of_isX0_true hRd,
        systemProjectResult]

/-! ## Sail-side generic CSRRS helpers -/

private theorem execute_CSRReg_CSRRS_machine_run
    (js : SailJoltState) (addr : BitVec 12) (rs1 rd : regidx)
    (rs1Val oldCsr newVal : BitVec 64) (sAfterCsrWrite : SailState)
    (hSourceSail :
      rX_bits rs1 (systemProject js) = .ok rs1Val (systemProject js))
    (hCurPrivProject :
      (systemProject js).regs.get? Register.cur_privilege =
        some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hCheck :
      check_CSR addr Privilege.Machine
          (csr_access_type csrop.CSRRS (rd == zreg) (rs1 == zreg))
          (systemProject js) =
        .ok true (systemProject js))
    (hRead :
      read_CSR addr (systemProject js) =
        .ok oldCsr (systemProject js))
    (hReadCallback :
      csr_id_read_callback addr oldCsr (systemProject js) =
        .ok () (systemProject js))
    (hNewVal : newVal = oldCsr ||| rs1Val)
    (hWrite :
      (rs1 == zreg) = false →
      write_CSR addr newVal (systemProject js) =
        .ok (Ok newVal) sAfterCsrWrite)
    (hWriteCallback :
      (rs1 == zreg) = false →
      csr_id_write_callback addr newVal sAfterCsrWrite =
        .ok () sAfterCsrWrite) :
    (execute_CSRReg addr rs1 rd csrop.CSRRS).run (systemProject js) =
      if rs1 == zreg then
        .ok RETIRE_SUCCESS
          (stateAfterWrite (systemProject js) rd oldCsr)
      else
        .ok RETIRE_SUCCESS
          (stateAfterWrite sAfterCsrWrite rd oldCsr) := by
  simp only [EStateM.run, execute_CSRReg, bind, EStateM.bind]
  simp only [hSourceSail]
  simp only [doCSR]
  simp only [bind, EStateM.bind]
  unfold Sail.readReg PreSail.readReg
  simp only [bind, EStateM.bind, pure, get, getThe, MonadStateOf.get, EStateM.get]
  simp only [EStateM.pure, hCurPrivProject]
  simp only [hCheck]
  simp only [LeanRV64D.Functions.not]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  simp only [EStateM.bind, EStateM.get]
  simp only [hCurPrivProject, EStateM.pure]
  simp only [ext_check_CSR, Bool.not_true, Bool.false_eq_true, if_false, EStateM.bind]
  cases hRs1 : rs1 == zreg
  · simp only [Bool.false_eq_true, if_false, csr_access_type]
    have hReadAccess :
        (CSRAccessType.CSRReadWrite != CSRAccessType.CSRWrite) = true := by decide
    simp only [hReadAccess, if_true]
    simp only [hRead]
    have hWriteAccess :
        (CSRAccessType.CSRReadWrite != CSRAccessType.CSRRead) = true := by decide
    simp only [hWriteAccess, if_true, EStateM.bind]
    rw [← hNewVal]
    simp only [hWrite hRs1, EStateM.bind]
    simp only [hWriteCallback hRs1]
    rw [wX_bits_stateAfterWrite rd oldCsr sAfterCsrWrite]
    simp only [EStateM.pure]
  · simp only [if_true, csr_access_type]
    have hReadAccess :
        (CSRAccessType.CSRRead != CSRAccessType.CSRWrite) = true := by decide
    simp only [hReadAccess, if_true]
    simp only [hRead]
    have hWriteAccess :
        ¬ ((CSRAccessType.CSRRead != CSRAccessType.CSRRead) = true) := by decide
    simp only [hWriteAccess, Bool.false_eq_true, if_false, EStateM.bind]
    simp only [hReadCallback]
    rw [wX_bits_stateAfterWrite rd oldCsr (systemProject js)]
    simp only [EStateM.pure]

/-! ## Sail-side CSR-specific helpers -/

private theorem check_CSR_systemCSR_machine_run
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (access : CSRAccessType) :
    check_CSR csr.address Privilege.Machine access
        (systemProject js) =
      .ok true (systemProject js) := by
  cases csr <;> cases access <;>
    unfold check_CSR check_CSR_priv check_CSR_access is_CSR_accessible
      stateen_allows_CSR_access privLevel_to_CSR_privbits csrPriv csrAccess
      JoltISA.SystemCSR.address zopz0zKzJ_u <;>
    simp [bind, EStateM.bind, pure, EStateM.pure]
  all_goals decide

private theorem csr_id_read_callback_systemCSR_run
    (s : SailState) (csr : JoltISA.SystemCSR) (value : BitVec 64) :
    csr_id_read_callback csr.address value s = .ok () s := by
  cases csr
  · change (EStateM.bind (pure "mstatus")
      (fun name => pure (csr_full_read_callback name 0x300#12 value))) s =
      .ok () s
    unfold csr_full_read_callback
    simp only [EStateM.bind, pure, EStateM.pure]
  · change (EStateM.bind (pure "mtvec")
      (fun name => pure (csr_full_read_callback name 0x305#12 value))) s =
      .ok () s
    unfold csr_full_read_callback
    simp only [EStateM.bind, pure, EStateM.pure]
  · change (EStateM.bind (pure "mscratch")
      (fun name => pure (csr_full_read_callback name 0x340#12 value))) s =
      .ok () s
    unfold csr_full_read_callback
    simp only [EStateM.bind, pure, EStateM.pure]
  · change (EStateM.bind (pure "mepc")
      (fun name => pure (csr_full_read_callback name 0x341#12 value))) s =
      .ok () s
    unfold csr_full_read_callback
    simp only [EStateM.bind, pure, EStateM.pure]
  · change (EStateM.bind (pure "mcause")
      (fun name => pure (csr_full_read_callback name 0x342#12 value))) s =
      .ok () s
    unfold csr_full_read_callback
    simp only [EStateM.bind, pure, EStateM.pure]
  · change (EStateM.bind (pure "mtval")
      (fun name => pure (csr_full_read_callback name 0x343#12 value))) s =
      .ok () s
    unfold csr_full_read_callback
    simp only [EStateM.bind, pure, EStateM.pure]

private theorem csr_id_write_callback_systemCSR_run
    (s : SailState) (csr : JoltISA.SystemCSR) (value : BitVec 64) :
    csr_id_write_callback csr.address value s = .ok () s := by
  cases csr
  · change (EStateM.bind (pure "mstatus")
      (fun name => pure (csr_full_write_callback name 0x300#12 value))) s =
      .ok () s
    unfold csr_full_write_callback
    simp only [EStateM.bind, pure, EStateM.pure]
  · change (EStateM.bind (pure "mtvec")
      (fun name => pure (csr_full_write_callback name 0x305#12 value))) s =
      .ok () s
    unfold csr_full_write_callback
    simp only [EStateM.bind, pure, EStateM.pure]
  · change (EStateM.bind (pure "mscratch")
      (fun name => pure (csr_full_write_callback name 0x340#12 value))) s =
      .ok () s
    unfold csr_full_write_callback
    simp only [EStateM.bind, pure, EStateM.pure]
  · change (EStateM.bind (pure "mepc")
      (fun name => pure (csr_full_write_callback name 0x341#12 value))) s =
      .ok () s
    unfold csr_full_write_callback
    simp only [EStateM.bind, pure, EStateM.pure]
  · change (EStateM.bind (pure "mcause")
      (fun name => pure (csr_full_write_callback name 0x342#12 value))) s =
      .ok () s
    unfold csr_full_write_callback
    simp only [EStateM.bind, pure, EStateM.pure]
  · change (EStateM.bind (pure "mtval")
      (fun name => pure (csr_full_write_callback name 0x343#12 value))) s =
      .ok () s
    unfold csr_full_write_callback
    simp only [EStateM.bind, pure, EStateM.pure]

private theorem read_CSR_mtvec_run
    (js : SailJoltState) :
    read_CSR JoltISA.SystemCSR.mtvec.address (systemProject js) =
      .ok (js.vregs JoltISA.trapHandlerVReg) (systemProject js) := by
  change (get_mtvec ()) (systemProject js) =
    .ok (js.vregs JoltISA.trapHandlerVReg) (systemProject js)
  unfold get_mtvec Sail.readReg PreSail.readReg
  simp only [systemProject_mtvec_read js, bind, EStateM.bind, pure,
    EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]

private theorem extractLsb_xlen_full_width (value : BitVec 64) :
    Sail.BitVec.extractLsb value (LeanRV64D.Functions.xlen -i 1) 0 = value := by
  change BitVec.extractLsb 63 0 value = value
  ext i
  simp [← BitVec.getLsbD_eq_getElem]
  omega

private theorem read_CSR_mstatus_run
    (js : SailJoltState) :
    read_CSR JoltISA.SystemCSR.mstatus.address (systemProject js) =
      .ok (js.vregs JoltISA.mstatusVReg) (systemProject js) := by
  change (do
      let value ← Sail.readReg Register.mstatus
      pure (Sail.BitVec.extractLsb value (LeanRV64D.Functions.xlen -i 1) 0))
      (systemProject js) =
    .ok (js.vregs JoltISA.mstatusVReg) (systemProject js)
  unfold Sail.readReg PreSail.readReg
  simp only [systemProject_mstatus_read js, bind, EStateM.bind, pure,
    EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]
  rw [extractLsb_xlen_full_width]

private theorem read_CSR_mscratch_run
    (js : SailJoltState) :
    read_CSR JoltISA.SystemCSR.mscratch.address (systemProject js) =
      .ok (js.vregs JoltISA.mscratchVReg) (systemProject js) := by
  change (Sail.readReg Register.mscratch) (systemProject js) =
    .ok (js.vregs JoltISA.mscratchVReg) (systemProject js)
  unfold Sail.readReg PreSail.readReg
  simp only [systemProject_mscratch_read js, bind, EStateM.bind, pure,
    EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]

private theorem read_CSR_mepc_run
    (js : SailJoltState)
    (hLinked : LinkedCSRs js)
    (hAligned :
      Assumptions.MepcReadAligned (js.vregs JoltISA.mepcVReg) js.sail) :
    read_CSR JoltISA.SystemCSR.mepc.address (systemProject js) =
      .ok (js.vregs JoltISA.mepcVReg) (systemProject js) := by
  have hProject : systemProject js = js.sail := by
    simpa [project] using systemProject_eq_project_of_compatible js hLinked
  rw [hProject]
  change (get_xepc Privilege.Machine) js.sail =
    .ok (js.vregs JoltISA.mepcVReg) js.sail
  unfold get_xepc Sail.readReg PreSail.readReg
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
  simp only [hLinked.2.2.2.1.value_eq, pure, EStateM.pure]
  exact hAligned.value_eq

private theorem read_CSR_mcause_run
    (js : SailJoltState) :
    read_CSR JoltISA.SystemCSR.mcause.address (systemProject js) =
      .ok (js.vregs JoltISA.mcauseVReg) (systemProject js) := by
  change (Sail.readReg Register.mcause) (systemProject js) =
    .ok (js.vregs JoltISA.mcauseVReg) (systemProject js)
  unfold Sail.readReg PreSail.readReg
  simp only [systemProject_mcause_read js, bind, EStateM.bind, pure,
    EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]

private theorem read_CSR_mtval_run
    (js : SailJoltState) :
    read_CSR JoltISA.SystemCSR.mtval.address (systemProject js) =
      .ok (js.vregs JoltISA.mtvalVReg) (systemProject js) := by
  change (Sail.readReg Register.mtval) (systemProject js) =
    .ok (js.vregs JoltISA.mtvalVReg) (systemProject js)
  unfold Sail.readReg PreSail.readReg
  simp only [systemProject_mtval_read js, bind, EStateM.bind, pure,
    EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get]

private theorem write_CSR_mtvec_direct_run
    (js : SailJoltState) (value : BitVec 64)
    (h_direct : MtvecWriteDirectMode value) :
    write_CSR JoltISA.SystemCSR.mtvec.address value (systemProject js) =
      .ok (Ok value)
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mtvec value } := by
  change (EStateM.bind (set_mtvec value) (fun x => pure (Ok x))) (systemProject js) =
    .ok (Ok value)
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mtvec value }
  unfold set_mtvec Sail.readReg PreSail.readReg Sail.writeReg PreSail.writeReg
  simp only [systemProject_mtvec_read js, bind, EStateM.bind, pure,
    EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, modify,
    modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  unfold legalize_tvec Mk_Mtvec
  rw [h_direct.mode_eq]
  unfold trapVectorMode_of_bits
  simp only [pure, EStateM.pure, Std.ExtDHashMap.get?_insert_self]

private theorem write_CSR_mscratch_run
    (js : SailJoltState) (value : BitVec 64) :
    write_CSR JoltISA.SystemCSR.mscratch.address value (systemProject js) =
      .ok (Ok value)
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mscratch value } := by
  change (do
      Sail.writeReg Register.mscratch value
      pure (Ok (← Sail.readReg Register.mscratch))) (systemProject js) =
    .ok (Ok value)
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mscratch value }
  unfold Sail.readReg PreSail.readReg Sail.writeReg PreSail.writeReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, get, getThe,
    MonadStateOf.get, EStateM.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, Std.ExtDHashMap.get?_insert_self]

private theorem write_CSR_mepc_legalized_run
    (js : SailJoltState) (value : BitVec 64)
    (hLegal : Assumptions.MepcWriteLegalized value) :
    write_CSR JoltISA.SystemCSR.mepc.address value (systemProject js) =
      .ok (Ok value)
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mepc value } := by
  change (EStateM.bind (set_xepc Privilege.Machine value)
      (fun x => pure (Ok x))) (systemProject js) =
    .ok (Ok value)
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mepc value }
  unfold set_xepc Sail.writeReg PreSail.writeReg
  rw [hLegal.value_eq]
  simp only [bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet]

private theorem write_CSR_mstatus_legalized_run
    (js : SailJoltState) (value : BitVec 64)
    (hLinked : LinkedCSRs js)
    (hLegal :
      Assumptions.MstatusWriteLegalized
        (js.vregs JoltISA.mstatusVReg) value js.sail) :
    write_CSR JoltISA.SystemCSR.mstatus.address value (systemProject js) =
      .ok (Ok value)
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mstatus value } := by
  have hProject : systemProject js = js.sail := by
    simpa [project] using systemProject_eq_project_of_compatible js hLinked
  rw [hProject]
  change (do
      Sail.writeReg Register.mstatus
        (← legalize_mstatus (← Sail.readReg Register.mstatus) value)
      pure (Ok (← Sail.readReg Register.mstatus))) js.sail =
    .ok (Ok value)
      { js.sail with
        regs := js.sail.regs.insert Register.mstatus value }
  unfold Sail.readReg PreSail.readReg Sail.writeReg PreSail.writeReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, get, getThe,
    MonadStateOf.get, EStateM.get, hLinked.1.value_eq]
  rw [hLegal.value_eq]
  simp only [EStateM.pure, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet,
    Std.ExtDHashMap.get?_insert_self]

private theorem write_CSR_mcause_run
    (js : SailJoltState) (value : BitVec 64) :
    write_CSR JoltISA.SystemCSR.mcause.address value (systemProject js) =
      .ok (Ok value)
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mcause value } := by
  change (do
      Sail.writeReg Register.mcause value
      pure (Ok (← Sail.readReg Register.mcause))) (systemProject js) =
    .ok (Ok value)
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mcause value }
  unfold Sail.readReg PreSail.readReg Sail.writeReg PreSail.writeReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, get, getThe,
    MonadStateOf.get, EStateM.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, Std.ExtDHashMap.get?_insert_self]

private theorem write_CSR_mtval_run
    (js : SailJoltState) (value : BitVec 64) :
    write_CSR JoltISA.SystemCSR.mtval.address value (systemProject js) =
      .ok (Ok value)
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mtval value } := by
  change (do
      Sail.writeReg Register.mtval value
      pure (Ok (← Sail.readReg Register.mtval))) (systemProject js) =
    .ok (Ok value)
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mtval value }
  unfold Sail.readReg PreSail.readReg Sail.writeReg PreSail.writeReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, get, getThe,
    MonadStateOf.get, EStateM.get, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, Std.ExtDHashMap.get?_insert_self]

/-! ## Projection helpers -/

private theorem systemProject_csrrsAfterReadOnly
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx) :
    systemProject (csrrsAfterReadOnly js csr rd) =
      stateAfterWrite (systemProject js) rd
        (js.vregs (JoltISA.SystemCSR.vreg csr)) := by
  exact systemProject_stateAfterWrite js rd (js.vregs (JoltISA.SystemCSR.vreg csr))

private theorem systemProject_csrrsAfterCsrSet_mtvec
    (js : SailJoltState) (rs1Val : BitVec 64) :
    systemProject (csrrsAfterCsrSet js JoltISA.SystemCSR.mtvec rs1Val) =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mtvec
          (js.vregs JoltISA.trapHandlerVReg ||| rs1Val) } := by
  unfold csrrsAfterCsrSet csrrsWriteValue joltSetVReg systemProject
    JoltISA.SystemCSR.vreg vregWrite
  simp only
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro reg
  cases reg <;>
    simp [Std.ExtDHashMap.get?_insert, JoltISA.mstatusVReg,
      JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
      JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.riscvRegisterBase,
      JoltISA.riscvRegisterCount]

private theorem systemProject_csrrsAfterCsrSet_mstatus
    (js : SailJoltState) (rs1Val : BitVec 64) :
    systemProject (csrrsAfterCsrSet js JoltISA.SystemCSR.mstatus rs1Val) =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mstatus
          (js.vregs JoltISA.mstatusVReg ||| rs1Val) } := by
  unfold csrrsAfterCsrSet csrrsWriteValue joltSetVReg systemProject
    JoltISA.SystemCSR.vreg vregWrite
  simp only
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro reg
  cases reg <;>
    simp [Std.ExtDHashMap.get?_insert, JoltISA.mstatusVReg,
      JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
      JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.riscvRegisterBase,
      JoltISA.riscvRegisterCount]

private theorem systemProject_csrrsAfterCsrSet_mscratch
    (js : SailJoltState) (rs1Val : BitVec 64) :
    systemProject (csrrsAfterCsrSet js JoltISA.SystemCSR.mscratch rs1Val) =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mscratch
          (js.vregs JoltISA.mscratchVReg ||| rs1Val) } := by
  unfold csrrsAfterCsrSet csrrsWriteValue joltSetVReg systemProject
    JoltISA.SystemCSR.vreg vregWrite
  simp only
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro reg
  cases reg <;>
    simp [Std.ExtDHashMap.get?_insert, JoltISA.mstatusVReg,
      JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
      JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.riscvRegisterBase,
      JoltISA.riscvRegisterCount]

private theorem systemProject_csrrsAfterCsrSet_mepc
    (js : SailJoltState) (rs1Val : BitVec 64) :
    systemProject (csrrsAfterCsrSet js JoltISA.SystemCSR.mepc rs1Val) =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mepc
          (js.vregs JoltISA.mepcVReg ||| rs1Val) } := by
  unfold csrrsAfterCsrSet csrrsWriteValue joltSetVReg systemProject
    JoltISA.SystemCSR.vreg vregWrite
  simp only
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro reg
  cases reg <;>
    simp [Std.ExtDHashMap.get?_insert, JoltISA.mstatusVReg,
      JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
      JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.riscvRegisterBase,
      JoltISA.riscvRegisterCount]

private theorem systemProject_csrrsAfterCsrSet_mcause
    (js : SailJoltState) (rs1Val : BitVec 64) :
    systemProject (csrrsAfterCsrSet js JoltISA.SystemCSR.mcause rs1Val) =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mcause
          (js.vregs JoltISA.mcauseVReg ||| rs1Val) } := by
  unfold csrrsAfterCsrSet csrrsWriteValue joltSetVReg systemProject
    JoltISA.SystemCSR.vreg vregWrite
  simp only
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro reg
  cases reg <;>
    simp [Std.ExtDHashMap.get?_insert, JoltISA.mstatusVReg,
      JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
      JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.riscvRegisterBase,
      JoltISA.riscvRegisterCount]

private theorem systemProject_csrrsAfterCsrSet_mtval
    (js : SailJoltState) (rs1Val : BitVec 64) :
    systemProject (csrrsAfterCsrSet js JoltISA.SystemCSR.mtval rs1Val) =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mtval
          (js.vregs JoltISA.mtvalVReg ||| rs1Val) } := by
  unfold csrrsAfterCsrSet csrrsWriteValue joltSetVReg systemProject
    JoltISA.SystemCSR.vreg vregWrite
  simp only
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro reg
  cases reg <;>
    simp [Std.ExtDHashMap.get?_insert, JoltISA.mstatusVReg,
      JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
      JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.riscvRegisterBase,
      JoltISA.riscvRegisterCount]

private theorem systemProject_csrrsAfterReadSet_mtvec
    (js : SailJoltState) (rd : regidx) (rs1Val : BitVec 64) :
    systemProject
        (csrrsAfterReadSet js JoltISA.SystemCSR.mtvec rd
          (js.vregs JoltISA.trapHandlerVReg) rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mtvec
            (js.vregs JoltISA.trapHandlerVReg ||| rs1Val) }
        rd (js.vregs JoltISA.trapHandlerVReg) := by
  rw [← systemProject_csrrsAfterCsrSet_mtvec js rs1Val]
  simpa [csrrsAfterReadSet, csrrsAfterCsrSet, csrrsWriteValue] using
    systemProject_stateAfterWrite
      (csrrsAfterCsrSet js JoltISA.SystemCSR.mtvec rs1Val) rd
      (js.vregs JoltISA.trapHandlerVReg)

private theorem systemProject_csrrsAfterReadSet_mstatus
    (js : SailJoltState) (rd : regidx) (rs1Val : BitVec 64) :
    systemProject
        (csrrsAfterReadSet js JoltISA.SystemCSR.mstatus rd
          (js.vregs JoltISA.mstatusVReg) rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mstatus
            (js.vregs JoltISA.mstatusVReg ||| rs1Val) }
        rd (js.vregs JoltISA.mstatusVReg) := by
  rw [← systemProject_csrrsAfterCsrSet_mstatus js rs1Val]
  simpa [csrrsAfterReadSet, csrrsAfterCsrSet, csrrsWriteValue] using
    systemProject_stateAfterWrite
      (csrrsAfterCsrSet js JoltISA.SystemCSR.mstatus rs1Val) rd
      (js.vregs JoltISA.mstatusVReg)

private theorem systemProject_csrrsAfterReadSet_mscratch
    (js : SailJoltState) (rd : regidx) (rs1Val : BitVec 64) :
    systemProject
        (csrrsAfterReadSet js JoltISA.SystemCSR.mscratch rd
          (js.vregs JoltISA.mscratchVReg) rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mscratch
            (js.vregs JoltISA.mscratchVReg ||| rs1Val) }
        rd (js.vregs JoltISA.mscratchVReg) := by
  rw [← systemProject_csrrsAfterCsrSet_mscratch js rs1Val]
  simpa [csrrsAfterReadSet, csrrsAfterCsrSet, csrrsWriteValue] using
    systemProject_stateAfterWrite
      (csrrsAfterCsrSet js JoltISA.SystemCSR.mscratch rs1Val) rd
      (js.vregs JoltISA.mscratchVReg)

private theorem systemProject_csrrsAfterReadSet_mepc
    (js : SailJoltState) (rd : regidx) (rs1Val : BitVec 64) :
    systemProject
        (csrrsAfterReadSet js JoltISA.SystemCSR.mepc rd
          (js.vregs JoltISA.mepcVReg) rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mepc
            (js.vregs JoltISA.mepcVReg ||| rs1Val) }
        rd (js.vregs JoltISA.mepcVReg) := by
  rw [← systemProject_csrrsAfterCsrSet_mepc js rs1Val]
  simpa [csrrsAfterReadSet, csrrsAfterCsrSet, csrrsWriteValue] using
    systemProject_stateAfterWrite
      (csrrsAfterCsrSet js JoltISA.SystemCSR.mepc rs1Val) rd
      (js.vregs JoltISA.mepcVReg)

private theorem systemProject_csrrsAfterReadSet_mcause
    (js : SailJoltState) (rd : regidx) (rs1Val : BitVec 64) :
    systemProject
        (csrrsAfterReadSet js JoltISA.SystemCSR.mcause rd
          (js.vregs JoltISA.mcauseVReg) rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mcause
            (js.vregs JoltISA.mcauseVReg ||| rs1Val) }
        rd (js.vregs JoltISA.mcauseVReg) := by
  rw [← systemProject_csrrsAfterCsrSet_mcause js rs1Val]
  simpa [csrrsAfterReadSet, csrrsAfterCsrSet, csrrsWriteValue] using
    systemProject_stateAfterWrite
      (csrrsAfterCsrSet js JoltISA.SystemCSR.mcause rs1Val) rd
      (js.vregs JoltISA.mcauseVReg)

private theorem systemProject_csrrsAfterReadSet_mtval
    (js : SailJoltState) (rd : regidx) (rs1Val : BitVec 64) :
    systemProject
        (csrrsAfterReadSet js JoltISA.SystemCSR.mtval rd
          (js.vregs JoltISA.mtvalVReg) rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mtval
            (js.vregs JoltISA.mtvalVReg ||| rs1Val) }
        rd (js.vregs JoltISA.mtvalVReg) := by
  rw [← systemProject_csrrsAfterCsrSet_mtval js rs1Val]
  simpa [csrrsAfterReadSet, csrrsAfterCsrSet, csrrsWriteValue] using
    systemProject_stateAfterWrite
      (csrrsAfterCsrSet js JoltISA.SystemCSR.mtval rs1Val) rd
      (js.vregs JoltISA.mtvalVReg)

private theorem systemProject_csrrsAfterSameReg_eq_readSet
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx)
    (oldCsr rs1Val : BitVec 64)
    (hOld : oldCsr = js.vregs (JoltISA.SystemCSR.vreg csr)) :
    systemProject (csrrsAfterSameReg js csr rd oldCsr rs1Val) =
      systemProject (csrrsAfterReadSet js csr rd oldCsr rs1Val) := by
  subst oldCsr
  cases csr <;>
    unfold csrrsAfterSameReg csrrsAfterReadSet csrrsAfterCsrSet
      csrrsWriteValue joltSetVReg systemProject JoltISA.SystemCSR.vreg
      vregWrite <;>
    simp only <;>
    congr 1

/-! ## Jolt/Sail CSRRS bridge helpers -/

private theorem csrrs_eq_sail_projected_from_facts
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (rs1Val oldCsr newVal : BitVec 64) (sAfterCsrWrite : SailState)
    (hSourceSail :
      rX_bits rs1 (systemProject js) = .ok rs1Val (systemProject js))
    (hCurPrivProject :
      (systemProject js).regs.get? Register.cur_privilege =
        some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hJoltRun :
      systemProjectResult
          ((JoltISA.execProgram (JoltISA.csrrsProgram csr rs1 rd)).run js) =
        .ok RETIRE_SUCCESS
          (systemProject (csrrsJoltFinal js csr rs1 rd rs1Val)))
    (hCheck :
      check_CSR (JoltISA.SystemCSR.address csr) Privilege.Machine
          (csr_access_type csrop.CSRRS (rd == zreg) (rs1 == zreg))
          (systemProject js) =
        .ok true (systemProject js))
    (hRead :
      read_CSR (JoltISA.SystemCSR.address csr) (systemProject js) =
        .ok oldCsr (systemProject js))
    (hReadCallback :
      csr_id_read_callback (JoltISA.SystemCSR.address csr) oldCsr
          (systemProject js) =
        .ok () (systemProject js))
    (hNewVal : newVal = oldCsr ||| rs1Val)
    (hWrite :
      (rs1 == zreg) = false →
      write_CSR (JoltISA.SystemCSR.address csr) newVal (systemProject js) =
        .ok (Ok newVal) sAfterCsrWrite)
    (hWriteCallback :
      (rs1 == zreg) = false →
      csr_id_write_callback (JoltISA.SystemCSR.address csr) newVal
          sAfterCsrWrite =
        .ok () sAfterCsrWrite)
    (hJoltFinalReadOnly :
      (rs1 == zreg) = true →
        systemProject (csrrsJoltFinal js csr rs1 rd rs1Val) =
          stateAfterWrite (systemProject js) rd oldCsr)
    (hJoltFinalSet :
      (rs1 == zreg) = false →
        systemProject (csrrsJoltFinal js csr rs1 rd rs1Val) =
          stateAfterWrite sAfterCsrWrite rd oldCsr) :
    systemProjectResult
        ((JoltISA.execProgram (JoltISA.csrrsProgram csr rs1 rd)).run js) =
      (execute_CSRReg (JoltISA.SystemCSR.address csr) rs1 rd csrop.CSRRS).run
        (systemProject js) := by
  rw [hJoltRun]
  rw [execute_CSRReg_CSRRS_machine_run js (JoltISA.SystemCSR.address csr)
    rs1 rd rs1Val oldCsr newVal sAfterCsrWrite hSourceSail hCurPrivProject
    hCheck hRead hReadCallback hNewVal hWrite hWriteCallback]
  cases hRs1 : rs1 == zreg
  · simp only [Bool.false_eq_true, if_false]
    rw [hJoltFinalSet hRs1]
  · simp only [if_true]
    rw [hJoltFinalReadOnly hRs1]

/-! ## Main theorem -/

def csrrsProgramEqSailStatement
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (_h_sys : CsrrsSystemAssumptions js csr rs1 rd) : Prop :=
  systemProjectResult
      ((JoltISA.execProgram (JoltISA.csrrsProgram csr rs1 rd)).run js) =
    (execute_CSRReg (JoltISA.SystemCSR.address csr) rs1 rd csrop.CSRRS).run
      (systemProject js)

theorem csrrsProgram_eq_sail_projected
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (h_sys : CsrrsSystemAssumptions js csr rs1 rd) :
    csrrsProgramEqSailStatement js csr rs1 rd h_sys := by
  unfold csrrsProgramEqSailStatement
  have hSourceSail :
      rX_bits rs1 (systemProject js) = .ok h_sys.rs1_val (systemProject js) := by
    exact systemProject_rX_bits js rs1 h_sys.rs1_val h_sys.rs1_read
  have hCurPrivProject :
      (systemProject js).regs.get? Register.cur_privilege =
        some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    exact systemProject_cur_privilege_read js h_sys.cur_privilege_machine.value
  cases csr
  · -- `mstatus`
    let oldCsr := js.vregs JoltISA.mstatusVReg
    let newVal := oldCsr ||| h_sys.rs1_val
    let sAfterCsrWrite : SailState :=
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mstatus newVal }
    have hJoltRun :
        systemProjectResult
            ((JoltISA.execProgram
              (JoltISA.csrrsProgram JoltISA.SystemCSR.mstatus rs1 rd)).run js) =
          .ok RETIRE_SUCCESS
            (systemProject
              (csrrsJoltFinal js JoltISA.SystemCSR.mstatus rs1 rd h_sys.rs1_val)) := by
      exact csrrsProgram_project_run js JoltISA.SystemCSR.mstatus rs1 rd
        h_sys.rs1_val h_sys.rs1_read
    exact csrrs_eq_sail_projected_from_facts js JoltISA.SystemCSR.mstatus
      rs1 rd h_sys.rs1_val oldCsr newVal sAfterCsrWrite
      hSourceSail hCurPrivProject hJoltRun
      (check_CSR_systemCSR_machine_run js JoltISA.SystemCSR.mstatus
        (csr_access_type csrop.CSRRS (rd == zreg) (rs1 == zreg)))
      (read_CSR_mstatus_run js)
      (csr_id_read_callback_systemCSR_run (systemProject js)
        JoltISA.SystemCSR.mstatus oldCsr)
      rfl
      (fun hRs1 => write_CSR_mstatus_legalized_run js newVal
        h_sys.linked_csrs (h_sys.mstatus_write_legalized rfl hRs1))
      (fun _ => csr_id_write_callback_systemCSR_run sAfterCsrWrite
        JoltISA.SystemCSR.mstatus newVal)
      (fun hRs1 => by
        unfold csrrsJoltFinal
        rw [isX0_eq_true_of_beq_zreg_true hRs1]
        simp only [if_true]
        exact systemProject_csrrsAfterReadOnly js JoltISA.SystemCSR.mstatus rd)
      (fun hRs1 => by
        unfold csrrsJoltFinal
        rw [isX0_eq_false_of_beq_zreg_false hRs1]
        simp only [Bool.false_eq_true, if_false]
        cases hRd : rd == zreg
        · rw [isX0_eq_false_of_beq_zreg_false hRd]
          simp only [Bool.false_eq_true, if_false]
          cases hSame : JoltISA.sameXReg rd rs1
          · simp only [Bool.false_eq_true, if_false]
            exact systemProject_csrrsAfterReadSet_mstatus js rd h_sys.rs1_val
          · simp only [if_true]
            change
              systemProject
                  (csrrsAfterSameReg js JoltISA.SystemCSR.mstatus rd oldCsr
                    h_sys.rs1_val) =
                stateAfterWrite sAfterCsrWrite rd oldCsr
            rw [systemProject_csrrsAfterSameReg_eq_readSet js
              JoltISA.SystemCSR.mstatus rd oldCsr h_sys.rs1_val rfl]
            exact systemProject_csrrsAfterReadSet_mstatus js rd h_sys.rs1_val
        · rw [isX0_eq_true_of_beq_zreg_true hRd]
          simp only [if_true]
          rw [systemProject_csrrsAfterCsrSet_mstatus]
          exact (stateAfterWrite_of_beq_zreg_true hRd sAfterCsrWrite oldCsr).symm)
  · -- `mtvec`
    let oldCsr := js.vregs JoltISA.trapHandlerVReg
    let newVal := oldCsr ||| h_sys.rs1_val
    let sAfterCsrWrite : SailState :=
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mtvec newVal }
    have hJoltRun :
        systemProjectResult
            ((JoltISA.execProgram
              (JoltISA.csrrsProgram JoltISA.SystemCSR.mtvec rs1 rd)).run js) =
          .ok RETIRE_SUCCESS
            (systemProject
              (csrrsJoltFinal js JoltISA.SystemCSR.mtvec rs1 rd h_sys.rs1_val)) := by
      exact csrrsProgram_project_run js JoltISA.SystemCSR.mtvec rs1 rd
        h_sys.rs1_val h_sys.rs1_read
    exact csrrs_eq_sail_projected_from_facts js JoltISA.SystemCSR.mtvec
      rs1 rd h_sys.rs1_val oldCsr newVal sAfterCsrWrite
      hSourceSail hCurPrivProject hJoltRun
      (check_CSR_systemCSR_machine_run js JoltISA.SystemCSR.mtvec
        (csr_access_type csrop.CSRRS (rd == zreg) (rs1 == zreg)))
      (read_CSR_mtvec_run js)
      (csr_id_read_callback_systemCSR_run (systemProject js)
        JoltISA.SystemCSR.mtvec oldCsr)
      rfl
      (fun hRs1 => write_CSR_mtvec_direct_run js newVal
        (h_sys.mtvec_write_direct rfl hRs1))
      (fun _ => csr_id_write_callback_systemCSR_run sAfterCsrWrite
        JoltISA.SystemCSR.mtvec newVal)
      (fun hRs1 => by
        unfold csrrsJoltFinal
        rw [isX0_eq_true_of_beq_zreg_true hRs1]
        simp only [if_true]
        exact systemProject_csrrsAfterReadOnly js JoltISA.SystemCSR.mtvec rd)
      (fun hRs1 => by
        unfold csrrsJoltFinal
        rw [isX0_eq_false_of_beq_zreg_false hRs1]
        simp only [Bool.false_eq_true, if_false]
        cases hRd : rd == zreg
        · rw [isX0_eq_false_of_beq_zreg_false hRd]
          simp only [Bool.false_eq_true, if_false]
          cases hSame : JoltISA.sameXReg rd rs1
          · simp only [Bool.false_eq_true, if_false]
            exact systemProject_csrrsAfterReadSet_mtvec js rd h_sys.rs1_val
          · simp only [if_true]
            change
              systemProject
                  (csrrsAfterSameReg js JoltISA.SystemCSR.mtvec rd oldCsr
                    h_sys.rs1_val) =
                stateAfterWrite sAfterCsrWrite rd oldCsr
            rw [systemProject_csrrsAfterSameReg_eq_readSet js
              JoltISA.SystemCSR.mtvec rd oldCsr h_sys.rs1_val rfl]
            exact systemProject_csrrsAfterReadSet_mtvec js rd h_sys.rs1_val
        · rw [isX0_eq_true_of_beq_zreg_true hRd]
          simp only [if_true]
          rw [systemProject_csrrsAfterCsrSet_mtvec]
          exact (stateAfterWrite_of_beq_zreg_true hRd sAfterCsrWrite oldCsr).symm)
  · -- `mscratch`
    let oldCsr := js.vregs JoltISA.mscratchVReg
    let newVal := oldCsr ||| h_sys.rs1_val
    let sAfterCsrWrite : SailState :=
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mscratch newVal }
    have hJoltRun :
        systemProjectResult
            ((JoltISA.execProgram
              (JoltISA.csrrsProgram JoltISA.SystemCSR.mscratch rs1 rd)).run js) =
          .ok RETIRE_SUCCESS
            (systemProject
              (csrrsJoltFinal js JoltISA.SystemCSR.mscratch rs1 rd h_sys.rs1_val)) := by
      exact csrrsProgram_project_run js JoltISA.SystemCSR.mscratch rs1 rd
        h_sys.rs1_val h_sys.rs1_read
    exact csrrs_eq_sail_projected_from_facts js JoltISA.SystemCSR.mscratch
      rs1 rd h_sys.rs1_val oldCsr newVal sAfterCsrWrite
      hSourceSail hCurPrivProject hJoltRun
      (check_CSR_systemCSR_machine_run js JoltISA.SystemCSR.mscratch
        (csr_access_type csrop.CSRRS (rd == zreg) (rs1 == zreg)))
      (read_CSR_mscratch_run js)
      (csr_id_read_callback_systemCSR_run (systemProject js)
        JoltISA.SystemCSR.mscratch oldCsr)
      rfl
      (fun _ => write_CSR_mscratch_run js newVal)
      (fun _ => csr_id_write_callback_systemCSR_run sAfterCsrWrite
        JoltISA.SystemCSR.mscratch newVal)
      (fun hRs1 => by
        unfold csrrsJoltFinal
        rw [isX0_eq_true_of_beq_zreg_true hRs1]
        simp only [if_true]
        exact systemProject_csrrsAfterReadOnly js JoltISA.SystemCSR.mscratch rd)
      (fun hRs1 => by
        unfold csrrsJoltFinal
        rw [isX0_eq_false_of_beq_zreg_false hRs1]
        simp only [Bool.false_eq_true, if_false]
        cases hRd : rd == zreg
        · rw [isX0_eq_false_of_beq_zreg_false hRd]
          simp only [Bool.false_eq_true, if_false]
          cases hSame : JoltISA.sameXReg rd rs1
          · simp only [Bool.false_eq_true, if_false]
            exact systemProject_csrrsAfterReadSet_mscratch js rd h_sys.rs1_val
          · simp only [if_true]
            change
              systemProject
                  (csrrsAfterSameReg js JoltISA.SystemCSR.mscratch rd oldCsr
                    h_sys.rs1_val) =
                stateAfterWrite sAfterCsrWrite rd oldCsr
            rw [systemProject_csrrsAfterSameReg_eq_readSet js
              JoltISA.SystemCSR.mscratch rd oldCsr h_sys.rs1_val rfl]
            exact systemProject_csrrsAfterReadSet_mscratch js rd h_sys.rs1_val
        · rw [isX0_eq_true_of_beq_zreg_true hRd]
          simp only [if_true]
          rw [systemProject_csrrsAfterCsrSet_mscratch]
          exact (stateAfterWrite_of_beq_zreg_true hRd sAfterCsrWrite oldCsr).symm)
  · -- `mepc`
    let oldCsr := js.vregs JoltISA.mepcVReg
    let newVal := oldCsr ||| h_sys.rs1_val
    let sAfterCsrWrite : SailState :=
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mepc newVal }
    have hJoltRun :
        systemProjectResult
            ((JoltISA.execProgram
              (JoltISA.csrrsProgram JoltISA.SystemCSR.mepc rs1 rd)).run js) =
          .ok RETIRE_SUCCESS
            (systemProject
              (csrrsJoltFinal js JoltISA.SystemCSR.mepc rs1 rd h_sys.rs1_val)) := by
      exact csrrsProgram_project_run js JoltISA.SystemCSR.mepc rs1 rd
        h_sys.rs1_val h_sys.rs1_read
    exact csrrs_eq_sail_projected_from_facts js JoltISA.SystemCSR.mepc
      rs1 rd h_sys.rs1_val oldCsr newVal sAfterCsrWrite
      hSourceSail hCurPrivProject hJoltRun
      (check_CSR_systemCSR_machine_run js JoltISA.SystemCSR.mepc
        (csr_access_type csrop.CSRRS (rd == zreg) (rs1 == zreg)))
      (read_CSR_mepc_run js h_sys.linked_csrs (h_sys.mepc_read_aligned rfl))
      (csr_id_read_callback_systemCSR_run (systemProject js)
        JoltISA.SystemCSR.mepc oldCsr)
      rfl
      (fun hRs1 => write_CSR_mepc_legalized_run js newVal
        (h_sys.mepc_write_legalized rfl hRs1))
      (fun _ => csr_id_write_callback_systemCSR_run sAfterCsrWrite
        JoltISA.SystemCSR.mepc newVal)
      (fun hRs1 => by
        unfold csrrsJoltFinal
        rw [isX0_eq_true_of_beq_zreg_true hRs1]
        simp only [if_true]
        exact systemProject_csrrsAfterReadOnly js JoltISA.SystemCSR.mepc rd)
      (fun hRs1 => by
        unfold csrrsJoltFinal
        rw [isX0_eq_false_of_beq_zreg_false hRs1]
        simp only [Bool.false_eq_true, if_false]
        cases hRd : rd == zreg
        · rw [isX0_eq_false_of_beq_zreg_false hRd]
          simp only [Bool.false_eq_true, if_false]
          cases hSame : JoltISA.sameXReg rd rs1
          · simp only [Bool.false_eq_true, if_false]
            exact systemProject_csrrsAfterReadSet_mepc js rd h_sys.rs1_val
          · simp only [if_true]
            change
              systemProject
                  (csrrsAfterSameReg js JoltISA.SystemCSR.mepc rd oldCsr
                    h_sys.rs1_val) =
                stateAfterWrite sAfterCsrWrite rd oldCsr
            rw [systemProject_csrrsAfterSameReg_eq_readSet js
              JoltISA.SystemCSR.mepc rd oldCsr h_sys.rs1_val rfl]
            exact systemProject_csrrsAfterReadSet_mepc js rd h_sys.rs1_val
        · rw [isX0_eq_true_of_beq_zreg_true hRd]
          simp only [if_true]
          rw [systemProject_csrrsAfterCsrSet_mepc]
          exact (stateAfterWrite_of_beq_zreg_true hRd sAfterCsrWrite oldCsr).symm)
  · -- `mcause`
    let oldCsr := js.vregs JoltISA.mcauseVReg
    let newVal := oldCsr ||| h_sys.rs1_val
    let sAfterCsrWrite : SailState :=
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mcause newVal }
    have hJoltRun :
        systemProjectResult
            ((JoltISA.execProgram
              (JoltISA.csrrsProgram JoltISA.SystemCSR.mcause rs1 rd)).run js) =
          .ok RETIRE_SUCCESS
            (systemProject
              (csrrsJoltFinal js JoltISA.SystemCSR.mcause rs1 rd h_sys.rs1_val)) := by
      exact csrrsProgram_project_run js JoltISA.SystemCSR.mcause rs1 rd
        h_sys.rs1_val h_sys.rs1_read
    exact csrrs_eq_sail_projected_from_facts js JoltISA.SystemCSR.mcause
      rs1 rd h_sys.rs1_val oldCsr newVal sAfterCsrWrite
      hSourceSail hCurPrivProject hJoltRun
      (check_CSR_systemCSR_machine_run js JoltISA.SystemCSR.mcause
        (csr_access_type csrop.CSRRS (rd == zreg) (rs1 == zreg)))
      (read_CSR_mcause_run js)
      (csr_id_read_callback_systemCSR_run (systemProject js)
        JoltISA.SystemCSR.mcause oldCsr)
      rfl
      (fun _ => write_CSR_mcause_run js newVal)
      (fun _ => csr_id_write_callback_systemCSR_run sAfterCsrWrite
        JoltISA.SystemCSR.mcause newVal)
      (fun hRs1 => by
        unfold csrrsJoltFinal
        rw [isX0_eq_true_of_beq_zreg_true hRs1]
        simp only [if_true]
        exact systemProject_csrrsAfterReadOnly js JoltISA.SystemCSR.mcause rd)
      (fun hRs1 => by
        unfold csrrsJoltFinal
        rw [isX0_eq_false_of_beq_zreg_false hRs1]
        simp only [Bool.false_eq_true, if_false]
        cases hRd : rd == zreg
        · rw [isX0_eq_false_of_beq_zreg_false hRd]
          simp only [Bool.false_eq_true, if_false]
          cases hSame : JoltISA.sameXReg rd rs1
          · simp only [Bool.false_eq_true, if_false]
            exact systemProject_csrrsAfterReadSet_mcause js rd h_sys.rs1_val
          · simp only [if_true]
            change
              systemProject
                  (csrrsAfterSameReg js JoltISA.SystemCSR.mcause rd oldCsr
                    h_sys.rs1_val) =
                stateAfterWrite sAfterCsrWrite rd oldCsr
            rw [systemProject_csrrsAfterSameReg_eq_readSet js
              JoltISA.SystemCSR.mcause rd oldCsr h_sys.rs1_val rfl]
            exact systemProject_csrrsAfterReadSet_mcause js rd h_sys.rs1_val
        · rw [isX0_eq_true_of_beq_zreg_true hRd]
          simp only [if_true]
          rw [systemProject_csrrsAfterCsrSet_mcause]
          exact (stateAfterWrite_of_beq_zreg_true hRd sAfterCsrWrite oldCsr).symm)
  · -- `mtval`
    let oldCsr := js.vregs JoltISA.mtvalVReg
    let newVal := oldCsr ||| h_sys.rs1_val
    let sAfterCsrWrite : SailState :=
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mtval newVal }
    have hJoltRun :
        systemProjectResult
            ((JoltISA.execProgram
              (JoltISA.csrrsProgram JoltISA.SystemCSR.mtval rs1 rd)).run js) =
          .ok RETIRE_SUCCESS
            (systemProject
              (csrrsJoltFinal js JoltISA.SystemCSR.mtval rs1 rd h_sys.rs1_val)) := by
      exact csrrsProgram_project_run js JoltISA.SystemCSR.mtval rs1 rd
        h_sys.rs1_val h_sys.rs1_read
    exact csrrs_eq_sail_projected_from_facts js JoltISA.SystemCSR.mtval
      rs1 rd h_sys.rs1_val oldCsr newVal sAfterCsrWrite
      hSourceSail hCurPrivProject hJoltRun
      (check_CSR_systemCSR_machine_run js JoltISA.SystemCSR.mtval
        (csr_access_type csrop.CSRRS (rd == zreg) (rs1 == zreg)))
      (read_CSR_mtval_run js)
      (csr_id_read_callback_systemCSR_run (systemProject js)
        JoltISA.SystemCSR.mtval oldCsr)
      rfl
      (fun _ => write_CSR_mtval_run js newVal)
      (fun _ => csr_id_write_callback_systemCSR_run sAfterCsrWrite
        JoltISA.SystemCSR.mtval newVal)
      (fun hRs1 => by
        unfold csrrsJoltFinal
        rw [isX0_eq_true_of_beq_zreg_true hRs1]
        simp only [if_true]
        exact systemProject_csrrsAfterReadOnly js JoltISA.SystemCSR.mtval rd)
      (fun hRs1 => by
        unfold csrrsJoltFinal
        rw [isX0_eq_false_of_beq_zreg_false hRs1]
        simp only [Bool.false_eq_true, if_false]
        cases hRd : rd == zreg
        · rw [isX0_eq_false_of_beq_zreg_false hRd]
          simp only [Bool.false_eq_true, if_false]
          cases hSame : JoltISA.sameXReg rd rs1
          · simp only [Bool.false_eq_true, if_false]
            exact systemProject_csrrsAfterReadSet_mtval js rd h_sys.rs1_val
          · simp only [if_true]
            change
              systemProject
                  (csrrsAfterSameReg js JoltISA.SystemCSR.mtval rd oldCsr
                    h_sys.rs1_val) =
                stateAfterWrite sAfterCsrWrite rd oldCsr
            rw [systemProject_csrrsAfterSameReg_eq_readSet js
              JoltISA.SystemCSR.mtval rd oldCsr h_sys.rs1_val rfl]
            exact systemProject_csrrsAfterReadSet_mtval js rd h_sys.rs1_val
        · rw [isX0_eq_true_of_beq_zreg_true hRd]
          simp only [if_true]
          rw [systemProject_csrrsAfterCsrSet_mtval]
          exact (stateAfterWrite_of_beq_zreg_true hRd sAfterCsrWrite oldCsr).symm)

end System

end
