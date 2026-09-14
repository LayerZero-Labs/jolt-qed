import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.Instructions.System.Common

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace System

/-! ## Jolt-side CSRRW helpers -/

private theorem isX0_eq_true_of_beq_zreg_true {rd : regidx}
    (h : (rd == zreg) = true) :
    JoltISA.isX0 rd = true := by
  cases rd with
  | Regidx bits =>
      unfold zreg at h
      unfold JoltISA.isX0
      change (bits == zero_extend (m := 5) 0b00#2) = true at h
      have hBits : bits = zero_extend (m := 5) 0b00#2 := LawfulBEq.eq_of_beq h
      rw [hBits]
      decide

private theorem isX0_eq_false_of_beq_zreg_false {rd : regidx}
    (h : (rd == zreg) = false) :
    JoltISA.isX0 rd = false := by
  cases rd with
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

private theorem regidx_eq_zero_of_beq_zreg_true {rd : regidx}
    (h : (rd == zreg) = true) :
    rd = regidx.Regidx 0 := by
  cases rd with
  | Regidx bits =>
      unfold zreg at h
      change (bits == zero_extend (m := 5) 0b00#2) = true at h
      have hBits : bits = zero_extend (m := 5) 0b00#2 := LawfulBEq.eq_of_beq h
      rw [hBits]
      congr

private theorem stateAfterWrite_of_beq_zreg_true {rd : regidx}
    (h : (rd == zreg) = true) (s : SailState) (value : BitVec 64) :
    stateAfterWrite s rd value = s := by
  rw [regidx_eq_zero_of_beq_zreg_true h]
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

private theorem systemProject_csrrwAfterCsrWrite_mtvec
    (js : SailJoltState) (value : BitVec 64) :
    systemProject (csrrwAfterCsrWrite js JoltISA.SystemCSR.mtvec value) =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mtvec value } := by
  unfold csrrwAfterCsrWrite joltSetVReg systemProject JoltISA.SystemCSR.vreg
    vregWrite
  simp only
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro reg
  cases reg <;>
    simp [Std.ExtDHashMap.get?_insert, JoltISA.mstatusVReg,
      JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
      JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.riscvRegisterBase,
      JoltISA.riscvRegisterCount]

private theorem systemProject_csrrwAfterCsrWrite_mstatus
    (js : SailJoltState) (value : BitVec 64) :
    systemProject (csrrwAfterCsrWrite js JoltISA.SystemCSR.mstatus value) =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mstatus value } := by
  unfold csrrwAfterCsrWrite joltSetVReg systemProject JoltISA.SystemCSR.vreg
    vregWrite
  simp only
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro reg
  cases reg <;>
    simp [Std.ExtDHashMap.get?_insert, JoltISA.mstatusVReg,
      JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
      JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.riscvRegisterBase,
      JoltISA.riscvRegisterCount]

private theorem systemProject_csrrwAfterCsrWrite_mscratch
    (js : SailJoltState) (value : BitVec 64) :
    systemProject (csrrwAfterCsrWrite js JoltISA.SystemCSR.mscratch value) =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mscratch value } := by
  unfold csrrwAfterCsrWrite joltSetVReg systemProject JoltISA.SystemCSR.vreg
    vregWrite
  simp only
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro reg
  cases reg <;>
    simp [Std.ExtDHashMap.get?_insert, JoltISA.mstatusVReg,
      JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
      JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.riscvRegisterBase,
      JoltISA.riscvRegisterCount]

private theorem systemProject_csrrwAfterCsrWrite_mepc
    (js : SailJoltState) (value : BitVec 64) :
    systemProject (csrrwAfterCsrWrite js JoltISA.SystemCSR.mepc value) =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mepc value } := by
  unfold csrrwAfterCsrWrite joltSetVReg systemProject JoltISA.SystemCSR.vreg
    vregWrite
  simp only
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro reg
  cases reg <;>
    simp [Std.ExtDHashMap.get?_insert, JoltISA.mstatusVReg,
      JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
      JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.riscvRegisterBase,
      JoltISA.riscvRegisterCount]

private theorem systemProject_csrrwAfterCsrWrite_mcause
    (js : SailJoltState) (value : BitVec 64) :
    systemProject (csrrwAfterCsrWrite js JoltISA.SystemCSR.mcause value) =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mcause value } := by
  unfold csrrwAfterCsrWrite joltSetVReg systemProject JoltISA.SystemCSR.vreg
    vregWrite
  simp only
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro reg
  cases reg <;>
    simp [Std.ExtDHashMap.get?_insert, JoltISA.mstatusVReg,
      JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
      JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.riscvRegisterBase,
      JoltISA.riscvRegisterCount]

private theorem systemProject_csrrwAfterCsrWrite_mtval
    (js : SailJoltState) (value : BitVec 64) :
    systemProject (csrrwAfterCsrWrite js JoltISA.SystemCSR.mtval value) =
      { systemProject js with
        regs := (systemProject js).regs.insert Register.mtval value } := by
  unfold csrrwAfterCsrWrite joltSetVReg systemProject JoltISA.SystemCSR.vreg
    vregWrite
  simp only
  congr 1
  apply Std.ExtDHashMap.ext_get?
  intro reg
  cases reg <;>
    simp [Std.ExtDHashMap.get?_insert, JoltISA.mstatusVReg,
      JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
      JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.riscvRegisterBase,
      JoltISA.riscvRegisterCount]

private theorem systemProject_csrrwAfterReadWrite_mtvec
    (js : SailJoltState) (rd : regidx) (oldCsr rs1Val : BitVec 64) :
    systemProject
        (csrrwAfterReadWrite js JoltISA.SystemCSR.mtvec rd oldCsr rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mtvec rs1Val }
        rd oldCsr := by
  rw [← systemProject_csrrwAfterCsrWrite_mtvec js rs1Val]
  simpa [csrrwAfterReadWrite, csrrwAfterCsrWrite, joltSetVReg] using
    systemProject_stateAfterWrite
      (csrrwAfterCsrWrite js JoltISA.SystemCSR.mtvec rs1Val) rd oldCsr

private theorem systemProject_csrrwAfterReadWrite_mstatus
    (js : SailJoltState) (rd : regidx) (oldCsr rs1Val : BitVec 64) :
    systemProject
        (csrrwAfterReadWrite js JoltISA.SystemCSR.mstatus rd oldCsr rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mstatus rs1Val }
        rd oldCsr := by
  rw [← systemProject_csrrwAfterCsrWrite_mstatus js rs1Val]
  simpa [csrrwAfterReadWrite, csrrwAfterCsrWrite, joltSetVReg] using
    systemProject_stateAfterWrite
      (csrrwAfterCsrWrite js JoltISA.SystemCSR.mstatus rs1Val) rd oldCsr

private theorem systemProject_csrrwAfterReadWrite_mscratch
    (js : SailJoltState) (rd : regidx) (oldCsr rs1Val : BitVec 64) :
    systemProject
        (csrrwAfterReadWrite js JoltISA.SystemCSR.mscratch rd oldCsr rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mscratch rs1Val }
        rd oldCsr := by
  rw [← systemProject_csrrwAfterCsrWrite_mscratch js rs1Val]
  simpa [csrrwAfterReadWrite, csrrwAfterCsrWrite, joltSetVReg] using
    systemProject_stateAfterWrite
      (csrrwAfterCsrWrite js JoltISA.SystemCSR.mscratch rs1Val) rd oldCsr

private theorem systemProject_csrrwAfterReadWrite_mepc
    (js : SailJoltState) (rd : regidx) (oldCsr rs1Val : BitVec 64) :
    systemProject
        (csrrwAfterReadWrite js JoltISA.SystemCSR.mepc rd oldCsr rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mepc rs1Val }
        rd oldCsr := by
  rw [← systemProject_csrrwAfterCsrWrite_mepc js rs1Val]
  simpa [csrrwAfterReadWrite, csrrwAfterCsrWrite, joltSetVReg] using
    systemProject_stateAfterWrite
      (csrrwAfterCsrWrite js JoltISA.SystemCSR.mepc rs1Val) rd oldCsr

private theorem systemProject_csrrwAfterReadWrite_mcause
    (js : SailJoltState) (rd : regidx) (oldCsr rs1Val : BitVec 64) :
    systemProject
        (csrrwAfterReadWrite js JoltISA.SystemCSR.mcause rd oldCsr rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mcause rs1Val }
        rd oldCsr := by
  rw [← systemProject_csrrwAfterCsrWrite_mcause js rs1Val]
  simpa [csrrwAfterReadWrite, csrrwAfterCsrWrite, joltSetVReg] using
    systemProject_stateAfterWrite
      (csrrwAfterCsrWrite js JoltISA.SystemCSR.mcause rs1Val) rd oldCsr

private theorem systemProject_csrrwAfterReadWrite_mtval
    (js : SailJoltState) (rd : regidx) (oldCsr rs1Val : BitVec 64) :
    systemProject
        (csrrwAfterReadWrite js JoltISA.SystemCSR.mtval rd oldCsr rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mtval rs1Val }
        rd oldCsr := by
  rw [← systemProject_csrrwAfterCsrWrite_mtval js rs1Val]
  simpa [csrrwAfterReadWrite, csrrwAfterCsrWrite, joltSetVReg] using
    systemProject_stateAfterWrite
      (csrrwAfterCsrWrite js JoltISA.SystemCSR.mtval rs1Val) rd oldCsr

private theorem systemProject_csrrwAfterSameReg_eq_readWrite
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rd : regidx)
    (oldCsr rs1Val : BitVec 64) :
    systemProject (csrrwAfterSameReg js csr rd oldCsr rs1Val) =
      systemProject (csrrwAfterReadWrite js csr rd oldCsr rs1Val) := by
  cases csr <;>
    unfold csrrwAfterSameReg csrrwAfterReadWrite joltSetVReg systemProject
      JoltISA.SystemCSR.vreg vregWrite <;>
    simp only <;>
    congr 1

private theorem csrrwProgram_project_run
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (rs1Val : BitVec 64)
    (hSource : rX_bits rs1 js.sail = .ok rs1Val js.sail) :
    systemProjectResult
        ((JoltISA.execProgram
          (JoltISA.csrrwProgram csr rs1 rd)).run js) =
      .ok RETIRE_SUCCESS
        (systemProject
          (csrrwJoltFinal js csr rs1 rd rs1Val)) := by
  unfold JoltISA.csrrwProgram csrrwJoltFinal
  cases hRd : JoltISA.isX0 rd
  · simp only [Bool.false_eq_true, if_false]
    cases hSame : JoltISA.sameXReg rd rs1
    · simp only [Bool.false_eq_true, if_false]
      let oldCsr := js.vregs (JoltISA.SystemCSR.vreg csr)
      let jsAfterRd : SailJoltState :=
        { sail := stateAfterWrite js.sail rd oldCsr, vregs := js.vregs }
      have hRdRun :
          (JoltISA.execInstr
              (.ADDI (.xreg rd) (.vreg (JoltISA.SystemCSR.vreg csr))
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
              (.ADDI (.vreg (JoltISA.SystemCSR.vreg csr)) (.xreg rs1)
                (0 : BitVec 12))).run jsAfterRd =
            .ok RETIRE_SUCCESS
              (csrrwAfterReadWrite js csr rd oldCsr rs1Val) := by
        have hRun :=
          JoltISA.addi_run_vreg_xreg (JoltISA.SystemCSR.vreg csr) rs1
            (0 : BitVec 12) jsAfterRd rs1Val hSourceAfter
            (systemCSR_vreg_writable csr)
        rw [addi_zero_value] at hRun
        simpa [csrrwAfterReadWrite, joltSetVReg, vregWrite, jsAfterRd,
          oldCsr] using hRun
      rw [JoltISA.execProgram_instr_run_retire _ _ js jsAfterRd hRdRun]
      rw [JoltISA.execProgram_instr_run_retire _ _ jsAfterRd
        (csrrwAfterReadWrite js csr rd oldCsr rs1Val) hCsrRun]
      simp only [oldCsr, JoltISA.execProgram_done, EStateM.run, pure,
        EStateM.pure, systemProjectResult]
    · simp only [if_true]
      let oldCsr := js.vregs (JoltISA.SystemCSR.vreg csr)
      let jsScratch : SailJoltState :=
        joltSetVReg js JoltISA.systemScratchVReg rs1Val
      let jsAfterRd : SailJoltState :=
        { sail := stateAfterWrite jsScratch.sail rd oldCsr
          vregs := jsScratch.vregs }
      have hScratchRun :
          (JoltISA.execInstr
              (.ADDI (.vreg JoltISA.systemScratchVReg) (.xreg rs1)
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
              (.ADDI (.xreg rd) (.vreg (JoltISA.SystemCSR.vreg csr))
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
              (.ADDI (.vreg (JoltISA.SystemCSR.vreg csr))
                (.vreg JoltISA.systemScratchVReg) (0 : BitVec 12))).run
              jsAfterRd =
            .ok RETIRE_SUCCESS
              (csrrwAfterSameReg js csr rd oldCsr rs1Val) := by
        have hRun :=
          JoltISA.addi_run_vreg_vreg (JoltISA.SystemCSR.vreg csr)
            JoltISA.systemScratchVReg (0 : BitVec 12) jsAfterRd
            (systemCSR_vreg_writable csr)
        rw [addi_zero_value] at hRun
        simpa [csrrwAfterSameReg, joltSetVReg, vregWrite, jsAfterRd,
          jsScratch, oldCsr, hScratchVal] using hRun
      rw [JoltISA.execProgram_instr_run_retire _ _ js jsScratch hScratchRun]
      rw [JoltISA.execProgram_instr_run_retire _ _ jsScratch jsAfterRd hRdRun]
      rw [JoltISA.execProgram_instr_run_retire _ _ jsAfterRd
        (csrrwAfterSameReg js csr rd oldCsr rs1Val) hCsrRun]
      simp only [oldCsr, JoltISA.execProgram_done, EStateM.run, pure,
        EStateM.pure, systemProjectResult]
  · simp only [if_true]
    have hCsrRun :
        (JoltISA.execInstr
            (.ADDI (.vreg (JoltISA.SystemCSR.vreg csr)) (.xreg rs1)
              (0 : BitVec 12))).run js =
          .ok RETIRE_SUCCESS (csrrwAfterCsrWrite js csr rs1Val) := by
      have hRun :=
        JoltISA.addi_run_vreg_xreg (JoltISA.SystemCSR.vreg csr) rs1
          (0 : BitVec 12) js rs1Val hSource (systemCSR_vreg_writable csr)
      rw [addi_zero_value] at hRun
      simpa [csrrwAfterCsrWrite, joltSetVReg, vregWrite] using hRun
    rw [JoltISA.execProgram_instr_run_retire _ _ js
      (csrrwAfterCsrWrite js csr rs1Val) hCsrRun]
    simp only [JoltISA.execProgram_done, EStateM.run, pure, EStateM.pure,
      systemProjectResult]

private theorem csrrwProgram_mtvec_project_run
    (js : SailJoltState) (rs1 rd : regidx) (rs1Val : BitVec 64)
    (hSource : rX_bits rs1 js.sail = .ok rs1Val js.sail) :
    systemProjectResult
        ((JoltISA.execProgram
          (JoltISA.csrrwProgram JoltISA.SystemCSR.mtvec rs1 rd)).run js) =
      .ok RETIRE_SUCCESS
        (systemProject
          (csrrwJoltFinal js JoltISA.SystemCSR.mtvec rs1 rd rs1Val)) := by
  exact csrrwProgram_project_run js JoltISA.SystemCSR.mtvec rs1 rd rs1Val
    hSource

private theorem csrrwJoltFinal_mtvec_project_rd_nonzero
    (js : SailJoltState) (rs1 rd : regidx) (rs1Val : BitVec 64)
    (hRd : (rd == zreg) = false) :
    systemProject (csrrwJoltFinal js JoltISA.SystemCSR.mtvec rs1 rd rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mtvec rs1Val }
        rd (js.vregs JoltISA.trapHandlerVReg) := by
  unfold csrrwJoltFinal
  rw [isX0_eq_false_of_beq_zreg_false hRd]
  simp only [Bool.false_eq_true, if_false]
  cases hSame : JoltISA.sameXReg rd rs1
  · simp only [Bool.false_eq_true, if_false]
    exact systemProject_csrrwAfterReadWrite_mtvec js rd
      (js.vregs JoltISA.trapHandlerVReg) rs1Val
  · simp only [if_true]
    rw [systemProject_csrrwAfterSameReg_eq_readWrite]
    exact systemProject_csrrwAfterReadWrite_mtvec js rd
      (js.vregs JoltISA.trapHandlerVReg) rs1Val

private theorem csrrwJoltFinal_mtvec_project_rd_zero
    (js : SailJoltState) (rs1 rd : regidx) (rs1Val : BitVec 64)
    (hRd : (rd == zreg) = true) :
    systemProject (csrrwJoltFinal js JoltISA.SystemCSR.mtvec rs1 rd rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mtvec rs1Val }
        rd (zeros : BitVec 64) := by
  unfold csrrwJoltFinal
  rw [isX0_eq_true_of_beq_zreg_true hRd]
  simp only [if_true]
  rw [systemProject_csrrwAfterCsrWrite_mtvec]
  rw [regidx_eq_zero_of_beq_zreg_true hRd]
  exact stateAfterWrite_regidx_zero
    { systemProject js with
      regs := (systemProject js).regs.insert Register.mtvec rs1Val }
    (zeros : BitVec 64)

/-! ## Sail-side generic CSRRW helpers -/

private theorem execute_CSRReg_CSRRW_machine_run
    (js : SailJoltState) (addr : BitVec 12) (rs1 rd : regidx)
    (rs1Val oldCsr : BitVec 64) (sAfterCsrWrite : SailState)
    (hSourceSail :
      rX_bits rs1 (systemProject js) = .ok rs1Val (systemProject js))
    (hCurPrivProject :
      (systemProject js).regs.get? Register.cur_privilege =
        some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hCheck :
      check_CSR addr Privilege.Machine
          (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
          (systemProject js) =
        .ok true (systemProject js))
    (hRead :
      read_CSR addr (systemProject js) =
        .ok oldCsr (systemProject js))
    (hWrite :
      write_CSR addr rs1Val (systemProject js) =
        .ok (Ok rs1Val) sAfterCsrWrite)
    (hCallback :
      csr_id_write_callback addr rs1Val sAfterCsrWrite =
        .ok () sAfterCsrWrite) :
    (execute_CSRReg addr rs1 rd csrop.CSRRW).run (systemProject js) =
      if rd == zreg then
        .ok RETIRE_SUCCESS
          (stateAfterWrite sAfterCsrWrite rd (zeros : BitVec 64))
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
  cases hRd : rd == zreg
  · simp only [Bool.false_eq_true, if_false, csr_access_type]
    have hReadAccess :
        (CSRAccessType.CSRReadWrite != CSRAccessType.CSRWrite) = true := by decide
    simp only [hReadAccess, if_true]
    simp only [hRead]
    have hWriteAccess :
        (CSRAccessType.CSRReadWrite != CSRAccessType.CSRRead) = true := by decide
    simp only [hWriteAccess, if_true, EStateM.bind]
    simp only [hWrite, EStateM.bind]
    simp only [hCallback]
    rw [wX_bits_stateAfterWrite rd oldCsr sAfterCsrWrite]
    simp only [EStateM.pure]
  · simp only [if_true, csr_access_type]
    have hReadAccess : ¬ ((CSRAccessType.CSRWrite != CSRAccessType.CSRWrite) = true) := by decide
    simp only [hReadAccess, Bool.false_eq_true, if_false, EStateM.pure]
    have hWriteAccess :
        (CSRAccessType.CSRWrite != CSRAccessType.CSRRead) = true := by decide
    simp only [hWriteAccess, if_true, EStateM.bind]
    simp only [hWrite, EStateM.bind]
    simp only [hCallback]
    rw [wX_bits_stateAfterWrite rd (zeros : BitVec 64) sAfterCsrWrite]
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

private theorem csr_id_write_callback_mtvec_run
    (s : SailState) (value : BitVec 64) :
    csr_id_write_callback JoltISA.SystemCSR.mtvec.address value s =
      .ok () s := by
  change (EStateM.bind (pure "mtvec")
      (fun name => pure (csr_full_write_callback name 0x305#12 value))) s =
    .ok () s
  unfold csr_full_write_callback
  simp only [pure, EStateM.pure, EStateM.bind]

private theorem csr_id_write_callback_mstatus_run
    (s : SailState) (value : BitVec 64) :
    csr_id_write_callback JoltISA.SystemCSR.mstatus.address value s =
      .ok () s := by
  change (long_csr_write_callback "mstatus" "mstatush" value) s =
    .ok () s
  exact long_csr_write_callback_mstatus_run s value

private theorem csr_id_write_callback_mscratch_run
    (s : SailState) (value : BitVec 64) :
    csr_id_write_callback JoltISA.SystemCSR.mscratch.address value s =
      .ok () s := by
  change (EStateM.bind (pure "mscratch")
      (fun name => pure (csr_full_write_callback name 0x340#12 value))) s =
    .ok () s
  unfold csr_full_write_callback
  simp only [pure, EStateM.pure, EStateM.bind]

private theorem csr_id_write_callback_mepc_run
    (s : SailState) (value : BitVec 64) :
    csr_id_write_callback JoltISA.SystemCSR.mepc.address value s =
      .ok () s := by
  change (EStateM.bind (pure "mepc")
      (fun name => pure (csr_full_write_callback name 0x341#12 value))) s =
    .ok () s
  unfold csr_full_write_callback
  simp only [pure, EStateM.pure, EStateM.bind]

private theorem csr_id_write_callback_mcause_run
    (s : SailState) (value : BitVec 64) :
    csr_id_write_callback JoltISA.SystemCSR.mcause.address value s =
      .ok () s := by
  change (EStateM.bind (pure "mcause")
      (fun name => pure (csr_full_write_callback name 0x342#12 value))) s =
    .ok () s
  unfold csr_full_write_callback
  simp only [pure, EStateM.pure, EStateM.bind]

private theorem csr_id_write_callback_mtval_run
    (s : SailState) (value : BitVec 64) :
    csr_id_write_callback JoltISA.SystemCSR.mtval.address value s =
      .ok () s := by
  change (EStateM.bind (pure "mtval")
      (fun name => pure (csr_full_write_callback name 0x343#12 value))) s =
    .ok () s
  unfold csr_full_write_callback
  simp only [pure, EStateM.pure, EStateM.bind]

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

/-! ## Jolt/Sail CSRRW bridge helpers -/

private theorem csrrw_eq_sail_projected_from_facts
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (rs1Val oldCsr : BitVec 64) (sAfterCsrWrite : SailState)
    (hSourceSail :
      rX_bits rs1 (systemProject js) = .ok rs1Val (systemProject js))
    (hCurPrivProject :
      (systemProject js).regs.get? Register.cur_privilege =
        some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hJoltRun :
      systemProjectResult
          ((JoltISA.execProgram (JoltISA.csrrwProgram csr rs1 rd)).run js) =
        .ok RETIRE_SUCCESS
          (systemProject (csrrwJoltFinal js csr rs1 rd rs1Val)))
    (hCheck :
      check_CSR (JoltISA.SystemCSR.address csr) Privilege.Machine
          (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
          (systemProject js) =
        .ok true (systemProject js))
    (hRead :
      read_CSR (JoltISA.SystemCSR.address csr) (systemProject js) =
        .ok oldCsr (systemProject js))
    (hWrite :
      write_CSR (JoltISA.SystemCSR.address csr) rs1Val (systemProject js) =
        .ok (Ok rs1Val) sAfterCsrWrite)
    (hCallback :
      csr_id_write_callback (JoltISA.SystemCSR.address csr) rs1Val
          sAfterCsrWrite =
        .ok () sAfterCsrWrite)
    (hJoltFinalNonzero :
      (rd == zreg) = false →
        systemProject (csrrwJoltFinal js csr rs1 rd rs1Val) =
          stateAfterWrite sAfterCsrWrite rd oldCsr)
    (hJoltFinalZero :
      (rd == zreg) = true →
        systemProject (csrrwJoltFinal js csr rs1 rd rs1Val) =
          stateAfterWrite sAfterCsrWrite rd (zeros : BitVec 64)) :
    systemProjectResult
        ((JoltISA.execProgram (JoltISA.csrrwProgram csr rs1 rd)).run js) =
      (execute_CSRReg (JoltISA.SystemCSR.address csr) rs1 rd csrop.CSRRW).run
        (systemProject js) := by
  rw [hJoltRun]
  rw [execute_CSRReg_CSRRW_machine_run js (JoltISA.SystemCSR.address csr)
    rs1 rd rs1Val oldCsr sAfterCsrWrite hSourceSail hCurPrivProject hCheck
    hRead hWrite hCallback]
  cases hRd : rd == zreg
  · simp only [Bool.false_eq_true, if_false]
    rw [hJoltFinalNonzero hRd]
  · simp only [if_true]
    rw [hJoltFinalZero hRd]

/-! ## Specialized CSR theorems -/

private theorem csrrwProgram_mstatus_project_run
    (js : SailJoltState) (rs1 rd : regidx) (rs1Val : BitVec 64)
    (hSource : rX_bits rs1 js.sail = .ok rs1Val js.sail) :
    systemProjectResult
        ((JoltISA.execProgram
          (JoltISA.csrrwProgram JoltISA.SystemCSR.mstatus rs1 rd)).run js) =
      .ok RETIRE_SUCCESS
        (systemProject
          (csrrwJoltFinal js JoltISA.SystemCSR.mstatus rs1 rd rs1Val)) := by
  exact csrrwProgram_project_run js JoltISA.SystemCSR.mstatus rs1 rd
    rs1Val hSource

private theorem csrrwJoltFinal_mstatus_project_rd_nonzero
    (js : SailJoltState) (rs1 rd : regidx) (rs1Val : BitVec 64)
    (hRd : (rd == zreg) = false) :
    systemProject (csrrwJoltFinal js JoltISA.SystemCSR.mstatus rs1 rd rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mstatus rs1Val }
        rd (js.vregs JoltISA.mstatusVReg) := by
  unfold csrrwJoltFinal
  rw [isX0_eq_false_of_beq_zreg_false hRd]
  simp only [Bool.false_eq_true, if_false]
  cases hSame : JoltISA.sameXReg rd rs1
  · simp only [Bool.false_eq_true, if_false]
    exact systemProject_csrrwAfterReadWrite_mstatus js rd
      (js.vregs JoltISA.mstatusVReg) rs1Val
  · simp only [if_true]
    rw [systemProject_csrrwAfterSameReg_eq_readWrite]
    exact systemProject_csrrwAfterReadWrite_mstatus js rd
      (js.vregs JoltISA.mstatusVReg) rs1Val

private theorem csrrwJoltFinal_mstatus_project_rd_zero
    (js : SailJoltState) (rs1 rd : regidx) (rs1Val : BitVec 64)
    (hRd : (rd == zreg) = true) :
    systemProject (csrrwJoltFinal js JoltISA.SystemCSR.mstatus rs1 rd rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mstatus rs1Val }
        rd (zeros : BitVec 64) := by
  unfold csrrwJoltFinal
  rw [isX0_eq_true_of_beq_zreg_true hRd]
  simp only [if_true]
  rw [systemProject_csrrwAfterCsrWrite_mstatus]
  rw [regidx_eq_zero_of_beq_zreg_true hRd]
  exact stateAfterWrite_regidx_zero
    { systemProject js with
      regs := (systemProject js).regs.insert Register.mstatus rs1Val }
    (zeros : BitVec 64)

private theorem csrrw_mstatus_eq_sail_projected
    (js : SailJoltState) (rs1 rd : regidx)
    (h_sys : CsrrwSystemAssumptions js JoltISA.SystemCSR.mstatus rs1 rd) :
    systemProjectResult
        ((JoltISA.execProgram
          (JoltISA.csrrwProgram JoltISA.SystemCSR.mstatus rs1 rd)).run js) =
      (execute_CSRReg JoltISA.SystemCSR.mstatus.address rs1 rd csrop.CSRRW).run
        (systemProject js) := by
  have hSourceSail : rX_bits rs1 (systemProject js) = .ok h_sys.rs1_val (systemProject js) := by
    exact systemProject_rX_bits js rs1 h_sys.rs1_val h_sys.rs1_read
  have hCurPrivProject :
      (systemProject js).regs.get? Register.cur_privilege =
        some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    exact systemProject_cur_privilege_read js h_sys.cur_privilege_machine.value
  let sAfterMstatusWrite : SailState :=
    { systemProject js with
      regs := (systemProject js).regs.insert Register.mstatus h_sys.rs1_val }
  have hCheck : check_CSR JoltISA.SystemCSR.mstatus.address Privilege.Machine
          (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
          (systemProject js) =
        .ok true (systemProject js) := by
    exact check_CSR_systemCSR_machine_run js JoltISA.SystemCSR.mstatus
      (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
  have hReadMstatus :
      read_CSR JoltISA.SystemCSR.mstatus.address (systemProject js) =
        .ok (js.vregs JoltISA.mstatusVReg) (systemProject js) := by
    exact read_CSR_mstatus_run js
  have hWriteMstatus :
      write_CSR JoltISA.SystemCSR.mstatus.address h_sys.rs1_val (systemProject js) =
        .ok (Ok h_sys.rs1_val) sAfterMstatusWrite := by
    exact write_CSR_mstatus_legalized_run js h_sys.rs1_val
      h_sys.linked_csrs (h_sys.mstatus_write_legalized rfl)
  have hWriteCallback :
      csr_id_write_callback JoltISA.SystemCSR.mstatus.address h_sys.rs1_val
          sAfterMstatusWrite =
        .ok () sAfterMstatusWrite := by
    exact csr_id_write_callback_mstatus_run sAfterMstatusWrite h_sys.rs1_val

  exact csrrw_eq_sail_projected_from_facts js JoltISA.SystemCSR.mstatus
    rs1 rd h_sys.rs1_val (js.vregs JoltISA.mstatusVReg) sAfterMstatusWrite
    hSourceSail hCurPrivProject
    (csrrwProgram_mstatus_project_run js rs1 rd h_sys.rs1_val h_sys.rs1_read)
    hCheck hReadMstatus hWriteMstatus hWriteCallback
    (fun hRd => csrrwJoltFinal_mstatus_project_rd_nonzero js rs1 rd h_sys.rs1_val hRd)
    (fun hRd => csrrwJoltFinal_mstatus_project_rd_zero js rs1 rd h_sys.rs1_val hRd)

private theorem csrrw_mtvec_eq_sail_projected
    (js : SailJoltState) (rs1 rd : regidx)
    (h_sys : CsrrwSystemAssumptions js JoltISA.SystemCSR.mtvec rs1 rd) :
    systemProjectResult
        ((JoltISA.execProgram
          (JoltISA.csrrwProgram JoltISA.SystemCSR.mtvec rs1 rd)).run js) =
      (execute_CSRReg JoltISA.SystemCSR.mtvec.address rs1 rd csrop.CSRRW).run
        (systemProject js) := by
  have hSourceSail : rX_bits rs1 (systemProject js) = .ok h_sys.rs1_val (systemProject js) := by
    exact systemProject_rX_bits js rs1 h_sys.rs1_val h_sys.rs1_read
  have hCurPrivProject :
      (systemProject js).regs.get? Register.cur_privilege =
        some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    exact systemProject_cur_privilege_read js h_sys.cur_privilege_machine.value
  let sAfterMtvecWrite : SailState :=
    { systemProject js with
      regs := (systemProject js).regs.insert Register.mtvec h_sys.rs1_val }
  have hCheck : check_CSR JoltISA.SystemCSR.mtvec.address Privilege.Machine
          (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
          (systemProject js) =
        .ok true (systemProject js) := by
    exact check_CSR_systemCSR_machine_run js JoltISA.SystemCSR.mtvec
      (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
  have hReadMtvec :
      read_CSR JoltISA.SystemCSR.mtvec.address (systemProject js) =
        .ok (js.vregs JoltISA.trapHandlerVReg) (systemProject js) := by
    exact read_CSR_mtvec_run js
  have hWriteMtvec :
      write_CSR JoltISA.SystemCSR.mtvec.address h_sys.rs1_val (systemProject js) =
        .ok (Ok h_sys.rs1_val) sAfterMtvecWrite := by
    exact write_CSR_mtvec_direct_run js h_sys.rs1_val
      (h_sys.mtvec_write_direct rfl)
  have hWriteCallback :
      csr_id_write_callback JoltISA.SystemCSR.mtvec.address h_sys.rs1_val sAfterMtvecWrite =
        .ok () sAfterMtvecWrite := by
    exact csr_id_write_callback_mtvec_run sAfterMtvecWrite h_sys.rs1_val

  exact csrrw_eq_sail_projected_from_facts js JoltISA.SystemCSR.mtvec
    rs1 rd h_sys.rs1_val (js.vregs JoltISA.trapHandlerVReg) sAfterMtvecWrite
    hSourceSail hCurPrivProject
    (csrrwProgram_mtvec_project_run js rs1 rd h_sys.rs1_val h_sys.rs1_read)
    hCheck hReadMtvec hWriteMtvec hWriteCallback
    (fun hRd => csrrwJoltFinal_mtvec_project_rd_nonzero js rs1 rd h_sys.rs1_val hRd)
    (fun hRd => csrrwJoltFinal_mtvec_project_rd_zero js rs1 rd h_sys.rs1_val hRd)

private theorem csrrwProgram_mscratch_project_run
    (js : SailJoltState) (rs1 rd : regidx) (rs1Val : BitVec 64)
    (hSource : rX_bits rs1 js.sail = .ok rs1Val js.sail) :
    systemProjectResult
        ((JoltISA.execProgram
          (JoltISA.csrrwProgram JoltISA.SystemCSR.mscratch rs1 rd)).run js) =
      .ok RETIRE_SUCCESS
        (systemProject
          (csrrwJoltFinal js JoltISA.SystemCSR.mscratch rs1 rd rs1Val)) := by
  exact csrrwProgram_project_run js JoltISA.SystemCSR.mscratch rs1 rd
    rs1Val hSource

private theorem csrrwJoltFinal_mscratch_project_rd_nonzero
    (js : SailJoltState) (rs1 rd : regidx) (rs1Val : BitVec 64)
    (hRd : (rd == zreg) = false) :
    systemProject (csrrwJoltFinal js JoltISA.SystemCSR.mscratch rs1 rd rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mscratch rs1Val }
        rd (js.vregs JoltISA.mscratchVReg) := by
  unfold csrrwJoltFinal
  rw [isX0_eq_false_of_beq_zreg_false hRd]
  simp only [Bool.false_eq_true, if_false]
  cases hSame : JoltISA.sameXReg rd rs1
  · simp only [Bool.false_eq_true, if_false]
    exact systemProject_csrrwAfterReadWrite_mscratch js rd
      (js.vregs JoltISA.mscratchVReg) rs1Val
  · simp only [if_true]
    rw [systemProject_csrrwAfterSameReg_eq_readWrite]
    exact systemProject_csrrwAfterReadWrite_mscratch js rd
      (js.vregs JoltISA.mscratchVReg) rs1Val

private theorem csrrwJoltFinal_mscratch_project_rd_zero
    (js : SailJoltState) (rs1 rd : regidx) (rs1Val : BitVec 64)
    (hRd : (rd == zreg) = true) :
    systemProject (csrrwJoltFinal js JoltISA.SystemCSR.mscratch rs1 rd rs1Val) =
      stateAfterWrite
        { systemProject js with
          regs := (systemProject js).regs.insert Register.mscratch rs1Val }
        rd (zeros : BitVec 64) := by
  unfold csrrwJoltFinal
  rw [isX0_eq_true_of_beq_zreg_true hRd]
  simp only [if_true]
  rw [systemProject_csrrwAfterCsrWrite_mscratch]
  rw [regidx_eq_zero_of_beq_zreg_true hRd]
  exact stateAfterWrite_regidx_zero
    { systemProject js with
      regs := (systemProject js).regs.insert Register.mscratch rs1Val }
    (zeros : BitVec 64)

private theorem csrrw_mscratch_eq_sail_projected
    (js : SailJoltState) (rs1 rd : regidx)
    (h_sys : CsrrwSystemAssumptions js JoltISA.SystemCSR.mscratch rs1 rd) :
    systemProjectResult
        ((JoltISA.execProgram
          (JoltISA.csrrwProgram JoltISA.SystemCSR.mscratch rs1 rd)).run js) =
      (execute_CSRReg JoltISA.SystemCSR.mscratch.address rs1 rd csrop.CSRRW).run
        (systemProject js) := by
  have hSourceSail : rX_bits rs1 (systemProject js) = .ok h_sys.rs1_val (systemProject js) := by
    exact systemProject_rX_bits js rs1 h_sys.rs1_val h_sys.rs1_read
  have hCurPrivProject :
      (systemProject js).regs.get? Register.cur_privilege =
        some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    exact systemProject_cur_privilege_read js h_sys.cur_privilege_machine.value
  let sAfterMscratchWrite : SailState :=
    { systemProject js with
      regs := (systemProject js).regs.insert Register.mscratch h_sys.rs1_val }
  have hCheck : check_CSR JoltISA.SystemCSR.mscratch.address Privilege.Machine
          (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
          (systemProject js) =
        .ok true (systemProject js) := by
    exact check_CSR_systemCSR_machine_run js JoltISA.SystemCSR.mscratch
      (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
  have hReadMscratch :
      read_CSR JoltISA.SystemCSR.mscratch.address (systemProject js) =
        .ok (js.vregs JoltISA.mscratchVReg) (systemProject js) := by
    exact read_CSR_mscratch_run js
  have hWriteMscratch :
      write_CSR JoltISA.SystemCSR.mscratch.address h_sys.rs1_val (systemProject js) =
        .ok (Ok h_sys.rs1_val) sAfterMscratchWrite := by
    exact write_CSR_mscratch_run js h_sys.rs1_val
  have hWriteCallback :
      csr_id_write_callback JoltISA.SystemCSR.mscratch.address h_sys.rs1_val
          sAfterMscratchWrite =
        .ok () sAfterMscratchWrite := by
    exact csr_id_write_callback_mscratch_run sAfterMscratchWrite h_sys.rs1_val

  exact csrrw_eq_sail_projected_from_facts js JoltISA.SystemCSR.mscratch
    rs1 rd h_sys.rs1_val (js.vregs JoltISA.mscratchVReg) sAfterMscratchWrite
    hSourceSail hCurPrivProject
    (csrrwProgram_mscratch_project_run js rs1 rd h_sys.rs1_val h_sys.rs1_read)
    hCheck hReadMscratch hWriteMscratch hWriteCallback
    (fun hRd => csrrwJoltFinal_mscratch_project_rd_nonzero js rs1 rd h_sys.rs1_val hRd)
    (fun hRd => csrrwJoltFinal_mscratch_project_rd_zero js rs1 rd h_sys.rs1_val hRd)

private theorem csrrw_mepc_eq_sail_projected
    (js : SailJoltState) (rs1 rd : regidx)
    (h_sys : CsrrwSystemAssumptions js JoltISA.SystemCSR.mepc rs1 rd) :
    systemProjectResult
        ((JoltISA.execProgram
          (JoltISA.csrrwProgram JoltISA.SystemCSR.mepc rs1 rd)).run js) =
      (execute_CSRReg JoltISA.SystemCSR.mepc.address rs1 rd csrop.CSRRW).run
        (systemProject js) := by
  have hSourceSail : rX_bits rs1 (systemProject js) = .ok h_sys.rs1_val (systemProject js) := by
    exact systemProject_rX_bits js rs1 h_sys.rs1_val h_sys.rs1_read
  have hCurPrivProject :
      (systemProject js).regs.get? Register.cur_privilege =
        some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    exact systemProject_cur_privilege_read js h_sys.cur_privilege_machine.value
  let sAfterMepcWrite : SailState :=
    { systemProject js with
      regs := (systemProject js).regs.insert Register.mepc h_sys.rs1_val }
  have hJoltRun :
      systemProjectResult
          ((JoltISA.execProgram
            (JoltISA.csrrwProgram JoltISA.SystemCSR.mepc rs1 rd)).run js) =
        .ok RETIRE_SUCCESS
          (systemProject
            (csrrwJoltFinal js JoltISA.SystemCSR.mepc rs1 rd h_sys.rs1_val)) := by
    exact csrrwProgram_project_run js JoltISA.SystemCSR.mepc rs1 rd
      h_sys.rs1_val h_sys.rs1_read
  have hCheck : check_CSR JoltISA.SystemCSR.mepc.address Privilege.Machine
          (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
          (systemProject js) =
        .ok true (systemProject js) := by
    exact check_CSR_systemCSR_machine_run js JoltISA.SystemCSR.mepc
      (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
  have hReadMepc :
      read_CSR JoltISA.SystemCSR.mepc.address (systemProject js) =
        .ok (js.vregs JoltISA.mepcVReg) (systemProject js) := by
    exact read_CSR_mepc_run js h_sys.linked_csrs
      (h_sys.mepc_read_aligned rfl)
  have hWriteMepc :
      write_CSR JoltISA.SystemCSR.mepc.address h_sys.rs1_val (systemProject js) =
        .ok (Ok h_sys.rs1_val) sAfterMepcWrite := by
    exact write_CSR_mepc_legalized_run js h_sys.rs1_val
      (h_sys.mepc_write_legalized rfl)
  have hWriteCallback :
      csr_id_write_callback JoltISA.SystemCSR.mepc.address h_sys.rs1_val
          sAfterMepcWrite =
        .ok () sAfterMepcWrite := by
    exact csr_id_write_callback_mepc_run sAfterMepcWrite h_sys.rs1_val
  have hJoltFinalNonzero
      (hRd : (rd == zreg) = false) :
      systemProject
          (csrrwJoltFinal js JoltISA.SystemCSR.mepc rs1 rd h_sys.rs1_val) =
        stateAfterWrite sAfterMepcWrite rd (js.vregs JoltISA.mepcVReg) := by
    unfold csrrwJoltFinal
    rw [isX0_eq_false_of_beq_zreg_false hRd]
    simp only [Bool.false_eq_true, if_false]
    cases hSame : JoltISA.sameXReg rd rs1
    · simp only [Bool.false_eq_true, if_false]
      exact systemProject_csrrwAfterReadWrite_mepc js rd
        (js.vregs JoltISA.mepcVReg) h_sys.rs1_val
    · simp only [if_true]
      rw [systemProject_csrrwAfterSameReg_eq_readWrite]
      exact systemProject_csrrwAfterReadWrite_mepc js rd
        (js.vregs JoltISA.mepcVReg) h_sys.rs1_val
  have hJoltFinalZero
      (hRd : (rd == zreg) = true) :
      systemProject
          (csrrwJoltFinal js JoltISA.SystemCSR.mepc rs1 rd h_sys.rs1_val) =
        stateAfterWrite sAfterMepcWrite rd (zeros : BitVec 64) := by
    unfold csrrwJoltFinal
    rw [isX0_eq_true_of_beq_zreg_true hRd]
    simp only [if_true]
    rw [systemProject_csrrwAfterCsrWrite_mepc]
    exact (stateAfterWrite_of_beq_zreg_true hRd sAfterMepcWrite
      (zeros : BitVec 64)).symm

  exact csrrw_eq_sail_projected_from_facts js JoltISA.SystemCSR.mepc
    rs1 rd h_sys.rs1_val (js.vregs JoltISA.mepcVReg) sAfterMepcWrite
    hSourceSail hCurPrivProject hJoltRun hCheck hReadMepc hWriteMepc
    hWriteCallback hJoltFinalNonzero hJoltFinalZero

private theorem csrrw_mcause_eq_sail_projected
    (js : SailJoltState) (rs1 rd : regidx)
    (h_sys : CsrrwSystemAssumptions js JoltISA.SystemCSR.mcause rs1 rd) :
    systemProjectResult
        ((JoltISA.execProgram
          (JoltISA.csrrwProgram JoltISA.SystemCSR.mcause rs1 rd)).run js) =
      (execute_CSRReg JoltISA.SystemCSR.mcause.address rs1 rd csrop.CSRRW).run
        (systemProject js) := by
  have hSourceSail : rX_bits rs1 (systemProject js) = .ok h_sys.rs1_val (systemProject js) := by
    exact systemProject_rX_bits js rs1 h_sys.rs1_val h_sys.rs1_read
  have hCurPrivProject :
      (systemProject js).regs.get? Register.cur_privilege =
        some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    exact systemProject_cur_privilege_read js h_sys.cur_privilege_machine.value
  let sAfterMcauseWrite : SailState :=
    { systemProject js with
      regs := (systemProject js).regs.insert Register.mcause h_sys.rs1_val }
  have hJoltRun :
      systemProjectResult
          ((JoltISA.execProgram
            (JoltISA.csrrwProgram JoltISA.SystemCSR.mcause rs1 rd)).run js) =
        .ok RETIRE_SUCCESS
          (systemProject
            (csrrwJoltFinal js JoltISA.SystemCSR.mcause rs1 rd h_sys.rs1_val)) := by
    exact csrrwProgram_project_run js JoltISA.SystemCSR.mcause rs1 rd
      h_sys.rs1_val h_sys.rs1_read
  have hCheck : check_CSR JoltISA.SystemCSR.mcause.address Privilege.Machine
          (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
          (systemProject js) =
        .ok true (systemProject js) := by
    exact check_CSR_systemCSR_machine_run js JoltISA.SystemCSR.mcause
      (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
  have hReadMcause :
      read_CSR JoltISA.SystemCSR.mcause.address (systemProject js) =
        .ok (js.vregs JoltISA.mcauseVReg) (systemProject js) := by
    exact read_CSR_mcause_run js
  have hWriteMcause :
      write_CSR JoltISA.SystemCSR.mcause.address h_sys.rs1_val (systemProject js) =
        .ok (Ok h_sys.rs1_val) sAfterMcauseWrite := by
    exact write_CSR_mcause_run js h_sys.rs1_val
  have hWriteCallback :
      csr_id_write_callback JoltISA.SystemCSR.mcause.address h_sys.rs1_val
          sAfterMcauseWrite =
        .ok () sAfterMcauseWrite := by
    exact csr_id_write_callback_mcause_run sAfterMcauseWrite h_sys.rs1_val
  have hJoltFinalNonzero
      (hRd : (rd == zreg) = false) :
      systemProject
          (csrrwJoltFinal js JoltISA.SystemCSR.mcause rs1 rd h_sys.rs1_val) =
        stateAfterWrite sAfterMcauseWrite rd (js.vregs JoltISA.mcauseVReg) := by
    unfold csrrwJoltFinal
    rw [isX0_eq_false_of_beq_zreg_false hRd]
    simp only [Bool.false_eq_true, if_false]
    cases hSame : JoltISA.sameXReg rd rs1
    · simp only [Bool.false_eq_true, if_false]
      exact systemProject_csrrwAfterReadWrite_mcause js rd
        (js.vregs JoltISA.mcauseVReg) h_sys.rs1_val
    · simp only [if_true]
      rw [systemProject_csrrwAfterSameReg_eq_readWrite]
      exact systemProject_csrrwAfterReadWrite_mcause js rd
        (js.vregs JoltISA.mcauseVReg) h_sys.rs1_val
  have hJoltFinalZero
      (hRd : (rd == zreg) = true) :
      systemProject
          (csrrwJoltFinal js JoltISA.SystemCSR.mcause rs1 rd h_sys.rs1_val) =
        stateAfterWrite sAfterMcauseWrite rd (zeros : BitVec 64) := by
    unfold csrrwJoltFinal
    rw [isX0_eq_true_of_beq_zreg_true hRd]
    simp only [if_true]
    rw [systemProject_csrrwAfterCsrWrite_mcause]
    exact (stateAfterWrite_of_beq_zreg_true hRd sAfterMcauseWrite
      (zeros : BitVec 64)).symm

  exact csrrw_eq_sail_projected_from_facts js JoltISA.SystemCSR.mcause
    rs1 rd h_sys.rs1_val (js.vregs JoltISA.mcauseVReg) sAfterMcauseWrite
    hSourceSail hCurPrivProject hJoltRun hCheck hReadMcause hWriteMcause
    hWriteCallback hJoltFinalNonzero hJoltFinalZero

private theorem csrrw_mtval_eq_sail_projected
    (js : SailJoltState) (rs1 rd : regidx)
    (h_sys : CsrrwSystemAssumptions js JoltISA.SystemCSR.mtval rs1 rd) :
    systemProjectResult
        ((JoltISA.execProgram
          (JoltISA.csrrwProgram JoltISA.SystemCSR.mtval rs1 rd)).run js) =
      (execute_CSRReg JoltISA.SystemCSR.mtval.address rs1 rd csrop.CSRRW).run
        (systemProject js) := by
  have hSourceSail : rX_bits rs1 (systemProject js) = .ok h_sys.rs1_val (systemProject js) := by
    exact systemProject_rX_bits js rs1 h_sys.rs1_val h_sys.rs1_read
  have hCurPrivProject :
      (systemProject js).regs.get? Register.cur_privilege =
        some (Privilege.Machine : RegisterType Register.cur_privilege) := by
    exact systemProject_cur_privilege_read js h_sys.cur_privilege_machine.value
  let sAfterMtvalWrite : SailState :=
    { systemProject js with
      regs := (systemProject js).regs.insert Register.mtval h_sys.rs1_val }
  have hJoltRun :
      systemProjectResult
          ((JoltISA.execProgram
            (JoltISA.csrrwProgram JoltISA.SystemCSR.mtval rs1 rd)).run js) =
        .ok RETIRE_SUCCESS
          (systemProject
            (csrrwJoltFinal js JoltISA.SystemCSR.mtval rs1 rd h_sys.rs1_val)) := by
    exact csrrwProgram_project_run js JoltISA.SystemCSR.mtval rs1 rd
      h_sys.rs1_val h_sys.rs1_read
  have hCheck : check_CSR JoltISA.SystemCSR.mtval.address Privilege.Machine
          (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
          (systemProject js) =
        .ok true (systemProject js) := by
    exact check_CSR_systemCSR_machine_run js JoltISA.SystemCSR.mtval
      (csr_access_type csrop.CSRRW (rd == zreg) (rs1 == zreg))
  have hReadMtval :
      read_CSR JoltISA.SystemCSR.mtval.address (systemProject js) =
        .ok (js.vregs JoltISA.mtvalVReg) (systemProject js) := by
    exact read_CSR_mtval_run js
  have hWriteMtval :
      write_CSR JoltISA.SystemCSR.mtval.address h_sys.rs1_val (systemProject js) =
        .ok (Ok h_sys.rs1_val) sAfterMtvalWrite := by
    exact write_CSR_mtval_run js h_sys.rs1_val
  have hWriteCallback :
      csr_id_write_callback JoltISA.SystemCSR.mtval.address h_sys.rs1_val
          sAfterMtvalWrite =
        .ok () sAfterMtvalWrite := by
    exact csr_id_write_callback_mtval_run sAfterMtvalWrite h_sys.rs1_val
  have hJoltFinalNonzero
      (hRd : (rd == zreg) = false) :
      systemProject
          (csrrwJoltFinal js JoltISA.SystemCSR.mtval rs1 rd h_sys.rs1_val) =
        stateAfterWrite sAfterMtvalWrite rd (js.vregs JoltISA.mtvalVReg) := by
    unfold csrrwJoltFinal
    rw [isX0_eq_false_of_beq_zreg_false hRd]
    simp only [Bool.false_eq_true, if_false]
    cases hSame : JoltISA.sameXReg rd rs1
    · simp only [Bool.false_eq_true, if_false]
      exact systemProject_csrrwAfterReadWrite_mtval js rd
        (js.vregs JoltISA.mtvalVReg) h_sys.rs1_val
    · simp only [if_true]
      rw [systemProject_csrrwAfterSameReg_eq_readWrite]
      exact systemProject_csrrwAfterReadWrite_mtval js rd
        (js.vregs JoltISA.mtvalVReg) h_sys.rs1_val
  have hJoltFinalZero
      (hRd : (rd == zreg) = true) :
      systemProject
          (csrrwJoltFinal js JoltISA.SystemCSR.mtval rs1 rd h_sys.rs1_val) =
        stateAfterWrite sAfterMtvalWrite rd (zeros : BitVec 64) := by
    unfold csrrwJoltFinal
    rw [isX0_eq_true_of_beq_zreg_true hRd]
    simp only [if_true]
    rw [systemProject_csrrwAfterCsrWrite_mtval]
    exact (stateAfterWrite_of_beq_zreg_true hRd sAfterMtvalWrite
      (zeros : BitVec 64)).symm

  exact csrrw_eq_sail_projected_from_facts js JoltISA.SystemCSR.mtval
    rs1 rd h_sys.rs1_val (js.vregs JoltISA.mtvalVReg) sAfterMtvalWrite
    hSourceSail hCurPrivProject hJoltRun hCheck hReadMtval hWriteMtval
    hWriteCallback hJoltFinalNonzero hJoltFinalZero

/-! ## Main theorem -/

def csrrwProgramEqSailStatement
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (_h_sys : CsrrwSystemAssumptions js csr rs1 rd) : Prop :=
  systemProjectResult
      ((JoltISA.execProgram (JoltISA.csrrwProgram csr rs1 rd)).run js) =
    (execute_CSRReg (JoltISA.SystemCSR.address csr) rs1 rd csrop.CSRRW).run
      (systemProject js)

theorem csrrwProgram_eq_sail_projected
    (js : SailJoltState) (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (h_sys : CsrrwSystemAssumptions js csr rs1 rd) :
    csrrwProgramEqSailStatement js csr rs1 rd h_sys := by
  unfold csrrwProgramEqSailStatement
  cases csr
  · -- `mstatus`
    exact csrrw_mstatus_eq_sail_projected js rs1 rd h_sys
  · -- `mtvec`
    exact csrrw_mtvec_eq_sail_projected js rs1 rd h_sys
  · -- `mscratch`
    exact csrrw_mscratch_eq_sail_projected js rs1 rd h_sys
  · -- `mepc`
    exact csrrw_mepc_eq_sail_projected js rs1 rd h_sys
  · -- `mcause`
    exact csrrw_mcause_eq_sail_projected js rs1 rd h_sys
  · -- `mtval`
    exact csrrw_mtval_eq_sail_projected js rs1 rd h_sys

end System

end
