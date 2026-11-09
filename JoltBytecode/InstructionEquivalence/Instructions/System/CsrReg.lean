import JoltBytecode.InstructionEquivalence.Instructions.System.Csr

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
open LeanRV64D LeanRV64D.Functions

noncomputable section
namespace SystemProofs

/-- Jolt's Boolean source/destination comparison agrees with register equality.
For example, two occurrences of x1 compare equal. -/
theorem sameXReg_iff (a b : regidx) : JoltISA.sameXReg a b = true ↔ a = b := by
  cases a; cases b
  simp [JoltISA.sameXReg]

/-- A zero architectural source reads zero.
For example, CSRRS with rs1 = x0 has an empty update operand. -/
theorem source_zero (rs : regidx) (s : SailState) (v : BitVec 64)
    (hz : JoltISA.isX0 rs = true) (hr : rX_bits rs s = .ok v s) : v = 0#64 := by
  have he := JoltISA.eq_regidx_zero_of_isX0_eq_true hz
  subst rs
  rw [rX_bits_regidx_zero] at hr
  exact (EStateM.Result.ok.inj hr).1.symm

/-- A reserved mtvec source mode removes both mode bits from the dynamic mask.
For example, source 6 produces the mask with its low two bits clear. -/
theorem mtvec_mode_mask (src : BitVec 64) :
    jolt_virtual_shift_right_bitmask_value (src &&& 2#64) =
      if src.getLsbD 1 then ~~~(3#64) else BitVec.allOnes 64 := by
  have hs : src &&& 2#64 = if src.getLsbD 1 then 2#64 else 0#64 := and_singleBit src 1
  rw [hs]
  cases hb : src.getLsbD 1 <;> rfl

/-- XOR with a masked difference selects new bits under the mask and old bits
outside it.
For example, a mask with bits 0 and 1 clear preserves those two old mode bits. -/
theorem xor_mask_select (old src mask : BitVec 64) :
    old ^^^ ((src ^^^ old) &&& mask) = (old &&& ~~~mask) ||| (src &&& mask) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases hm : mask.getLsbD i
  · simp
  · simp only [Bool.and_true, Bool.not_true, Bool.and_false, Bool.false_or]
    rw [Bool.xor_left_comm, Bool.xor_self, Bool.xor_false]

/-- The dynamic mtvec mask either permits every source bit or removes its two
mode bits when the requested mode is reserved.
For example, source 6 masks to base 4. -/
theorem mtvec_source_mask (src : BitVec 64) :
    src &&& jolt_virtual_shift_right_bitmask_value (src &&& 2#64) =
      csrBitMask false .mtvec src := by
  have hs : src &&& 2#64 = if src.getLsbD 1 then 2#64 else 0#64 := and_singleBit src 1
  rw [hs]
  cases hb : src.getLsbD 1
  · have hc : src &&& ~~~(2#64) = src := clearSingleBit_self src 1 hb
    have hb' : src[1] = false := by exact hb
    have hc' : src &&& 18446744073709551613#64 = src := hc
    have ho : src &&& 18446744073709551615#64 = src := BitVec.and_allOnes
    simp [csrBitMask, hs, hb', jolt_virtual_shift_right_bitmask_value, hc', ho]
  · simp [csrBitMask, hs, hb, jolt_virtual_shift_right_bitmask_value]

/-- The full-width operand used by register CSR set/clear rows.
For example, setting mepc masks bit zero, while clearing uses the source directly. -/
def csrRegisterMask (clear : Bool) (csr : JoltISA.SystemCSR) (src : BitVec 64) : BitVec 64 :=
  if clear then src else csrBitMask false csr src

/-- A zero source produces an empty register CSR update mask.
For example, CSRRS with x0 preserves its CSR. -/
theorem csrRegisterMask_zero (clear : Bool) (csr : JoltISA.SystemCSR) :
    csrRegisterMask clear csr 0#64 = 0#64 := by
  cases clear <;> cases csr <;> rfl

/-- Projection commutes with writing an integer destination after replacing
virtual registers.
For example, a scratch update does not change how an old CSR value reaches x1. -/
theorem systemProject_withVRegs_writeRd (js : SailJoltState)
    (regs : JoltISA.VReg → BitVec 64) (rd : regidx) (value : BitVec 64) :
    System.systemProject { js with vregs := regs, sail := stateAfterWrite js.sail rd value } =
      stateAfterWrite (System.systemProject { js with vregs := regs }) rd value := by
  exact Projection.systemProject_stateAfterWrite { js with vregs := regs } rd value

/-- The register-source set/clear program writes its old CSR to rd and updates
that CSR with its compiled operand; scratch registers disappear in projection.
For example, CSRRS with rd = rs1 still uses the source value from before the read. -/
theorem csrBitUpdateProgram_spec (clear : Bool) (csr : JoltISA.SystemCSR)
    (rs1 rd : regidx) (js : SailJoltState) (src : BitVec 64)
    (hr : rX_bits rs1 js.sail = .ok src js.sail) :
    System.systemProjectResult
      (JoltISA.execProgram (JoltISA.csrBitUpdateProgram clear csr rs1 rd) js) =
      .ok RETIRE_SUCCESS
        (stateAfterWrite (Step.csrSet csr.address
          (if csr = .mstatus then
            bitUpdate clear (js.vregs csr.vreg) (csrRegisterMask clear csr src) ||| 0x1800#64
           else bitUpdate clear (js.vregs csr.vreg) (csrRegisterMask clear csr src))
          (System.systemProject js)) rd (csrValue csr js)) := by
  classical
  by_cases hzero : JoltISA.isX0 rs1 = true
  · have hs := source_zero rs1 js.sail src hzero hr
    subst src
    have hp : JoltISA.csrBitUpdateProgram clear csr rs1 rd =
        JoltISA.csrImmediateBitUpdateProgram clear csr 0#5 rd := by
      unfold JoltISA.csrBitUpdateProgram JoltISA.csrImmediateBitUpdateProgram
      rw [csrImmediateMask_zero]
      by_cases hd : JoltISA.isX0 rd = true <;>
        simp [hzero, hd, JoltISA.csrReadInto]
    rw [hp, csrImmediateBitUpdateProgram_run, csrImmediateMask_zero,
      bitUpdate_zero, setCsr_self, csrRegisterMask_zero, bitUpdate_zero]
    simp only [System.systemProjectResult]
    congr 1
    simpa only [setCsr_self] using
      systemProject_setCsr_writeRd js csr (js.vregs csr.vreg) (csrValue csr js) rd
  · have hzero' : JoltISA.isX0 rs1 = false := Bool.eq_false_iff.mpr hzero
    have hread (v : BitVec 64) (hs : JoltISA.sameXReg rd rs1 = false) :
        rX_bits rs1 (stateAfterWrite js.sail rd v) =
          .ok src (stateAfterWrite js.sail rd v) := by
      apply rX_bits_stateAfterWrite_of_ne rd rs1 v src js.sail _ hr
      intro hd
      have ht := (sameXReg_iff rd rs1).mpr hd
      rw [hs] at ht
      contradiction
    have hrd (hs : JoltISA.sameXReg rd rs1 = true) : JoltISA.isX0 rd = false := by
      rw [(sameXReg_iff rd rs1).mp hs]
      exact hzero'
    cases hsame : JoltISA.sameXReg rd rs1 <;> cases csr <;> cases clear <;>
      simp [JoltISA.csrBitUpdateProgram, hzero', hsame, hrd, csrReadInto_run,
        JoltISA.execProgram, JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst,
        liftSail, hr, hread, readVReg, writeVReg, csrValue, bitUpdate, csrRegisterMask,
        csrBitMask, Riscv.andi, Riscv.ori, jolt_andn_value, JoltISA.addWide_low,
        RETIRE_SUCCESS, System.systemProjectResult, systemProject_withVRegs_writeRd, JoltISA.SystemCSR.address, JoltISA.SystemCSR.vreg,
        JoltISA.mstatusVReg, JoltISA.trapHandlerVReg, JoltISA.mscratchVReg,
        JoltISA.mepcVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg,
        JoltISA.reservationWReg, JoltISA.reservationDReg,
        System.extDHashMap_insert_insert_same, System.extDHashMap_insert_comm_of_ne,
        JoltISA.inlineTmp0, JoltISA.inlineTmp1, JoltISA.inlineTmp,
        JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters,
        JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
        bind, EStateM.bind, pure, EStateM.pure, get, getThe,
        MonadStateOf.get, EStateM.get, modify, modifyGet, MonadStateOf.modifyGet,
        EStateM.modifyGet]
    all_goals simp [System.systemProject, Step.csrSet, Step.setReg,
      JoltISA.SystemCSR.address, JoltISA.SystemCSR.vreg,
      JoltISA.mstatusVReg, JoltISA.trapHandlerVReg, JoltISA.mscratchVReg,
      JoltISA.mepcVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg,
      JoltISA.reservationWReg, JoltISA.reservationDReg,
      JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
      mtvec_source_mask, csrBitMask,
      System.extDHashMap_insert_insert_same, System.extDHashMap_insert_comm_of_ne]

/-- The raw value stored by a register CSR swap.
For example, a reserved mtvec mode preserves the old mode and replaces the base. -/
def registerSwapValue (csr : JoltISA.SystemCSR) (old src : BitVec 64) : BitVec 64 :=
  if csr = .mtvec then
    old ^^^ ((src ^^^ old) &&& jolt_virtual_shift_right_bitmask_value (src &&& 2#64))
  else swapValue csr src

/-- The ordinary CSR write suffix stores its masked source in the virtual CSR.
For example, a mepc source of 17 stores 16. -/
theorem csrSwapWrite_run (csr : JoltISA.SystemCSR) (source : JoltISA.Src)
    (js : SailJoltState) (src : BitVec 64)
    (hr : JoltISA.readSrc source js = .ok src js) :
    JoltISA.execProgram (JoltISA.csrSwapWrite csr source) js =
      .ok RETIRE_SUCCESS (setCsr js csr (swapValue csr src)) := by
  have hw := writeCsr_run csr
  cases csr <;> simp only [JoltISA.SystemCSR.vreg] at hw <;>
    simp [JoltISA.csrSwapWrite, JoltISA.execProgram, JoltISA.execInstr,
      hr, JoltISA.writeDst, hw, swapValue, JoltISA.SystemCSR.vreg,
      Riscv.andi, JoltISA.addWide_low, RETIRE_SUCCESS,
      bind, EStateM.bind, pure, EStateM.pure]

/-- A CSR read followed by its ordinary write suffix returns the old value
and stores the supplied source.
For example, a source saved in v40 remains available after writing rd. -/
theorem csrSwapReadWrite_run (csr : JoltISA.SystemCSR) (source : JoltISA.Src)
    (rd : regidx) (js : SailJoltState) (src : BitVec 64)
    (hr : JoltISA.readSrc source { js with sail := stateAfterWrite js.sail rd (csrValue csr js) } =
      .ok src { js with sail := stateAfterWrite js.sail rd (csrValue csr js) }) :
    JoltISA.execProgram (JoltISA.csrReadInto csr rd (JoltISA.csrSwapWrite csr source)) js =
      .ok RETIRE_SUCCESS { setCsr js csr (swapValue csr src) with
        sail := stateAfterWrite js.sail rd (csrValue csr js) } := by
  rw [csrReadInto_run, csrSwapWrite_run csr source _ src hr]
  rfl

/-- An architectural CSR register is distinct from the first scratch register.
For example, mscratch uses v35 rather than v40. -/
theorem csrVReg_neScratch (csr : JoltISA.SystemCSR) : csr.vreg ≠ JoltISA.inlineTmp0 := by
  cases csr <;> decide

/-- Save a CSR source in scratch v40 before reading a possibly aliased rd.
For example, CSRRW x1, mscratch, x1 saves the original x1. -/
def csrSaveSource (js : SailJoltState) (src : BitVec 64) : SailJoltState :=
  { js with vregs := fun r => if r = JoltISA.inlineTmp0 then src else js.vregs r }

/-- Saving a source in scratch preserves the entire projected state.
For example, v40 never supplies Sail's mepc or integer registers. -/
theorem systemProject_csrSaveSource (js : SailJoltState) (src : BitVec 64) :
    System.systemProject (csrSaveSource js src) = System.systemProject js :=
  Projection.systemProject_rdZeroRewriteVReg js src

/-- The source-saving ADDI row copies its source into scratch v40.
For example, copying x1 = 7 saves 7 without changing the Sail state. -/
theorem csrSaveSource_run (rs1 : regidx) (js : SailJoltState) (src : BitVec 64)
    (hr : rX_bits rs1 js.sail = .ok src js.sail) :
    JoltISA.execInstr (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) 0#64) js =
      .ok RETIRE_SUCCESS (csrSaveSource js src) := by
  simp [JoltISA.execInstr, JoltISA.readSrc, liftSail, hr, JoltISA.writeDst,
    writeVReg, csrSaveSource, JoltISA.inlineTmp0, JoltISA.inlineTmp,
    JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters,
    JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount, JoltISA.addWide_low, RETIRE_SUCCESS,
    bind, EStateM.bind, pure, EStateM.pure, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet]

/-- The dynamic mtvec swap path preserves mode bits for a reserved requested
mode and writes the old mtvec to rd.
For example, source 6 replaces BASE while preserving the current MODE. -/
theorem csrrwMtvecProgram_spec (rs1 rd : regidx) (js : SailJoltState) (src : BitVec 64)
    (hz : JoltISA.isX0 rs1 = false) (hr : rX_bits rs1 js.sail = .ok src js.sail) :
    System.systemProjectResult (JoltISA.execProgram (JoltISA.csrrwProgram .mtvec rs1 rd) js) =
      .ok RETIRE_SUCCESS (stateAfterWrite
        (Step.csrSet JoltISA.SystemCSR.mtvec.address
          (registerSwapValue .mtvec (js.vregs JoltISA.trapHandlerVReg) src)
          (System.systemProject js)) rd (csrValue .mtvec js)) := by
  simp [JoltISA.csrrwProgram, hz, csrReadInto_run,
    JoltISA.execProgram, JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst,
    liftSail, hr, readVReg, writeVReg, csrValue, registerSwapValue,
    Riscv.andi, jolt_xor_value, RETIRE_SUCCESS, System.systemProjectResult,
    systemProject_withVRegs_writeRd, JoltISA.SystemCSR.vreg,
    JoltISA.trapHandlerVReg, JoltISA.inlineTmp0, JoltISA.inlineTmp1, JoltISA.inlineTmp,
    JoltISA.inlineRegisterBase, JoltISA.numReservedVirtualRegisters,
    JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
    bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  simp [System.systemProject, Step.csrSet, Step.setReg,
    JoltISA.SystemCSR.address, JoltISA.mstatusVReg, JoltISA.trapHandlerVReg,
    JoltISA.mscratchVReg, JoltISA.mepcVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg,
    JoltISA.reservationWReg, JoltISA.reservationDReg,
    JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
    System.extDHashMap_insert_insert_same, System.extDHashMap_insert_comm_of_ne]

/-- Register swap rows read the old CSR into rd and store the original source,
with the CSR-specific mask.
For example, CSRRW with rd = rs1 preserves the original source in scratch first. -/
theorem csrrwProgram_spec (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (js : SailJoltState) (src : BitVec 64)
    (hr : rX_bits rs1 js.sail = .ok src js.sail) :
    System.systemProjectResult (JoltISA.execProgram (JoltISA.csrrwProgram csr rs1 rd) js) =
      .ok RETIRE_SUCCESS (stateAfterWrite (Step.csrSet csr.address
        (if csr = .mstatus then registerSwapValue csr (js.vregs csr.vreg) src ||| 0x1800#64
         else registerSwapValue csr (js.vregs csr.vreg) src)
        (System.systemProject js)) rd (csrValue csr js)) := by
  classical
  by_cases hspecial : csr = .mtvec ∧ JoltISA.isX0 rs1 = false
  · obtain ⟨rfl, hz⟩ := hspecial
    exact csrrwMtvecProgram_spec rs1 rd js src hz hr
  · have hswap : registerSwapValue csr (js.vregs csr.vreg) src = swapValue csr src := by
      by_cases hc : csr = .mtvec
      · subst csr
        have hz : JoltISA.isX0 rs1 = true := by
          cases h : JoltISA.isX0 rs1 <;> simp_all
        have hs := source_zero rs1 js.sail src hz hr
        subst src
        have hones (v : BitVec 64) : v &&& 18446744073709551615#64 = v := BitVec.and_allOnes
        simp [registerSwapValue, swapValue, jolt_virtual_shift_right_bitmask_value, hones]
      · simp [registerSwapValue, hc]
    rw [hswap]
    unfold JoltISA.csrrwProgram
    rw [if_neg hspecial]
    by_cases ha : (!JoltISA.isX0 rd && JoltISA.sameXReg rd rs1) = true
    · simp only [ha, ↓reduceIte]
      have hcopy := JoltISA.execProgram_instr_run_retire
        (.ADDI (.vreg JoltISA.inlineTmp0) (.xreg rs1) 0#64)
        (JoltISA.csrReadInto csr rd (JoltISA.csrSwapWrite csr (.vreg JoltISA.inlineTmp0)))
        js (csrSaveSource js src) (csrSaveSource_run rs1 js src hr)
      simp only [EStateM.run] at hcopy
      refine (congrArg System.systemProjectResult hcopy).trans ?_
      have hc : (csrSaveSource js src).vregs csr.vreg = js.vregs csr.vreg := by
        simp [csrSaveSource, csrVReg_neScratch]
      have hv : csrValue csr (csrSaveSource js src) = csrValue csr js := by simp [csrValue, hc]
      rw [csrSwapReadWrite_run csr (.vreg JoltISA.inlineTmp0) rd (csrSaveSource js src) src
        (by simp [JoltISA.readSrc, readVReg, csrSaveSource,
          bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get])]
      simp only [System.systemProjectResult, systemProject_setCsr_writeRd,
        systemProject_csrSaveSource, hv]
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      have hp : rX_bits rs1 (stateAfterWrite js.sail rd (csrValue csr js)) =
          .ok src (stateAfterWrite js.sail rd (csrValue csr js)) := by
        by_cases hz : JoltISA.isX0 rd = true
        · simpa only [JoltISA.stateAfterWrite_of_isX0_eq_true hz] using hr
        · apply rX_bits_stateAfterWrite_of_ne rd rs1 _ src js.sail _ hr
          intro hd
          have hs := (sameXReg_iff rd rs1).mpr hd
          simp [hs, hz] at ha
      rw [csrSwapReadWrite_run csr (.xreg rs1) rd js src (by simp [JoltISA.readSrc, liftSail, hp])]
      simp only [System.systemProjectResult, systemProject_setCsr_writeRd]

/-- A register CSR swap stores precisely Sail's legalized value.
For example, swapping mepc with source 17 stores 16. -/
theorem registerSwapValue_legal (csr : JoltISA.SystemCSR) (old src : BitVec 64) :
    (if csr = .mstatus then registerSwapValue csr old src ||| 0x1800#64
      else registerSwapValue csr old src) =
      Step.csrLegal csr.address (if csr = .mstatus then old ||| 0x1800#64 else old) src := by
  cases csr <;> simp [registerSwapValue, swapValue, Step.csrLegal, JoltISA.SystemCSR.address]
  rw [xor_mask_select, mtvec_mode_mask]
  cases hb : src.getLsbD 1 <;> simp_all [BitVec.or_comm]
  exact BitVec.and_allOnes

/-- Register CSR swap rows agree with Sail on the projected machine hart.
The source-read and linked-CSR facts are the usual register-read assumptions.
For example, CSRRW x1, mepc, x1 stores the aligned original x1 and returns old mepc. -/
theorem csrrwProgram_eq_execute (csr : JoltISA.SystemCSR) (rs1 rd : regidx)
    (js : SailJoltState) (src : BitVec 64)
    (hinv : Step.StepInvariant (System.systemProject js))
    (hl : LinkedCSRs js) (hr : rX_bits rs1 js.sail = .ok src js.sail)
    (hm : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88#64) = 0#64)
    (ht : (js.vregs JoltISA.trapHandlerVReg).getLsbD 1 = false)
    (he : (js.vregs JoltISA.mepcVReg).getLsbD 0 = false) :
    System.systemProjectResult (JoltISA.execProgram (JoltISA.csrrwProgram csr rs1 rd) js) =
      execute (.CSRReg (csr.address, rs1, rd, .CSRRW)) (System.systemProject js) := by
  have hrp : rX_bits rs1 (System.systemProject js) = .ok src (System.systemProject js) := by
    rw [Projection.systemProject_eq_sail_of_compatible js hl]
    exact hr
  rw [Step.execute_CSRReg_jolt csr.address (isJoltCsr csr) rs1 rd .CSRRW _
    hinv (csrLegal_project js hm ht he) _ src (csrRead_project csr js) hrp,
    csrrwProgram_spec csr rs1 rd js src hr]
  simp only [true_or, ↓reduceIte, Step.csrApply]
  simpa only [csrValue] using congrArg (fun value =>
    EStateM.Result.ok (ε := Error exception) RETIRE_SUCCESS
      (stateAfterWrite (Step.csrSet csr.address value (System.systemProject js))
        rd (csrValue csr js))) (registerSwapValue_legal csr (js.vregs csr.vreg) src)

/-- Writing the projected value of a CSR back to it preserves the state.
For example, rewriting mscratch with v35 has no effect. -/
theorem csrSet_csrValue_self (csr : JoltISA.SystemCSR) (js : SailJoltState) :
    Step.csrSet csr.address (csrValue csr js) (System.systemProject js) =
      System.systemProject js := by
  simpa only [csrValue, setCsr_self] using
    (systemProject_setCsr js csr (js.vregs csr.vreg)).symm

/-- The register set/clear result is Sail's legalized CSR value.
For example, clearing MIE never changes the fixed Machine privilege bits. -/
theorem registerBitUpdateValue_legal (clear : Bool) (csr : JoltISA.SystemCSR)
    (raw src : BitVec 64)
    (hm : csr = .mstatus → raw &&& ~~~(0x88#64) = 0#64)
    (ht : csr = .mtvec → raw.getLsbD 1 = false)
    (he : csr = .mepc → raw.getLsbD 0 = false) :
    (if csr = .mstatus then bitUpdate clear raw (csrRegisterMask clear csr src) ||| 0x1800#64
     else bitUpdate clear raw (csrRegisterMask clear csr src)) =
      Step.csrLegal csr.address (if csr = .mstatus then raw ||| 0x1800#64 else raw)
        (Step.csrApply (if clear then .CSRRC else .CSRRS)
          (if csr = .mstatus then raw ||| 0x1800#64 else raw) src) := by
  have hv := csrBitUpdateValue_legal clear csr raw src hm ht he
  cases clear
  · exact hv
  · have hraw : bitUpdate true raw (csrBitMask true csr src) =
        bitUpdate true raw src := by
      have hm' : csr = .mstatus → raw &&& 0x88#64 = raw := by
        intro hc
        simpa using BitVec.and_not_eq_self_of_and_eq_zero raw (~~~(0x88#64)) (hm hc)
      have he' : csr = .mepc → raw &&& ~~~(1#64) = raw := by
        intro hc
        exact clearSingleBit_self raw 0 (he hc)
      have ht' : csr = .mtvec → raw &&& ~~~(2#64) = raw := by
        intro hc
        exact clearSingleBit_self raw 1 (ht hc)
      cases csr <;> simp_all [csrBitMask, bitUpdate, clear_mask_eq]
    simpa only [csrRegisterMask, Bool.true_eq, ↓reduceIte, hraw] using hv

/-- Register CSR set/clear rows agree with Sail on the projected machine hart.
The source read and linked-CSR facts are the usual register-read bundle facts.
For example, CSRRS with rd = rs1 sets bits using the original source value. -/
theorem csrBitUpdateProgram_eq_execute (clear : Bool) (csr : JoltISA.SystemCSR)
    (rs1 rd : regidx) (js : SailJoltState) (src : BitVec 64)
    (hinv : Step.StepInvariant (System.systemProject js))
    (hl : LinkedCSRs js) (hr : rX_bits rs1 js.sail = .ok src js.sail)
    (hm : js.vregs JoltISA.mstatusVReg &&& ~~~(0x88#64) = 0#64)
    (ht : (js.vregs JoltISA.trapHandlerVReg).getLsbD 1 = false)
    (he : (js.vregs JoltISA.mepcVReg).getLsbD 0 = false) :
    System.systemProjectResult
      (JoltISA.execProgram (JoltISA.csrBitUpdateProgram clear csr rs1 rd) js) =
      execute (.CSRReg (csr.address, rs1, rd, if clear then .CSRRC else .CSRRS))
        (System.systemProject js) := by
  have hrp : rX_bits rs1 (System.systemProject js) = .ok src (System.systemProject js) := by
    rw [Projection.systemProject_eq_sail_of_compatible js hl]
    exact hr
  rw [Step.execute_CSRReg_jolt csr.address (isJoltCsr csr) rs1 rd
    (if clear then .CSRRC else .CSRRS) _ hinv (csrLegal_project js hm ht he)
    _ src (csrRead_project csr js) hrp, csrBitUpdateProgram_spec clear csr rs1 rd js src hr]
  by_cases hz : rs1 = zreg
  · subst rs1
    have hs := source_zero zreg js.sail src (by rfl) hr
    subst src
    rw [csrRegisterMask_zero, bitUpdate_zero]
    change EStateM.Result.ok RETIRE_SUCCESS
      (stateAfterWrite (Step.csrSet csr.address (csrValue csr js) (System.systemProject js))
        rd (csrValue csr js)) = _
    rw [csrSet_csrValue_self]
    cases clear <;> simp
  · rw [if_pos (Or.inr hz)]
    have hv := registerBitUpdateValue_legal clear csr (js.vregs csr.vreg) src
      (fun hc => by subst csr; exact hm) (fun hc => by subst csr; exact ht)
      (fun hc => by subst csr; exact he)
    simpa only [csrValue] using congrArg (fun value =>
      EStateM.Result.ok (ε := Error exception) RETIRE_SUCCESS
        (stateAfterWrite (Step.csrSet csr.address value (System.systemProject js))
          rd (csrValue csr js))) hv

end SystemProofs
