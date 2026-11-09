import JoltBytecode.InstructionEquivalence.Instructions.System.ScDword
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.ADDI

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
open LeanRV64D LeanRV64D.Functions

noncomputable section
namespace SystemProofs

/-- Copy one virtual register to another with the emitted zero-offset ADDI.
For example, SC.W spills its comparison flag into v32. -/
theorem reservationCopy_run (dst source : JoltISA.VReg) (js : SailJoltState)
    (hw : WritableVReg dst) :
    (JoltISA.execInstr (JoltISA.Encoded.ADDI (.vreg dst) (.vreg source) 0#12)).run js =
      .ok RETIRE_SUCCESS (stateAfterVRegWrite js dst (js.vregs source)) := by
  have hz : sign_extend (m := 64) 0#12 = 0#64 := rfl
  simpa only [hz, BitVec.add_zero, stateAfterVRegWrite] using JoltISA.addi_run_vreg_vreg dst source 0#12 js hw

/-- A retiring row is a retiring one-row program.
For example, a proved ADDI row can be composed with a lane-window fragment. -/
theorem reservationRow_run (instr : JoltISA.Instr) (js post : SailJoltState)
    (hr : (JoltISA.execInstr instr).run js = .ok RETIRE_SUCCESS post) :
    JoltISA.Program.Run (.instr instr (.done RETIRE_SUCCESS)) js post :=
  (JoltISA.execProgram_instr_run_retire instr _ js post hr).trans rfl

/-- SC.W's floor read and mask rows open the addressed lane.
For example, address 12 opens the upper word of the doubleword at 8. -/
theorem scWordOpen_run (rs1 : regidx) (dword lane : JoltISA.VReg)
    (js : SailJoltState) (addr original : BitVec 64)
    (hr : rX_bits rs1 js.sail = .ok addr js.sail) (ha : addr &&& 3#64 = 0#64)
    (hl : JoltISA.Mmu.load_doubleword (amoWordBase addr) js = .ok (.Ok original) js)
    (hd : WritableVReg dword) (hm : WritableVReg lane) :
    JoltISA.Program.Run (JoltISA.laneWindowOpen .word (.vreg dword) (.vreg lane)
      (.xreg rs1) 0 .amo (ExceptionType.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS)) js
      (stateAfterVRegWrite (stateAfterVRegWrite js dword original) lane (AtomicFamily.amoWordLaneMask addr)) := by
  have hload := AtomicFamily.amo_word_floor_load_aligned_run rs1 dword js addr original hr ha hl hd
  have hmask := JoltISA.virtual_window_mask_w_run_vreg_xreg lane rs1 0#12
    (stateAfterVRegWrite js dword original) addr hr hm
  have h1 := JoltISA.execProgram_instr_run_retire _
    (.instr (JoltISA.Encoded.VirtualWindowMaskW (.vreg lane) (.xreg rs1) 0#12)
      (.done RETIRE_SUCCESS)) js _ hload
  have h2 := JoltISA.execProgram_instr_run_retire _ (.done RETIRE_SUCCESS) _ _ hmask
  exact h1.trans (h2.trans rfl)

/-- Writes to different virtual registers commute.
For example, clearing v32 commutes with writing the discarded status to v40. -/
theorem reservation_vregWrite_commute (js : SailJoltState) (a b : JoltISA.VReg)
    (x y : BitVec 64) (hne : a ≠ b) :
    stateAfterVRegWrite (stateAfterVRegWrite js a x) b y =
      stateAfterVRegWrite (stateAfterVRegWrite js b y) a x := by
  simp only [stateAfterVRegWrite]
  congr 1
  funext r
  by_cases ha : r = a
  · subst r; simp [hne]
  · by_cases hb : r = b <;> simp [ha, hb, Ne.symm hne]

/-- A reservation-register write commutes with Jolt's destination write.
For example, clearing v33 commutes with writing SC's status to x1 or v40. -/
theorem reservation_vregWrite_afterDst (js : SailJoltState) (rd : regidx)
    (value : BitVec 64) (r : JoltISA.VReg) (x : BitVec 64)
    (hne : r ≠ JoltISA.rdZeroRewriteVReg) :
    stateAfterVRegWrite (NativeDispatch.afterDst js rd value) r x =
      NativeDispatch.afterDst (stateAfterVRegWrite js r x) rd value := by
  cases hd : JoltISA.isX0 rd with
  | false => simp only [NativeDispatch.afterDst, hd, Bool.false_eq_true, ite_false, stateAfterVRegWrite]
  | true =>
      simpa only [NativeDispatch.afterDst, hd, ite_true, stateAfterVRegWrite] using
        reservation_vregWrite_commute js JoltISA.rdZeroRewriteVReg r value x (Ne.symm hne)

/-- Clearing SC's reservation commutes with writing its status.
For example, the two generated SC widths may place the status row on either side of the clears. -/
theorem scCleared_afterDst (double : Bool) (js : SailJoltState) (rd : regidx) (value : BitVec 64) :
    scCleared double (NativeDispatch.afterDst js rd value) =
      NativeDispatch.afterDst (scCleared double js) rd value := by
  have h32 : (32#7) ≠ JoltISA.rdZeroRewriteVReg := by decide
  have h33 : (33#7) ≠ JoltISA.rdZeroRewriteVReg := by decide
  cases double <;> simp only [scCleared, Bool.false_eq_true, ite_true, ite_false,
    reservation_vregWrite_afterDst _ _ _ _ _ h32, reservation_vregWrite_afterDst _ _ _ _ _ h33]

/-- SC.W writes its selected word through the containing doubleword, clears
both reservation registers, and returns zero for a successful comparison.
For example, a failed SC.W merges the old signed word back into its original lane. -/
theorem scwProgram_spec (rd rs1 rs2 : regidx) (js : SailJoltState) (addr src : BitVec 64)
    (hr1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hr2 : rX_bits rs2 js.sail = .ok src js.sail)
    (ha : addr &&& 3#64 = 0#64) (hram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
    (hbase : JoltISA.RAM_START_ADDRESS ≤ (amoWordBase addr).toNat)
    (hl : JoltISA.Mmu.effective_address_ok js.jolt_device (amoWordBase addr).toNat false = true)
    (hs : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
    System.systemProjectResult (JoltISA.execProgram (JoltISA.scwProgramAuto rd rs1 rs2) js) =
      .ok RETIRE_SUCCESS (stateAfterWrite (System.systemProject (withReservation
        { js with sail := (state_after_dword_store js.sail (amoWordBase addr)
          (AtomicFamily.amoWordLaneMerged addr (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat)
            (if addr == js.vregs 32#7 then src else AtomicFamily.amoWordLaneOld addr
              (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat)))) }
        0#64 0#64)) rd (if addr == js.vregs 32#7 then 0#64 else 1#64)) := by
  have hsext : sign_extend (m := 64) 0#12 = 0#64 := rfl
  let flag := scScratch rd
  let dword := flag + 1#7
  let lane := flag + 2#7
  let success := addr == js.vregs 32#7
  let bits : BitVec 64 := if success then 1#64 else 0#64
  let original := JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat
  let old := AtomicFamily.amoWordLaneOld addr original
  let choice := if success then src else old
  let checked := stateAfterVRegWrite js flag 0x80000000#64
  let compared := stateAfterVRegWrite checked flag bits
  let flagged := stateAfterVRegWrite compared 32#7 bits
  let extracted := stateAfterVRegWrite
    (stateAfterVRegWrite (stateAfterVRegWrite flagged dword original) lane
      (AtomicFamily.amoWordLaneMask addr)) flag old
  let selected := stateAfterVRegWrite extracted dword choice
  let spilled := stateAfterVRegWrite selected 33#7 choice
  let opened := stateAfterVRegWrite (stateAfterVRegWrite spilled flag original) dword
    (AtomicFamily.amoWordLaneMask addr)
  let stored := { AtomicFamily.amoWordLaneMergeState opened flag dword addr original choice with
    sail := state_after_dword_store js.sail (amoWordBase addr) (AtomicFamily.amoWordLaneMerged addr original choice) }
  let statusState := NativeDispatch.afterDst stored rd (if success then 0#64 else 1#64)
  let final := scCleared false statusState
  obtain ⟨hf, hd, hm, hfd, hfl, hdl⟩ := scScratch_facts rd
  have hcheck := reservationRamCheck_run flag rs1 js addr hf hr1 hram
  have hvres : checked.vregs 32#7 = js.vregs 32#7 := by
    cases hb : JoltISA.isX0 rd <;> simp [checked, flag, scScratch, hb, stateAfterVRegWrite]
  have hcompare : JoltISA.Program.Run (scCompareRows flag 32#7 rs1) checked compared := by
    simpa only [hvres] using scCompareRows_run flag 32#7 rs1 checked addr hf hr1
  have hvflag : compared.vregs flag = bits := by simp [compared, stateAfterVRegWrite]
  have hcopy : (JoltISA.execInstr (JoltISA.Encoded.ADDI (.vreg 32#7) (.vreg flag) 0#12)).run compared =
      .ok RETIRE_SUCCESS flagged := by
    simpa only [hvflag] using reservationCopy_run 32#7 flag compared (by unfold WritableVReg; decide)
  have hload (state : SailJoltState) (hsa : state.sail = js.sail) (hdev : state.jolt_device = js.jolt_device) :
      JoltISA.Mmu.load_doubleword (amoWordBase addr) state = .ok (.Ok original) state := by
    have hlegal : JoltISA.Mmu.effective_address_ok state.jolt_device (amoWordBase addr).toNat false = true := by
      rw [hdev]; exact hl
    have h := JoltISA.Mmu.load_doubleword_ram state (amoWordBase addr)
      (AtomicFamily.amo_word_base_aligned addr) hbase hlegal
    simpa only [hsa] using h
  have hpre : JoltISA.Program.Run (JoltISA.amoPre64ProgramWithScratch rs1 flag dword lane
      (.done RETIRE_SUCCESS)) flagged extracted :=
    AtomicFamily.amo_word_lane_pre_run rs1 flag dword lane flagged addr original hr1 ha
      (hload flagged rfl rfl) hd hm hf hdl
  have hvold : extracted.vregs flag = old := by simp [extracted, stateAfterVRegWrite]
  have hvbits : extracted.vregs 32#7 = bits := by
    cases hb : JoltISA.isX0 rd <;>
      simp [extracted, flagged, compared, checked, stateAfterVRegWrite, flag, dword, lane, scScratch, hb]
  have hchoice : extracted.vregs flag + (src - extracted.vregs flag) * extracted.vregs 32#7 = choice := by
    rw [hvold, hvbits]; exact scSelect_value success old src
  have hneq : dword ≠ 32#7 := by cases hb : JoltISA.isX0 rd <;> simp [dword, flag, scScratch, hb]
  have hselect : JoltISA.Program.Run (scSelectRows dword flag 32#7 rs2) extracted selected := by
    have h := scSelectRows_run dword flag 32#7 rs2 extracted src hd (Ne.symm hfd) hneq hr2
    simpa only [hchoice] using h
  have hvchoice : selected.vregs dword = choice := by simp [selected, stateAfterVRegWrite]
  have hspill : (JoltISA.execInstr (JoltISA.Encoded.ADDI (.vreg 33#7) (.vreg dword) 0#12)).run selected =
      .ok RETIRE_SUCCESS spilled := by
    simpa only [hvchoice] using reservationCopy_run 33#7 dword selected (by unfold WritableVReg; decide)
  have hopen : JoltISA.Program.Run (JoltISA.laneWindowOpen .word (.vreg flag) (.vreg dword)
      (.xreg rs1) 0 .amo (ExceptionType.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS)) spilled opened :=
    scWordOpen_run rs1 flag dword spilled addr original hr1 ha (hload spilled rfl rfl) hf hd
  have hval : (JoltISA.readSrc (.vreg 33#7)).run (stateAfterVRegWrite opened flag
      (original &&& ~~~AtomicFamily.amoWordLaneMask addr)) =
      .ok choice (stateAfterVRegWrite opened flag (original &&& ~~~AtomicFamily.amoWordLaneMask addr)) := by
    cases hb : JoltISA.isX0 rd <;>
      simp [JoltISA.readSrc, readVReg, EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
        get, getThe, MonadStateOf.get, EStateM.get, opened, spilled,
        stateAfterVRegWrite, flag, dword, scScratch, hb]
  have hfd' : flag ≠ dword := hfd
  have hmerge : JoltISA.Program.Run (JoltISA.laneWindowMerge .word (.vreg flag) (.vreg dword)
      (.xreg rs1) 0 (.vreg 33#7) (ExceptionType.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS)) opened stored := by
    apply AtomicFamily.amo_word_lane_merge_run rs1 flag dword (.vreg 33#7) opened addr original choice hr1
      _ _ hval hf hd hfd ha (AtomicFamily.amo_word_base_aligned addr) hbase ⟨hs.below_heap_end, hs.outside_canary⟩
    · simp [opened, stateAfterVRegWrite, hfd']
    · simp [opened, stateAfterVRegWrite]
  have hstatus : (JoltISA.execInstr (JoltISA.Encoded.XORI (JoltISA.sideEffectingRdZeroDst rd)
      (.vreg 32#7) 1#12)).run stored = .ok RETIRE_SUCCESS statusState := by
    have hv : stored.vregs 32#7 = bits := by
      cases hb : JoltISA.isX0 rd <;>
        simp [stored, AtomicFamily.amoWordLaneMergeState, opened, spilled, selected,
          extracted, flagged, compared, checked, stateAfterVRegWrite, flag, dword, lane, scScratch, hb]
    simpa only [hv, bits, statusState, scStatus_value] using scStatus_run rd 32#7 stored
  have hclear := scClearRows_run false statusState
  let copy := JoltISA.Program.instr (JoltISA.Encoded.ADDI (.vreg 32#7) (.vreg flag) 0#12) (.done RETIRE_SUCCESS)
  let spill := JoltISA.Program.instr (JoltISA.Encoded.ADDI (.vreg 33#7) (.vreg dword) 0#12) (.done RETIRE_SUCCESS)
  let status := JoltISA.Program.instr (JoltISA.Encoded.XORI (JoltISA.sideEffectingRdZeroDst rd) (.vreg 32#7) 1#12) (.done RETIRE_SUCCESS)
  let pre := JoltISA.amoPre64ProgramWithScratch rs1 flag dword lane (.done RETIRE_SUCCESS)
  let openRows := JoltISA.laneWindowOpen .word (.vreg flag) (.vreg dword) (.xreg rs1) 0 .amo (ExceptionType.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS)
  let merge := JoltISA.laneWindowMerge .word (.vreg flag) (.vreg dword) (.xreg rs1) 0 (.vreg 33#7) (ExceptionType.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS)
  have hshape : JoltISA.scwProgramAuto rd rs1 rs2 = (reservationRamCheck flag rs1).append
      ((scCompareRows flag 32#7 rs1).append (copy.append (pre.append
        ((scSelectRows dword flag 32#7 rs2).append (spill.append
          (openRows.append (merge.append (status.append (scClearRows false))))))))) := by
    dsimp only [copy, pre, spill, openRows, merge, status, flag, dword, lane, scScratch]
    cases hb : JoltISA.isX0 rd <;>
      simp only [JoltISA.scwProgramAuto, JoltISA.sideEffectingRdZeroDst, hb,
        Bool.false_eq_true, ite_true, ite_false] <;> rfl
  have hrun : JoltISA.Program.Run (JoltISA.scwProgramAuto rd rs1 rs2) js final := by
    rw [hshape]
    exact hcheck.append (hcompare.append ((reservationRow_run _ _ _ hcopy).append
      (hpre.append (hselect.append ((reservationRow_run _ _ _ hspill).append
        (hopen.append (hmerge.append ((reservationRow_run _ _ _ hstatus).append hclear))))))))
  have hproject : System.systemProject final = stateAfterWrite
      (System.systemProject (withReservation { js with sail := (state_after_dword_store js.sail
        (amoWordBase addr) (AtomicFamily.amoWordLaneMerged addr original choice)) } 0#64 0#64)) rd
      (if success then 0#64 else 1#64) := by
    change System.systemProject (scCleared false (NativeDispatch.afterDst stored rd _)) = _
    rw [scCleared_afterDst, NativeDispatch.systemProject_afterDst]
    congr 1
    cases hb : JoltISA.isX0 rd <;>
      simp [scCleared, stored, AtomicFamily.amoWordLaneMergeState, opened, spilled,
        selected, extracted, flagged, compared, checked, stateAfterVRegWrite,
        System.systemProject, withReservation, flag, dword, lane, scScratch, hb,
        JoltISA.reservationWReg, JoltISA.reservationDReg, JoltISA.trapHandlerVReg,
        JoltISA.mscratchVReg, JoltISA.mepcVReg, JoltISA.mcauseVReg, JoltISA.mtvalVReg,
        JoltISA.mstatusVReg, JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount]
  exact (congrArg System.systemProjectResult hrun).trans (congrArg (EStateM.Result.ok RETIRE_SUCCESS) hproject)

end SystemProofs
