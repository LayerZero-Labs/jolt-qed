import JoltBytecode.InstructionEquivalence.Instructions.System.ScRows

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
open LeanRV64D LeanRV64D.Functions

noncomputable section
namespace SystemProofs

/-- The first scratch slot used by an SC expansion.
For example, rd = x0 reserves v40 for the discarded status and starts at v41. -/
def scScratch (rd : regidx) : JoltISA.VReg := if JoltISA.isX0 rd then 41#7 else 40#7

/-- SC's three scratch slots are writable and distinct.
For example, the ordinary destination case uses v40, v41 and v42. -/
theorem scScratch_facts (rd : regidx) :
    WritableVReg (scScratch rd) ∧ WritableVReg (scScratch rd + 1#7) ∧
      WritableVReg (scScratch rd + 2#7) ∧
      scScratch rd ≠ scScratch rd + 1#7 ∧ scScratch rd ≠ scScratch rd + 2#7 ∧
      scScratch rd + 1#7 ≠ scScratch rd + 2#7 := by
  cases hd : JoltISA.isX0 rd <;> simp [scScratch, hd, WritableVReg]

/-- The SC.D program writes either its source or its previously loaded value,
clears the reservation and reports success as zero.
For example, a failed SC.D writes its loaded doubleword back to the same address. -/
theorem scdProgram_spec (rd rs1 rs2 : regidx) (js : SailJoltState) (addr src : BitVec 64)
    (hr1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hr2 : rX_bits rs2 js.sail = .ok src js.sail)
    (ha : addr &&& 7#64 = 0#64) (hram : JoltISA.RAM_START_ADDRESS ≤ addr.toNat)
    (hl : JoltISA.Mmu.effective_address_ok js.jolt_device addr.toNat false = true)
    (hs : JoltISA.Mmu.effective_address_ok js.jolt_device addr.toNat true = true) :
    System.systemProjectResult (JoltISA.execProgram (JoltISA.scdProgramAuto rd rs1 rs2) js) =
      .ok RETIRE_SUCCESS (stateAfterWrite
        (System.systemProject (withReservation
          { js with sail := (state_after_dword_store js.sail addr
            (if addr == js.vregs 33#7 then src else JoltISA.Mmu.ram_doubleword js.sail.mem addr.toNat)) }
          0#64 0#64)) rd (if addr == js.vregs 33#7 then 0#64 else 1#64)) := by
  let flag := scScratch rd
  let old := flag + 1#7
  let result := flag + 2#7
  let success := addr == js.vregs 33#7
  let bits : BitVec 64 := if success then 1#64 else 0#64
  let value := JoltISA.Mmu.ram_doubleword js.sail.mem addr.toNat
  let choice := if success then src else value
  let checked := stateAfterVRegWrite js flag 0x80000000#64
  let compared := stateAfterVRegWrite checked flag bits
  let loaded := stateAfterVRegWrite compared old value
  let selected := stateAfterVRegWrite loaded result choice
  let stored := { selected with sail := state_after_dword_store js.sail addr choice }
  let cleared := scCleared true stored
  let final := NativeDispatch.afterDst cleared rd (if success then 0#64 else 1#64)
  obtain ⟨hf, ho, hout, hfo, hfr, hor⟩ := scScratch_facts rd
  have hcheck := reservationRamCheck_run flag rs1 js addr hf hr1 hram
  have hvres : checked.vregs 33#7 = js.vregs 33#7 := by
    cases hd : JoltISA.isX0 rd <;> simp [checked, stateAfterVRegWrite, flag, scScratch, hd]
  have hcmp : JoltISA.Program.Run (scCompareRows flag 33#7 rs1) checked compared := by
    simpa only [hvres] using scCompareRows_run flag 33#7 rs1 checked addr hf hr1
  have hld : (JoltISA.execInstr (JoltISA.Encoded.LD .amo (.vreg old) (.xreg rs1) 0#12)).run compared =
      .ok RETIRE_SUCCESS loaded := by
    have hzero : addr + sign_extend (m := 64) 0#12 = addr := by
      have hz : sign_extend (m := 64) 0#12 = 0#64 := rfl
      rw [hz, BitVec.add_zero]
    have h := JoltISA.ld_run_vreg_xreg (faultClass := .amo) old rs1 0#12 compared addr hr1
      (by rw [hzero]; exact ha) ho (by rw [hzero]; exact hram) (by rw [hzero]; exact hl)
    simpa only [loaded, value, hzero, stateAfterVRegWrite, compared, checked] using h
  have hvold : loaded.vregs old = value := by simp [loaded, stateAfterVRegWrite]
  have hvflag : loaded.vregs flag = bits := by
    simp [loaded, compared, stateAfterVRegWrite, old, flag, hfo]
  have hchoose : loaded.vregs old + (src - loaded.vregs old) * loaded.vregs flag = choice := by
    rw [hvold, hvflag]
    exact scSelect_value success value src
  have hselect : JoltISA.Program.Run (scSelectRows result old flag rs2) loaded selected := by
    have h := scSelectRows_run result old flag rs2 loaded src hout (Ne.symm hor) (Ne.symm hfr) hr2
    simpa only [hchoose] using h
  have hvalue : selected.vregs result = choice := by simp [selected, stateAfterVRegWrite]
  have hstore : JoltISA.Mmu.store_doubleword addr choice selected = .ok (.Ok true) stored := by
    have h := JoltISA.Mmu.store_doubleword_ram selected addr choice ha hram hs
    rw [JoltISA.Mmu.write_ram_doubleword_eq] at h
    exact h
  have hsd := reservationSd_run rs1 result selected addr choice stored hr1 hvalue ha hstore
  have hclear := scClearRows_run true stored
  have hstatus : (JoltISA.execInstr (JoltISA.Encoded.XORI (JoltISA.sideEffectingRdZeroDst rd)
      (.vreg flag) 1#12)).run cleared = .ok RETIRE_SUCCESS final := by
    have hv : cleared.vregs flag = bits := by
      cases hd : JoltISA.isX0 rd <;>
        simp [cleared, scCleared, stored, selected, loaded, compared, checked,
          stateAfterVRegWrite, flag, old, result, scScratch, hd, bits]
    simpa only [hv, bits, final, scStatus_value] using scStatus_run rd flag cleared
  let read := JoltISA.Program.instr (JoltISA.Encoded.LD .amo (.vreg old) (.xreg rs1) 0#12) (.done RETIRE_SUCCESS)
  let write := JoltISA.Program.instr (JoltISA.Encoded.SD (.xreg rs1) (.vreg result) 0#12) (.done RETIRE_SUCCESS)
  let status := JoltISA.Program.instr (JoltISA.Encoded.XORI (JoltISA.sideEffectingRdZeroDst rd) (.vreg flag) 1#12) (.done RETIRE_SUCCESS)
  have hread : JoltISA.Program.Run read compared loaded :=
    (JoltISA.execProgram_instr_run_retire _ _ compared loaded hld).trans rfl
  have hwrite : JoltISA.Program.Run write selected stored :=
    (JoltISA.execProgram_instr_run_retire _ _ selected stored hsd).trans rfl
  have hlast : JoltISA.Program.Run status cleared final :=
    (JoltISA.execProgram_instr_run_retire _ _ cleared final hstatus).trans rfl
  have hshape : JoltISA.scdProgramAuto rd rs1 rs2 =
      (reservationRamCheck flag rs1).append ((scCompareRows flag 33#7 rs1).append
        (read.append ((scSelectRows result old flag rs2).append
          (write.append ((scClearRows true).append status))))) := by
    cases hd : JoltISA.isX0 rd <;>
      simp [JoltISA.scdProgramAuto, reservationRamCheck, scCompareRows, scSelectRows,
        scClearRows, read, write, status, flag, old, result, scScratch, hd,
        JoltISA.Program.append, RETIRE_SUCCESS, JoltISA.sideEffectingRdZeroDst,
        JoltISA.rdZeroRewriteVReg, JoltISA.inlineTmp, JoltISA.inlineRegisterBase,
        JoltISA.riscvRegisterBase, JoltISA.numReservedVirtualRegisters, JoltISA.riscvRegisterCount]
  have hrun : JoltISA.Program.Run (JoltISA.scdProgramAuto rd rs1 rs2) js final := by
    rw [hshape]
    exact hcheck.append (hcmp.append (hread.append (hselect.append (hwrite.append (hclear.append hlast)))))
  have hproject : System.systemProject final =
      stateAfterWrite (System.systemProject (withReservation
        { js with sail := state_after_dword_store js.sail addr choice } 0#64 0#64)) rd
          (if success then 0#64 else 1#64) := by
    change System.systemProject (NativeDispatch.afterDst cleared rd _) = _
    rw [NativeDispatch.systemProject_afterDst]
    congr 1
    cases hd : JoltISA.isX0 rd <;>
      simp [cleared, scCleared, stored, selected, loaded, compared, checked,
        stateAfterVRegWrite, System.systemProject, withReservation,
        flag, old, result, scScratch, hd, JoltISA.reservationWReg, JoltISA.reservationDReg,
        JoltISA.trapHandlerVReg, JoltISA.mscratchVReg, JoltISA.mepcVReg,
        JoltISA.mcauseVReg, JoltISA.mtvalVReg, JoltISA.mstatusVReg,
        JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount]
  exact (congrArg System.systemProjectResult hrun).trans (congrArg (EStateM.Result.ok RETIRE_SUCCESS) hproject)

end SystemProofs
