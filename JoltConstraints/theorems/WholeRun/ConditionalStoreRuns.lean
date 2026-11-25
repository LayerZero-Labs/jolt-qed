import JoltConstraints.theorems.WholeRun.AtomicStoreRuns

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions JoltISA JoltConstraints JoltConstraints.Soundness

set_option autoImplicit false
noncomputable section

namespace WholeRun

/-- SC's three scratch registers avoid both persistent reservation registers.
For example, the x0 allocation uses v41 through v43, all distinct from v32/v33.
The joint fact serves both widths without repeating allocator cases.
Jolt at `ff6fc6568`: `shared.rs` (`expand_sc_success`). -/
theorem scScratch_reserved (rd : regidx) :
    SystemProofs.scScratch rd ≠ 32#7 ∧ SystemProofs.scScratch rd ≠ 33#7 ∧
    SystemProofs.scScratch rd + 1#7 ≠ 32#7 ∧ SystemProofs.scScratch rd + 1#7 ≠ 33#7 ∧
    SystemProofs.scScratch rd + 2#7 ≠ 32#7 ∧ SystemProofs.scScratch rd + 2#7 ≠ 33#7 := by
  cases zero : isX0 rd <;> simp [SystemProofs.scScratch, zero]

/-- The common SC prefix checks RAM and computes its reservation equality bit.
For example, SC.W compares v32 and SC.D compares v33.
An arbitrary continuation then runs with that bit in the scratch register.
Jolt at `ff6fc6568`: `shared.rs` (`expand_sc_success`). -/
theorem scPrefix_continue (rd rs1 : regidx) (reservation : JoltISA.VReg)
    (pre : SailJoltState) (address : BitVec 64)
    (baseRead : rX_bits rs1 pre.sail = .ok address pre.sail)
    (inRam : RAM_START_ADDRESS ≤ address.toNat)
    (disjoint : SystemProofs.scScratch rd ≠ reservation) (tail : Program) :
    (execProgram ((SystemProofs.reservationRamCheck (SystemProofs.scScratch rd) rs1).append
      ((SystemProofs.scCompareRows (SystemProofs.scScratch rd) reservation rs1).append tail))).run pre =
    (execProgram tail).run (stateAfterVRegWrite
      (stateAfterVRegWrite pre (SystemProofs.scScratch rd) 0x80000000#64)
      (SystemProofs.scScratch rd) (if address == pre.vregs reservation then 1#64 else 0#64)) := by
  let checked := stateAfterVRegWrite pre (SystemProofs.scScratch rd) 0x80000000#64
  have reserved : checked.vregs reservation = pre.vregs reservation := by
    simp only [checked, stateAfterVRegWrite, ite_eq_right (Ne.symm disjoint)]
  have checkRun := SystemProofs.reservationRamCheck_run (SystemProofs.scScratch rd)
    rs1 pre address (SystemProofs.scScratch_facts rd).1 baseRead inRam
  have compareRun := SystemProofs.scCompareRows_run (SystemProofs.scScratch rd)
    reservation rs1 checked address (SystemProofs.scScratch_facts rd).1 baseRead
  rw [reserved] at compareRun
  rw [execProgram_append_of_first_succeeds _ _ _ _ checkRun,
    execProgram_append_of_first_succeeds _ _ _ _ compareRun]

/-- SC.D checks RAM, compares its reservation, loads the old word, selects its
replacement, stores it, then clears the reservation and writes the status.
For example, a failed reservation selects the loaded old word.
Jolt at `ff6fc6568`: `expand/memory/scd.rs` (`expand_scd`). -/
theorem scTemplates (rd rs1 rs2 : regidx) :
    (scdProgramAuto rd rs1 rs2 =
      (SystemProofs.reservationRamCheck (SystemProofs.scScratch rd) rs1).append
        ((SystemProofs.scCompareRows (SystemProofs.scScratch rd) 33#7 rs1).append
          (.instr (.LD .amo (.vreg (SystemProofs.scScratch rd + 1#7)) (.xreg rs1) 0#64)
            ((SystemProofs.scSelectRows (SystemProofs.scScratch rd + 2#7)
              (SystemProofs.scScratch rd + 1#7) (SystemProofs.scScratch rd) rs2).append
              (.instr (.SD (.xreg rs1) (.vreg (SystemProofs.scScratch rd + 2#7)) 0#64)
                ((SystemProofs.scClearRows true).append
                  (.instr (Encoded.XORI (sideEffectingRdZeroDst rd)
                    (.vreg (SystemProofs.scScratch rd)) 1#12) (.done RETIRE_SUCCESS)))))))) ∧
    (scwProgramAuto rd rs1 rs2 =
      (SystemProofs.reservationRamCheck (SystemProofs.scScratch rd) rs1).append
        ((SystemProofs.scCompareRows (SystemProofs.scScratch rd) 32#7 rs1).append
          (.instr (Encoded.ADDI (.vreg 32#7) (.vreg (SystemProofs.scScratch rd)) 0#12)
            ((amoPre64ProgramWithScratch rs1 (SystemProofs.scScratch rd)
              (SystemProofs.scScratch rd + 1#7) (SystemProofs.scScratch rd + 2#7)
              (.done RETIRE_SUCCESS)).append
              ((SystemProofs.scSelectRows (SystemProofs.scScratch rd + 1#7)
                (SystemProofs.scScratch rd) 32#7 rs2).append
                (.instr (Encoded.ADDI (.vreg 33#7) (.vreg (SystemProofs.scScratch rd + 1#7)) 0#12)
                  ((laneWindowOpen .word (.vreg (SystemProofs.scScratch rd))
                    (.vreg (SystemProofs.scScratch rd + 1#7)) (.xreg rs1) 0#64 .amo
                    (.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS)).append
                    (laneWindowMerge .word (.vreg (SystemProofs.scScratch rd))
                      (.vreg (SystemProofs.scScratch rd + 1#7)) (.xreg rs1) 0#64 (.vreg 33#7)
                      (.E_SAMO_Addr_Align ())
                      (.instr (Encoded.XORI (sideEffectingRdZeroDst rd) (.vreg 32#7) 1#12)
                        (SystemProofs.scClearRows false)))))))))) := by
  cases zero : isX0 rd <;>
    simp [scdProgramAuto, scwProgramAuto, SystemProofs.reservationRamCheck,
      SystemProofs.scCompareRows, SystemProofs.scSelectRows, SystemProofs.scClearRows,
      SystemProofs.scScratch, zero, Program.append, RETIRE_SUCCESS,
      sideEffectingRdZeroDst, rdZeroRewriteVReg, inlineTmp, inlineRegisterBase,
      riscvRegisterBase, numReservedVirtualRegisters, riscvRegisterCount,
      amoPre64ProgramWithScratch, laneWindowOpen, laneWindowExtract, laneWindowMerge]
  all_goals exact ⟨rfl, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩, rfl, rfl⟩

/-- The doubleword projection of the shared SC program identities.
For example, its store follows selection and precedes the reservation clears. -/
theorem scdTemplate (rd rs1 rs2 : regidx) :
    scdProgramAuto rd rs1 rs2 =
      (SystemProofs.reservationRamCheck (SystemProofs.scScratch rd) rs1).append
        ((SystemProofs.scCompareRows (SystemProofs.scScratch rd) 33#7 rs1).append
          (.instr (.LD .amo (.vreg (SystemProofs.scScratch rd + 1#7)) (.xreg rs1) 0#64)
            ((SystemProofs.scSelectRows (SystemProofs.scScratch rd + 2#7)
              (SystemProofs.scScratch rd + 1#7) (SystemProofs.scScratch rd) rs2).append
              (.instr (.SD (.xreg rs1) (.vreg (SystemProofs.scScratch rd + 2#7)) 0#64)
                ((SystemProofs.scClearRows true).append
                  (.instr (Encoded.XORI (sideEffectingRdZeroDst rd)
                    (.vreg (SystemProofs.scScratch rd)) 1#12) (.done RETIRE_SUCCESS))))))) := (scTemplates rd rs1 rs2).1

/-- The SC.W window before its final merge opens, selects, spills and reopens.
For example, failure spills the old word and the supplied tail merges it back. -/
private def scwWindowRows (rd rs1 rs2 : regidx) (tail : Program) : Program :=
  (amoPre64ProgramWithScratch rs1 (SystemProofs.scScratch rd)
    (SystemProofs.scScratch rd + 1#7) (SystemProofs.scScratch rd + 2#7)
    (.done RETIRE_SUCCESS)).append
    ((SystemProofs.scSelectRows (SystemProofs.scScratch rd + 1#7)
      (SystemProofs.scScratch rd) 32#7 rs2).append
      (.instr (Encoded.ADDI (.vreg 33#7) (.vreg (SystemProofs.scScratch rd + 1#7)) 0#12)
        ((laneWindowOpen .word (.vreg (SystemProofs.scScratch rd))
          (.vreg (SystemProofs.scScratch rd + 1#7)) (.xreg rs1) 0#64 .amo
          (.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS)).append tail)))

/-- The word projection of the shared SC program identities.
For example, its selected value is spilled to v33 before the containing word is reopened. -/
theorem scwTemplate (rd rs1 rs2 : regidx) :
    scwProgramAuto rd rs1 rs2 =
      (SystemProofs.reservationRamCheck (SystemProofs.scScratch rd) rs1).append
        ((SystemProofs.scCompareRows (SystemProofs.scScratch rd) 32#7 rs1).append
          (.instr (Encoded.ADDI (.vreg 32#7) (.vreg (SystemProofs.scScratch rd)) 0#12)
            (scwWindowRows rd rs1 rs2
              (laneWindowMerge .word (.vreg (SystemProofs.scScratch rd))
                (.vreg (SystemProofs.scScratch rd + 1#7)) (.xreg rs1) 0#64 (.vreg 33#7)
                (.E_SAMO_Addr_Align ())
                (.instr (Encoded.XORI (sideEffectingRdZeroDst rd) (.vreg 32#7) 1#12)
                  (SystemProofs.scClearRows false)))))) := (scTemplates rd rs1 rs2).2

/-- SC.W opens its old lane, selects and spills the replacement, then reopens
its containing word for the final merge.
For example, a zero success bit spills the old signed word to v33.
The continuation equality preserves an arbitrary merge/store tail.
Jolt at `ff6fc6568`: `expand/memory/scw.rs` (`expand_scw`). -/
theorem scwWindow_continue (rd rs1 rs2 : regidx) (pre : SailJoltState)
    (address original source : BitVec 64) (success : Bool)
    (baseRead : rX_bits rs1 pre.sail = .ok address pre.sail)
    (valueRead : rX_bits rs2 pre.sail = .ok source pre.sail)
    (aligned : address &&& 3#64 = 0)
    (inRam : RAM_START_ADDRESS ≤ (amoWordBase address).toNat)
    (legal : Mmu.effective_address_ok pre.jolt_device (amoWordBase address).toNat false = true)
    (readWord : Mmu.load_doubleword (amoWordBase address) pre = .ok (.Ok original) pre)
    (originalEq : original = Mmu.ram_doubleword pre.sail.mem (amoWordBase address).toNat)
    (successEq : pre.vregs 32#7 = if success then 1#64 else 0#64) :
    ∃ opened,
      (∀ tail, (execProgram (scwWindowRows rd rs1 rs2 tail)).run pre =
        (execProgram tail).run opened) ∧
      opened.sail = pre.sail ∧
      opened.vregs (SystemProofs.scScratch rd) = original ∧
      opened.vregs (SystemProofs.scScratch rd + 1#7) = AtomicFamily.amoWordLaneMask address ∧
      (readSrc (.vreg 33#7)).run
        (stateAfterVRegWrite opened (SystemProofs.scScratch rd)
          (original &&& ~~~AtomicFamily.amoWordLaneMask address)) =
        .ok (if success then source else AtomicFamily.amoWordLaneOld address original)
          (stateAfterVRegWrite opened (SystemProofs.scScratch rd)
            (original &&& ~~~AtomicFamily.amoWordLaneMask address)) := by
  let flag := SystemProofs.scScratch rd
  let dword := flag + 1#7
  let lane := flag + 2#7
  let old := AtomicFamily.amoWordLaneOld address original
  let choice := if success then source else old
  let extracted := stateAfterVRegWrite
    (stateAfterVRegWrite (stateAfterVRegWrite pre dword original) lane
      (AtomicFamily.amoWordLaneMask address)) flag old
  let selected := stateAfterVRegWrite extracted dword choice
  let spilled := stateAfterVRegWrite selected 33#7 choice
  let opened := stateAfterVRegWrite (stateAfterVRegWrite spilled flag original) dword
    (AtomicFamily.amoWordLaneMask address)
  obtain ⟨fw, dw, lw, fd, fl, dl⟩ := SystemProofs.scScratch_facts rd
  obtain ⟨f32, f33, d32, d33, l32, l33⟩ := scScratch_reserved rd
  have extractRun := AtomicFamily.amo_word_lane_pre_run rs1 flag dword lane pre
    address original baseRead aligned readWord dw lw fw dl
  have oldEq : extracted.vregs flag = old := by simp only [extracted, stateAfterVRegWrite, ite_true]
  have bitsEq : extracted.vregs 32#7 = if success then 1#64 else 0#64 := by
    simp only [extracted, stateAfterVRegWrite, flag, dword, lane,
      ite_eq_right (Ne.symm f32), ite_eq_right (Ne.symm d32),
      ite_eq_right (Ne.symm l32), successEq]
  have selectRun : Program.Run (SystemProofs.scSelectRows dword flag 32#7 rs2) extracted selected := by
    have calculated := SystemProofs.scSelectRows_run dword flag 32#7 rs2 extracted source dw
      (Ne.symm fd) d32 valueRead
    simpa only [oldEq, bitsEq, SystemProofs.scSelect_value] using calculated
  have spillRun : (execInstr (Encoded.ADDI (.vreg 33#7) (.vreg dword) 0#12)).run selected =
      .ok RETIRE_SUCCESS spilled := by
    have choiceRead : selected.vregs dword = choice := by
      simp only [selected, stateAfterVRegWrite, ite_true]
    simpa only [choiceRead] using SystemProofs.reservationCopy_run 33#7 dword selected
      (by unfold WritableVReg; decide)
  have loadAgain : Mmu.load_doubleword (amoWordBase address) spilled = .ok (.Ok original) spilled := by
    have checked := Mmu.load_doubleword_ram spilled (amoWordBase address)
      (AtomicFamily.amo_word_base_aligned address) inRam legal
    simpa only [spilled, selected, extracted, stateAfterVRegWrite, originalEq] using checked
  have openRun := SystemProofs.scWordOpen_run rs1 flag dword spilled address original
    baseRead aligned loadAgain fw dw
  change flag ≠ dword at fd
  change Program.Run (laneWindowOpen .word (.vreg flag) (.vreg dword) (.xreg rs1) 0#64 .amo
    (.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS)) spilled opened at openRun
  refine ⟨opened, ?_, rfl, ?_, ?_, ?_⟩
  · intro tail
    change (execProgram ((amoPre64ProgramWithScratch rs1 flag dword lane
      (.done RETIRE_SUCCESS)).append
      ((SystemProofs.scSelectRows dword flag 32#7 rs2).append
        (.instr (Encoded.ADDI (.vreg 33#7) (.vreg dword) 0#12)
          ((laneWindowOpen .word (.vreg flag) (.vreg dword) (.xreg rs1) 0#64 .amo
            (.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS)).append tail))))).run pre = _
    rw [execProgram_append_of_first_succeeds _ _ _ _ extractRun,
      execProgram_append_of_first_succeeds _ _ _ _ selectRun,
      execProgram_instr_run_retire _ _ _ _ spillRun,
      execProgram_append_of_first_succeeds _ _ _ _ openRun]
  · change opened.vregs flag = original
    simp only [opened, stateAfterVRegWrite, ite_eq_right fd, ite_true]
  · change opened.vregs dword = AtomicFamily.amoWordLaneMask address
    simp only [opened, stateAfterVRegWrite, ite_true]
  · change (readSrc (.vreg 33#7)).run
      (stateAfterVRegWrite opened flag (original &&& ~~~AtomicFamily.amoWordLaneMask address)) =
      .ok choice (stateAfterVRegWrite opened flag (original &&& ~~~AtomicFamily.amoWordLaneMask address))
    simp only [EStateM.run, readSrc_vreg, readVReg_run, opened, spilled,
      stateAfterVRegWrite, flag, dword, ite_eq_right (Ne.symm f33),
      ite_eq_right (Ne.symm d33), ite_true]

/-- A retiring SC.D checks its actual selected word against byte protection.
A matching reservation selects rs2; a failed reservation rewrites the old word.
For example, a failed SC.D into protected code preserves the code bytes.
Jolt at `ff6fc6568`: `expand/memory/scd.rs` (`expand_scd`) and
`tracer/src/emulator/mmu.rs` (`Mmu::trace_store`).
This execution inversion is a candidate to move into JoltBytecode. -/
theorem scd_ram_guard (rd rs1 rs2 : regidx) (pre post : SailJoltState)
    (baseRead : rX_bits rs1 pre.sail = .ok (sourceValue (.xreg rs1) pre) pre.sail)
    (valueRead : rX_bits rs2 pre.sail = .ok (sourceValue (.xreg rs2) pre) pre.sail)
    (inRam : RAM_START_ADDRESS ≤ (sourceValue (.xreg rs1) pre).toNat)
    (runs : Program.Run (scdProgramAuto rd rs1 rs2) pre post) :
    Assumptions.JoltRamStoreOk (sourceValue (.xreg rs1) pre) pre
      (SystemProofs.scStoreValue true pre (sourceValue (.xreg rs1) pre)
        (sourceValue (.xreg rs2) pre)) 8 := by
  let flag := SystemProofs.scScratch rd
  let address := sourceValue (.xreg rs1) pre
  let success := address == pre.vregs 33#7
  let checked := stateAfterVRegWrite pre flag 0x80000000#64
  let compared := stateAfterVRegWrite checked flag (if success then 1#64 else 0#64)
  obtain ⟨flagWritable, oldWritable, resultWritable, flagOld, flagResult, oldResult⟩ :=
    SystemProofs.scScratch_facts rd
  change flag ≠ flag + 1#7 at flagOld
  rw [scdTemplate] at runs
  unfold Program.Run at runs
  rw [scPrefix_continue rd rs1 33#7 pre address baseRead inRam (scScratch_reserved rd).2.1] at runs
  have guards := dwordRmw_ram_guards_of_loaded (flag + 1#7) oldWritable rs1 rs2
    (.vreg (flag + 2#7))
    (fun rest => (SystemProofs.scSelectRows (flag + 2#7) (flag + 1#7) flag rs2).append rest)
    _ (fun source old => if success then source else old) compared post inRam (by
      intro word loaded loadedEq
      have oldEq : loaded.vregs (flag + 1#7) = word := by
        simp only [loadedEq, stateAfterVRegWrite, ite_true]
      have flagEq : loaded.vregs flag = if success then 1#64 else 0#64 := by
        simp only [loadedEq, compared, checked, stateAfterVRegWrite,
          ite_eq_right flagOld, ite_true]
      have selectRun := SystemProofs.scSelectRows_run (flag + 2#7) (flag + 1#7) flag rs2
        loaded (sourceValue (.xreg rs2) pre) resultWritable (Ne.symm oldResult)
        (Ne.symm flagResult) (by rw [loadedEq]; exact valueRead)
      rw [oldEq, flagEq, SystemProofs.scSelect_value] at selectRun
      refine ⟨_, fun rest => execProgram_append_of_first_succeeds _ _ _ _ selectRun,
        ?_, ?_⟩
      · rw [loadedEq]; rfl
      · simp only [EStateM.run, readSrc_vreg, readVReg_run, stateAfterVRegWrite, ite_true]
        rfl) runs
  exact guards.2.2.transfer rfl rfl rfl

/-- The first row of a word-window program checks alignment and its shared RAM load.
The continuation is arbitrary; for example, SC.W selects a replacement after this opening. -/
private theorem wordOpen_prefix_conditions (rs1 : regidx) (old dword lane : JoltISA.VReg)
    (pre post : SailJoltState) (tail : Program)
    (inRam : RAM_START_ADDRESS ≤ (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
    (runs : Program.Run
      ((amoPre64ProgramWithScratch rs1 old dword lane (.done RETIRE_SUCCESS)).append tail)
      pre post) :
    sourceValue (.xreg rs1) pre &&& 3#64 = 0 ∧
      Assumptions.JoltRamLoadOk (amoWordBase (sourceValue (.xreg rs1) pre)) pre ∧
      Mmu.load_doubleword (amoWordBase (sourceValue (.xreg rs1) pre)) pre =
        .ok (.Ok (Mmu.ram_doubleword pre.sail.mem
          (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)) pre := by
  change (execProgram (.instr (.VirtualLoadW .amo (.vreg dword) (.xreg rs1) 0#64
    (.E_SAMO_Addr_Align ())) _)).run pre = .ok RETIRE_SUCCESS post at runs
  obtain ⟨loaded, loadRun, _⟩ := execProgram_instr_run_retire_inv _ _ pre post runs
  exact wordOpen_conditions rs1 dword pre loaded inRam loadRun

/-- A retiring SC.W window checks its selected replacement and containing-word merge.
The entry state is arbitrary apart from its source reads and saved success bit.
For example, failure selects the old signed word before rewriting its original lane. -/
private theorem scwWindow_ram_guard (rd rs1 rs2 : regidx) (pre post : SailJoltState)
    (success : Bool) (tail : Program)
    (baseRead : rX_bits rs1 pre.sail = .ok (sourceValue (.xreg rs1) pre) pre.sail)
    (valueRead : rX_bits rs2 pre.sail = .ok (sourceValue (.xreg rs2) pre) pre.sail)
    (inRam : RAM_START_ADDRESS ≤ (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
    (successEq : pre.vregs 32#7 = if success then 1#64 else 0#64)
    (runs : Program.Run (scwWindowRows rd rs1 rs2
      (laneWindowMerge .word (.vreg (SystemProofs.scScratch rd))
        (.vreg (SystemProofs.scScratch rd + 1#7)) (.xreg rs1) 0#64 (.vreg 33#7)
        (.E_SAMO_Addr_Align ()) tail)) pre post) :
    Assumptions.JoltRamStoreOk (amoWordBase (sourceValue (.xreg rs1) pre)) pre
      (AtomicFamily.amoWordLaneMerged (sourceValue (.xreg rs1) pre)
        (Mmu.ram_doubleword pre.sail.mem (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
        (if success then sourceValue (.xreg rs2) pre else AtomicFamily.amoWordLaneOld
          (sourceValue (.xreg rs1) pre)
          (Mmu.ram_doubleword pre.sail.mem
            (amoWordBase (sourceValue (.xreg rs1) pre)).toNat))) 8 := by
  let flag := SystemProofs.scScratch rd
  let address := sourceValue (.xreg rs1) pre
  let original := Mmu.ram_doubleword pre.sail.mem (amoWordBase address).toNat
  let choice := if success then sourceValue (.xreg rs2) pre else
    AtomicFamily.amoWordLaneOld address original
  obtain ⟨aligned, loadGuard, readWord⟩ := wordOpen_prefix_conditions rs1 flag (flag + 1#7)
    (flag + 2#7) pre post _ inRam runs
  obtain ⟨opened, continueRun, sailEq, originalEq, maskEq, valueEq⟩ :=
    scwWindow_continue rd rs1 rs2 pre address original (sourceValue (.xreg rs2) pre)
      success baseRead valueRead aligned inRam
      (Mmu.effective_address_ok_of_load inRam loadGuard) readWord rfl successEq
  have setup := JoltIOSetupFrame.execProgram_setup _ pre opened RETIRE_SUCCESS
    ((continueRun (.done RETIRE_SUCCESS)).trans rfl)
  unfold Program.Run at runs
  rw [continueRun] at runs
  obtain ⟨flagWritable, dwordWritable, _, flagDword, _, _⟩ := SystemProofs.scScratch_facts rd
  have guard := wordLaneMerge_ram_guard rs1 flag (flag + 1#7) (.vreg 33#7) opened post
    address original choice (by rw [sailEq]; exact baseRead) originalEq maskEq valueEq
    flagWritable dwordWritable flagDword inRam tail runs
  exact guard.transfer setup.1.symm setup.2.symm
    (congrArg (fun state : SailState => state.mem) sailEq.symm)

/-- The SC.W prefix saves its reservation-match bit in v32.
For example, a failed reservation leaves zero there before opening its old word. -/
private def scwPrefixState (rd : regidx) (pre : SailJoltState) (address : BitVec 64) :
    SailJoltState :=
  let flag := SystemProofs.scScratch rd
  let bits : BitVec 64 := if address == pre.vregs 32#7 then 1#64 else 0#64
  stateAfterVRegWrite
    (stateAfterVRegWrite (stateAfterVRegWrite pre flag 0x80000000#64) flag bits) 32#7 bits

/-- Execute the SC.W RAM and reservation prefix before an arbitrary tail.
For example, the window proof can use its saved match bit without reexecuting the prefix. -/
private theorem scwPrefix_continue (rd rs1 : regidx) (pre : SailJoltState) (address : BitVec 64)
    (baseRead : rX_bits rs1 pre.sail = .ok address pre.sail)
    (inRam : RAM_START_ADDRESS ≤ address.toNat) (tail : Program) :
    (execProgram ((SystemProofs.reservationRamCheck (SystemProofs.scScratch rd) rs1).append
      ((SystemProofs.scCompareRows (SystemProofs.scScratch rd) 32#7 rs1).append
        (.instr (Encoded.ADDI (.vreg 32#7) (.vreg (SystemProofs.scScratch rd)) 0#12) tail)))).run pre =
      (execProgram tail).run (scwPrefixState rd pre address) := by
  let flag := SystemProofs.scScratch rd
  let bits : BitVec 64 := if address == pre.vregs 32#7 then 1#64 else 0#64
  let checked := stateAfterVRegWrite pre flag 0x80000000#64
  let compared := stateAfterVRegWrite checked flag bits
  have flagBits : compared.vregs flag = bits := by
    simp only [compared, stateAfterVRegWrite, ite_true]
  have copyRun : (execInstr (Encoded.ADDI (.vreg 32#7) (.vreg flag) 0#12)).run compared =
      .ok RETIRE_SUCCESS (scwPrefixState rd pre address) := by
    change (execInstr (Encoded.ADDI (.vreg 32#7) (.vreg flag) 0#12)).run compared =
      .ok RETIRE_SUCCESS (stateAfterVRegWrite compared 32#7 bits)
    simpa only [flagBits] using SystemProofs.reservationCopy_run 32#7 flag compared
      (by unfold WritableVReg; decide)
  rw [scPrefix_continue rd rs1 32#7 pre address baseRead inRam (scScratch_reserved rd).1]
  exact execProgram_instr_run_retire _ tail compared _ copyRun

/-- A retiring SC.W checks the actual containing word after conditional selection.
For example, failure merges the old word back and preserves every byte.
The first opening load supplies the address guard reused by the second opening.
Jolt at `ff6fc6568`: `expand/memory/scw.rs` (`expand_scw`).
This execution inversion is a candidate to move into JoltBytecode. -/
theorem scw_ram_guard (rd rs1 rs2 : regidx) (pre post : SailJoltState)
    (baseRead : rX_bits rs1 pre.sail = .ok (sourceValue (.xreg rs1) pre) pre.sail)
    (valueRead : rX_bits rs2 pre.sail = .ok (sourceValue (.xreg rs2) pre) pre.sail)
    (inRam : RAM_START_ADDRESS ≤ (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
    (runs : Program.Run (scwProgramAuto rd rs1 rs2) pre post) :
    Assumptions.JoltRamStoreOk (amoWordBase (sourceValue (.xreg rs1) pre)) pre
      (SystemProofs.scStoreValue false pre (sourceValue (.xreg rs1) pre)
        (sourceValue (.xreg rs2) pre)) 8 := by
  trace "SC.W: entering prefix assembly"
  let address := sourceValue (.xreg rs1) pre
  let success := address == pre.vregs 32#7
  let flagged := scwPrefixState rd pre address
  have lower : RAM_START_ADDRESS ≤ address.toNat := by
    have baseLower : (amoWordBase address).toNat ≤ address.toNat := by
      rw [BitVec.toNat_and]
      exact Nat.and_le_left
    exact inRam.trans baseLower
  trace "SC.W: lower bound obtained"
  rw [scwTemplate] at runs
  trace "SC.W: template rewritten"
  unfold Program.Run at runs
  rw [scwPrefix_continue rd rs1 pre address baseRead lower] at runs
  trace "SC.W: prefix executed"
  have saved : flagged.vregs 32#7 = if success then 1#64 else 0#64 := by
    simp only [flagged, scwPrefixState, stateAfterVRegWrite, ite_true]
    rfl
  have guard := scwWindow_ram_guard rd rs1 rs2 flagged post success _ baseRead valueRead
    inRam saved runs
  trace "SC.W: normalizing final guard by explicit equalities"
  have sources (r : regidx) : sourceValue (.xreg r) flagged = sourceValue (.xreg r) pre := by
    cases r
    simp only [sourceValue, flagged, scwPrefixState, stateAfterVRegWrite]
  have memory : flagged.sail.mem = pre.sail.mem := rfl
  have restored := guard.transfer (t := pre) rfl rfl memory.symm
  simpa only [sources, memory, SystemProofs.scStoreValue, SystemProofs.reservationBase,
    Bool.false_eq_true, ite_false, address, success] using restored

end WholeRun
