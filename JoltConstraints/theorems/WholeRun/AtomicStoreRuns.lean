import JoltConstraints.theorems.MemoryRowExecution

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D LeanRV64D.Functions JoltISA JoltConstraints JoltConstraints.Soundness

set_option autoImplicit false
noncomputable section

namespace WholeRun

/-- A retiring read-modify-write prefix supplies the checks for its computed word.
The middle contract states its pure calculation after the old word is loaded.
For example, an ADD middle supplies the sum of rs2 and that old word.
The continuation can include architectural writeback without changing the claim.
Jolt at `ff6fc6568`: `crates/jolt-program/src/expand/memory/shared.rs` (`expand_amo_d`).
The execution inversion is a candidate to move into JoltBytecode. -/
theorem dwordRmw_ram_guards_of_loaded (old : JoltISA.VReg) (writable : WritableVReg old)
    (rs1 rs2 : regidx) (source : Src) (middle : Program → Program) (tail : Program)
    (resultValue : BitVec 64 → BitVec 64 → BitVec 64) (pre post : SailJoltState)
    (inRam : RAM_START_ADDRESS ≤ (sourceValue (.xreg rs1) pre).toNat)
    (calculate : ∀ (word : BitVec 64) (loaded : SailJoltState),
      loaded = stateAfterVRegWrite pre old word →
      ∃ calculated : SailJoltState,
        (∀ rest, (execProgram (middle rest)).run loaded = (execProgram rest).run calculated) ∧
        calculated.sail = pre.sail ∧
        (readSrc source).run calculated = .ok (resultValue (sourceValue (.xreg rs2) pre) word) calculated)
    (runs : Program.Run (.instr (.LD .amo (.vreg old) (.xreg rs1) 0)
      (middle (.instr (.SD (.xreg rs1) source 0) tail))) pre post) :
    (sourceValue (.xreg rs1) pre) &&& 7 = 0 ∧
    Assumptions.JoltRamLoadOk (sourceValue (.xreg rs1) pre) pre ∧
    Assumptions.JoltRamStoreOk (sourceValue (.xreg rs1) pre) pre
      (resultValue (sourceValue (.xreg rs2) pre)
        (Mmu.ram_doubleword pre.sail.mem (sourceValue (.xreg rs1) pre).toNat)) 8 := by
  obtain ⟨loaded, loadRun, restRun⟩ := execProgram_instr_run_retire_inv _ _ pre post runs
  have loadRow : LoadRow (.LD .amo (.vreg old) (.xreg rs1) 0)
      .double (.vreg old) (.xreg rs1) 0 := ⟨.amo, .E_SAMO_Addr_Align (), rfl⟩
  have loadRun' : execInstr ((Instr.LD .amo (.vreg old) (.xreg rs1) 0).withRuntimeAdvice ()) pre =
      .ok RETIRE_SUCCESS loaded := by
    rw [withRuntimeAdvice_eq_of_noAdvice (.LD .amo (.vreg old) (.xreg rs1) 0) () loadRow.metadata.noAdvice]
    exact loadRun
  have aligned := (loadRow.aligned_continuation_of_run () pre loaded loadRun').1
  obtain ⟨readResult, readState, readRun⟩ := loadRow.load_of_run () pre loaded loadRun'
  have loadGuard := ramLoad_guard_of_run _ pre readState readResult
    (by
      change RAM_START_ADDRESS ≤ (sourceValue (.xreg rs1) pre + 0).toNat
      exact (congrArg (fun address : BitVec 64 => RAM_START_ADDRESS ≤ address.toNat)
        (BitVec.add_zero (sourceValue (.xreg rs1) pre))).mpr inRam) readRun
  have loadedEq := loadRow.vreg_post_of_run writable () pre loaded loadRun'
  simp only [MemoryWidth.accessed] at loadedEq loadGuard
  have zeroImmediate : sourceValue (.xreg rs1) pre + (0 : BitVec 64) =
      sourceValue (.xreg rs1) pre := BitVec.add_zero _
  simp only [zeroImmediate] at loadedEq loadGuard
  obtain ⟨calculated, middleRun, sailEq, valueRead⟩ := calculate
    (Mmu.ram_doubleword pre.sail.mem (sourceValue (.xreg rs1) pre).toNat) loaded
    loadedEq
  rw [middleRun] at restRun
  obtain ⟨stored, storeRun, _⟩ := execProgram_instr_run_retire_inv _ _ calculated post restRun
  have storeRow : StoreRow (.SD (.xreg rs1) source 0) .double (.xreg rs1) source 0 :=
    ⟨.E_SAMO_Addr_Align (), rfl⟩
  obtain ⟨storeResult, storeRun'⟩ := storeRow.store_of_run 0 () calculated stored (by
    rw [withRuntimeAdvice_eq_of_noAdvice (.SD (.xreg rs1) source 0) () storeRow.metadata.noAdvice,
      execWithTapeAnswer_of_ne _ 0 storeRow.access.not_tape]
    exact storeRun)
  have baseEq : sourceValue (.xreg rs1) calculated = sourceValue (.xreg rs1) pre := by
    cases rs1 <;> simp only [sourceValue, sailEq]
  have valueEq := (lookup_readSrc_value source calculated calculated _ valueRead).2.symm
  simp only [MemoryWidth.accessed, baseEq, valueEq, zeroImmediate] at storeRun'
  have storeGuard := ramStore_guard_of_run _ _ calculated stored storeResult inRam storeRun'
  have setup := JoltIOSetupFrame.execProgram_setup (middle (.done RETIRE_SUCCESS))
    loaded calculated RETIRE_SUCCESS (middleRun (.done RETIRE_SUCCESS))
  have layoutEq : calculated.jolt_device.memory_layout = pre.jolt_device.memory_layout := by
    simpa only [loadedEq, stateAfterVRegWrite] using setup.1
  have codeEq : calculated.codeRegion = pre.codeRegion := by
    simpa only [loadedEq, stateAfterVRegWrite] using setup.2
  refine ⟨?_, loadGuard, storeGuard.transfer layoutEq.symm codeEq.symm ?_⟩
  · simpa only [MemoryWidth.alignMask, zeroImmediate] using aligned
  · exact congrArg (fun state : SailState => state.mem) sailEq.symm

/-- A pure AMO middle can use only Sail equality and the loaded old word.
For example, an ADD certificate needs no other scratch-register values.
The more general loaded-state inversion also supports SC's reservation flag.
Jolt at `ff6fc6568`: `shared.rs` (`expand_amo_d`). -/
theorem dwordRmw_ram_guards (old : JoltISA.VReg) (writable : WritableVReg old)
    (rs1 rs2 : regidx) (source : Src) (middle : Program → Program) (tail : Program)
    (resultValue : BitVec 64 → BitVec 64 → BitVec 64) (pre post : SailJoltState)
    (inRam : RAM_START_ADDRESS ≤ (sourceValue (.xreg rs1) pre).toNat)
    (calculate : ∀ (word : BitVec 64) (loaded : SailJoltState),
      loaded.sail = pre.sail → loaded.vregs old = word →
      ∃ calculated : SailJoltState,
        (∀ rest, (execProgram (middle rest)).run loaded = (execProgram rest).run calculated) ∧
        calculated.sail = pre.sail ∧
        (readSrc source).run calculated = .ok (resultValue (sourceValue (.xreg rs2) pre) word) calculated)
    (runs : Program.Run (.instr (.LD .amo (.vreg old) (.xreg rs1) 0)
      (middle (.instr (.SD (.xreg rs1) source 0) tail))) pre post) :
    (sourceValue (.xreg rs1) pre) &&& 7 = 0 ∧
    Assumptions.JoltRamLoadOk (sourceValue (.xreg rs1) pre) pre ∧
    Assumptions.JoltRamStoreOk (sourceValue (.xreg rs1) pre) pre
      (resultValue (sourceValue (.xreg rs2) pre)
        (Mmu.ram_doubleword pre.sail.mem (sourceValue (.xreg rs1) pre).toNat)) 8 := by
  apply dwordRmw_ram_guards_of_loaded old writable rs1 rs2 source middle tail resultValue
    pre post inRam ?_ runs
  intro word loaded loadedEq
  exact calculate word loaded (by rw [loadedEq]; rfl)
    (by rw [loadedEq]; simp only [stateAfterVRegWrite, ite_true])

private theorem dwordBinop_registers (rd : regidx) :
    WritableVReg (amoDoubleBinopOldVRegFor rd) ∧
      WritableVReg (amoDoubleBinopNewVRegFor rd) ∧
      amoDoubleBinopOldVRegFor rd ≠ amoDoubleBinopNewVRegFor rd := by
  unfold amoDoubleBinopOldVRegFor amoDoubleBinopNewVRegFor amoVRegFor WritableVReg
  split <;> decide

/-- An ADD, XOR, AND or OR doubleword-AMO template accepts its computed result.
The caller supplies the existing pure middle-row calculation, once for its operator.
For example, AMOADD.D uses the ADD middle certificate and stores `rs2 + old`.
Jolt at `ff6fc6568`: `shared.rs` (`expand_amo_d`). -/
theorem dwordBinop_ram_guards
    (binop : Dst → Src → Src → Instr) (value : BitVec 64 → BitVec 64 → BitVec 64)
    (rs2 rs1 rd : regidx) (pre post : SailJoltState)
    (inRam : RAM_START_ADDRESS ≤ (sourceValue (.xreg rs1) pre).toNat)
    (calculate : ∀ (word : BitVec 64) (loaded : SailJoltState),
      loaded.sail = pre.sail → loaded.vregs (amoDoubleBinopOldVRegFor rd) = word →
      ∃ calculated, AtomicFamily.AmoDwordMiddleStepInto
        (amoDoubleBinopNewVRegFor rd) (amoDoubleBinopOldVRegFor rd)
        (binop (.vreg (amoDoubleBinopNewVRegFor rd)) (.vreg (amoDoubleBinopOldVRegFor rd))
          (.xreg rs2)) word (value (sourceValue (.xreg rs2) pre) word) loaded calculated)
    (runs : Program.Run (amoDoubleBinopProgram binop rs2 rs1 rd) pre post) :
    (sourceValue (.xreg rs1) pre) &&& 7 = 0 ∧
    Assumptions.JoltRamLoadOk (sourceValue (.xreg rs1) pre) pre ∧
    Assumptions.JoltRamStoreOk (sourceValue (.xreg rs1) pre) pre
      (value (sourceValue (.xreg rs2) pre)
        (Mmu.ram_doubleword pre.sail.mem (sourceValue (.xreg rs1) pre).toNat)) 8 := by
  refine dwordRmw_ram_guards (amoDoubleBinopOldVRegFor rd) (dwordBinop_registers rd).1
    rs1 rs2 (.vreg (amoDoubleBinopNewVRegFor rd))
    (fun rest => .instr (binop (.vreg (amoDoubleBinopNewVRegFor rd))
      (.vreg (amoDoubleBinopOldVRegFor rd)) (.xreg rs2)) rest)
    (.instr (Encoded.ADDI (amoDstFor rd) (.vreg (amoDoubleBinopOldVRegFor rd)) 0)
      (.done RETIRE_SUCCESS)) value pre post inRam ?_ runs
  intro word loaded sailEq oldEq
  obtain ⟨calculated, step⟩ := calculate word loaded sailEq oldEq
  refine ⟨calculated, fun rest => execProgram_instr_run_retire _ _ _ _ step.run,
    step.sail.trans sailEq, ?_⟩
  simp only [EStateM.run, readSrc_vreg, readVReg_run, step.result_vreg]

/-- A signed or unsigned min/max doubleword-AMO template accepts its selected word.
The existing middle certificate calculates the selection before the checked store.
For example, AMOMIN.D selects the smaller signed operand and retains the old word
for architectural writeback.
Jolt at `ff6fc6568`: `shared.rs` (`expand_amo_minmax_d`). -/
theorem dwordSelect_ram_guards
    (compare : Dst → Src → Src → Instr) (left right : Src)
    (value : BitVec 64 → BitVec 64 → BitVec 64)
    (rs2 rs1 rd : regidx) (pre post : SailJoltState)
    (inRam : RAM_START_ADDRESS ≤ (sourceValue (.xreg rs1) pre).toNat)
    (calculate : ∀ (word : BitVec 64) (loaded : SailJoltState),
      loaded.sail = pre.sail → loaded.vregs (amoOldVRegFor rd) = word →
      ∃ calculated, AtomicFamily.AmoDwordSelectMiddleStepInto
        (amoNewVRegFor rd) (amoTmpVRegFor rd) (amoOldVRegFor rd)
        compare left right rs2 word (value (sourceValue (.xreg rs2) pre) word)
        loaded calculated)
    (runs : Program.Run (amoDoubleSelectProgram compare left right rs2 rs1 rd) pre post) :
    (sourceValue (.xreg rs1) pre) &&& 7 = 0 ∧
    Assumptions.JoltRamLoadOk (sourceValue (.xreg rs1) pre) pre ∧
    Assumptions.JoltRamStoreOk (sourceValue (.xreg rs1) pre) pre
      (value (sourceValue (.xreg rs2) pre)
        (Mmu.ram_doubleword pre.sail.mem (sourceValue (.xreg rs1) pre).toNat)) 8 := by
  refine dwordRmw_ram_guards (amoOldVRegFor rd) (amoOldVRegFor_writable rd)
    rs1 rs2 (.vreg (amoNewVRegFor rd))
    (AtomicFamily.amoDwordSelectMiddleProgramInto (amoNewVRegFor rd)
      (amoTmpVRegFor rd) (amoOldVRegFor rd) compare left right rs2)
    (.instr (Encoded.ADDI (amoDstFor rd) (.vreg (amoOldVRegFor rd)) 0)
      (.done RETIRE_SUCCESS)) value pre post inRam ?_ runs
  intro word loaded sailEq oldEq
  obtain ⟨calculated, step⟩ := calculate word loaded sailEq oldEq
  exact ⟨calculated, step.run, step.sail.trans sailEq, by
    simp only [EStateM.run, readSrc_vreg, readVReg_run, step.result_vreg]⟩

/-- A doubleword swap template accepts exactly its architectural source value.
For example, AMOSWAP.D to a protected word retires only when that word stays equal.
Its temporary load and final writeback do not add a source-read premise.
Jolt at `ff6fc6568`: `amoswapd.rs` (`AMOSWAPD::expand`). -/
theorem dwordSwap_ram_guards (rs2 rs1 rd : regidx) (pre post : SailJoltState)
    (valueRead : rX_bits rs2 pre.sail = .ok (sourceValue (.xreg rs2) pre) pre.sail)
    (inRam : RAM_START_ADDRESS ≤ (sourceValue (.xreg rs1) pre).toNat)
    (runs : Program.Run (.instr (Encoded.LD .amo (.vreg (amoOldVRegFor rd)) (.xreg rs1) 0)
      (.instr (Encoded.SD (.xreg rs1) (.xreg rs2) 0)
        (.instr (Encoded.ADDI (amoDstFor rd) (.vreg (amoOldVRegFor rd)) 0)
          (.done RETIRE_SUCCESS)))) pre post) :
    (sourceValue (.xreg rs1) pre) &&& 7 = 0 ∧
    Assumptions.JoltRamLoadOk (sourceValue (.xreg rs1) pre) pre ∧
    Assumptions.JoltRamStoreOk (sourceValue (.xreg rs1) pre) pre
      (sourceValue (.xreg rs2) pre) 8 := by
  refine dwordRmw_ram_guards (amoOldVRegFor rd) (amoOldVRegFor_writable rd)
    rs1 rs2 (.xreg rs2) (fun rest => rest)
    (.instr (Encoded.ADDI (amoDstFor rd) (.vreg (amoOldVRegFor rd)) 0)
      (.done RETIRE_SUCCESS)) (fun source _ => source) pre post inRam ?_ runs
  intro word loaded sailEq _
  refine ⟨loaded, fun _ => rfl, sailEq, ?_⟩
  exact readSrc_xreg_run_of_read rs2 loaded _ (by rw [sailEq]; exact valueRead)

/-- The three pure merge rows compute the containing word before its checked store.
For example, replacing the upper word clears that lane and adds its shifted value.
The equation keeps an arbitrary continuation, so AMOs and SC share this reduction.
Jolt at `ff6fc6568`: `shared.rs` (`LaneWindow::merge`). -/
theorem wordLaneMerge_continue (rs1 : regidx) (dword lane : JoltISA.VReg)
    (source : Src) (pre : SailJoltState) (address original value : BitVec 64)
    (baseRead : rX_bits rs1 pre.sail = .ok address pre.sail)
    (originalEq : pre.vregs dword = original)
    (maskEq : pre.vregs lane = AtomicFamily.amoWordLaneMask address)
    (valueRead : readSrc source
      (stateAfterVRegWrite pre dword (original &&& ~~~AtomicFamily.amoWordLaneMask address)) =
      .ok value (stateAfterVRegWrite pre dword
        (original &&& ~~~AtomicFamily.amoWordLaneMask address)))
    (dwordWritable : WritableVReg dword) (laneWritable : WritableVReg lane)
    (distinct : dword ≠ lane) (tail : Program) :
    (execProgram (laneWindowMerge .word (.vreg dword) (.vreg lane) (.xreg rs1) 0
      source (.E_SAMO_Addr_Align ()) tail)).run pre =
    (execProgram (.instr (.VirtualStoreW (.xreg rs1) (.vreg dword) 0
      (.E_SAMO_Addr_Align ())) tail)).run
      (AtomicFamily.amoWordLaneMergeState pre dword lane address original value) := by
  let cleared := stateAfterVRegWrite pre dword
    (original &&& ~~~AtomicFamily.amoWordLaneMask address)
  let shifted := stateAfterVRegWrite cleared lane (jolt_virtual_shift_data_w_value value address)
  have clearRun : (execInstr (.ANDN (.vreg dword) (.vreg dword) (.vreg lane))).run pre =
      .ok RETIRE_SUCCESS cleared := by
    simpa only [originalEq, maskEq, cleared, stateAfterVRegWrite] using
      andn_run_vreg_vreg_vreg dword dword lane pre dwordWritable
  have shiftRun := AtomicFamily.amo_word_shift_data_run lane source rs1 cleared
    value address valueRead baseRead laneWritable
  have addRun : (execInstr (.ADD (.vreg dword) (.vreg dword) (.vreg lane))).run shifted =
      .ok RETIRE_SUCCESS
        (AtomicFamily.amoWordLaneMergeState pre dword lane address original value) := by
    simpa [shifted, cleared, AtomicFamily.amoWordLaneMergeState,
      stateAfterVRegWrite, distinct, AtomicFamily.amoWordLaneMerged] using
      add_run_vreg_vreg_vreg dword dword lane shifted dwordWritable
  change (execProgram (.instr (.ANDN (.vreg dword) (.vreg dword) (.vreg lane))
    (.instr (.VirtualShiftDataW (.vreg lane) source (.xreg rs1) 0)
      (.instr (.ADD (.vreg dword) (.vreg dword) (.vreg lane))
        (.instr (.VirtualStoreW (.xreg rs1) (.vreg dword) 0
          (.E_SAMO_Addr_Align ())) tail))))).run pre = _
  rw [execProgram_instr_run_retire _ _ _ _ clearRun,
    execProgram_instr_run_retire _ _ _ _ shiftRun,
    execProgram_instr_run_retire _ _ _ _ addRun]

/-- A retiring merge checks its computed eight-byte word against protection.
For example, an SC.W merge into code can retire only if its selected lane stays equal.
Only the merge's register calculation is supplied; its store guard follows from execution.
Jolt at `ff6fc6568`: `shared.rs` (`LaneWindow::merge`) and `Mmu::trace_store`. -/
theorem wordLaneMerge_ram_guard (rs1 : regidx) (dword lane : JoltISA.VReg)
    (source : Src) (pre post : SailJoltState) (address original value : BitVec 64)
    (baseRead : rX_bits rs1 pre.sail = .ok address pre.sail)
    (originalEq : pre.vregs dword = original)
    (maskEq : pre.vregs lane = AtomicFamily.amoWordLaneMask address)
    (valueRead : readSrc source
      (stateAfterVRegWrite pre dword (original &&& ~~~AtomicFamily.amoWordLaneMask address)) =
      .ok value (stateAfterVRegWrite pre dword
        (original &&& ~~~AtomicFamily.amoWordLaneMask address)))
    (dwordWritable : WritableVReg dword) (laneWritable : WritableVReg lane)
    (distinct : dword ≠ lane)
    (inRam : RAM_START_ADDRESS ≤ (amoWordBase address).toNat) (tail : Program)
    (runs : Program.Run (laneWindowMerge .word (.vreg dword) (.vreg lane) (.xreg rs1) 0
      source (.E_SAMO_Addr_Align ()) tail) pre post) :
    Assumptions.JoltRamStoreOk (amoWordBase address) pre
      (AtomicFamily.amoWordLaneMerged address original value) 8 := by
  unfold Program.Run at runs
  rw [wordLaneMerge_continue rs1 dword lane source pre address original value
    baseRead originalEq maskEq valueRead dwordWritable laneWritable distinct tail] at runs
  obtain ⟨stored, storeRun, _⟩ := execProgram_instr_run_retire_inv _ _ _ post runs
  have row : StoreRow (.VirtualStoreW (.xreg rs1) (.vreg dword) 0 (.E_SAMO_Addr_Align ()))
      .word (.xreg rs1) (.vreg dword) 0 := ⟨.E_SAMO_Addr_Align (), rfl⟩
  obtain ⟨result, checked⟩ := row.store_of_run 0 () _ stored (by
    rw [withRuntimeAdvice_eq_of_noAdvice
      (.VirtualStoreW (.xreg rs1) (.vreg dword) 0 (.E_SAMO_Addr_Align ())) ()
      row.metadata.noAdvice, execWithTapeAnswer_of_ne _ 0 row.access.not_tape]
    exact storeRun)
  have addressEq : sourceValue (.xreg rs1)
      (AtomicFamily.amoWordLaneMergeState pre dword lane address original value) = address := by
    exact (lookup_readSrc_value (.xreg rs1) pre pre address
      (readSrc_xreg_run_of_read rs1 pre address baseRead)).2.symm
  have valueEq : sourceValue (.vreg dword)
      (AtomicFamily.amoWordLaneMergeState pre dword lane address original value) =
      AtomicFamily.amoWordLaneMerged address original value := by
    simp only [sourceValue, AtomicFamily.amoWordLaneMergeState, stateAfterVRegWrite, ite_true]
  simp only [MemoryWidth.accessed, addressEq, valueEq] at checked
  have zeroImmediate : address + (0 : BitVec 64) = address := BitVec.add_zero _
  simp only [zeroImmediate] at checked
  have guard := ramStore_guard_of_run _ _ _ stored result inRam checked
  exact guard.transfer rfl rfl rfl

/-- A retiring floor word load determines its alignment, guard and shared value.
For example, a word load at address twelve reads the doubleword at eight.
The same inversion supplies AMO opening loads and SC.W's first opening load.
Jolt at `ff6fc6568`: `shared.rs` (`LaneWindow::open`).
This primitive fact is a candidate to move into JoltBytecode. -/
theorem wordOpen_conditions (rs1 : regidx) (dword : JoltISA.VReg)
    (pre post : SailJoltState)
    (inRam : RAM_START_ADDRESS ≤ (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
    (runs : (execInstr (.VirtualLoadW .amo (.vreg dword) (.xreg rs1) 0
      (.E_SAMO_Addr_Align ()))).run pre = .ok RETIRE_SUCCESS post) :
    sourceValue (.xreg rs1) pre &&& 3 = 0 ∧
    Assumptions.JoltRamLoadOk (amoWordBase (sourceValue (.xreg rs1) pre)) pre ∧
    Mmu.load_doubleword (amoWordBase (sourceValue (.xreg rs1) pre)) pre =
      .ok (.Ok (Mmu.ram_doubleword pre.sail.mem
        (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)) pre := by
  have row : LoadRow (.VirtualLoadW .amo (.vreg dword) (.xreg rs1) 0
      (.E_SAMO_Addr_Align ())) .word (.vreg dword) (.xreg rs1) 0 :=
    ⟨.amo, .E_SAMO_Addr_Align (), rfl⟩
  have runtimeRun : execInstr ((Instr.VirtualLoadW .amo (.vreg dword) (.xreg rs1) 0
      (.E_SAMO_Addr_Align ())).withRuntimeAdvice ()) pre = .ok RETIRE_SUCCESS post := runs
  have aligned := (row.aligned_continuation_of_run () pre post runtimeRun).1
  have zeroImmediate : sourceValue (.xreg rs1) pre + (0 : BitVec 64) =
      sourceValue (.xreg rs1) pre := BitVec.add_zero _
  simp only [MemoryWidth.alignMask, zeroImmediate] at aligned
  obtain ⟨readResult, readState, readRun⟩ := row.load_of_run () pre post runtimeRun
  simp only [MemoryWidth.accessed, zeroImmediate] at readRun
  obtain ⟨resultEq, stateEq⟩ := load_doubleword_shape pre readState _ readResult readRun
  have checked := ramLoad_guard_of_run _ pre readState readResult inRam readRun
  exact ⟨aligned, checked, by
    simpa only [resultEq, stateEq, amoWordBase,
      show ~~~(7 : BitVec 64) = (-8 : BitVec 64) from rfl] using readRun⟩

/-- Every retiring word-AMO window checks the word calculated by its middle fragment.
For example, a swap supplies its architectural source without a middle row.
The opening load determines the old shared word and the four-byte alignment.
Jolt at `ff6fc6568`: `shared.rs` (`expand_amo_w`, `LaneWindow`). -/
theorem wordRmw_ram_guard (rd rs1 : regidx) (middle : Program) (source : Src)
    (resultValue : BitVec 32 → BitVec 64) (pre post : SailJoltState)
    (baseRead : rX_bits rs1 pre.sail = .ok (sourceValue (.xreg rs1) pre) pre.sail)
    (inRam : RAM_START_ADDRESS ≤ (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
    (calculate : ∀ (original : BitVec 64) (opened : SailJoltState),
      opened.sail = pre.sail →
      opened.vregs (amoWordDwordVRegFor rd) = original →
      opened.vregs (amoWordLaneVRegFor rd) =
        AtomicFamily.amoWordLaneMask (sourceValue (.xreg rs1) pre) →
      opened.vregs (amoWordOldVRegFor rd) = sign_extend (m := 64)
        (word_of_dword original ((sourceValue (.xreg rs1) pre) &&& 7).toNat) →
      ∃ after, AtomicFamily.AmoWordWindowStep rd middle source
        (word_of_dword original ((sourceValue (.xreg rs1) pre) &&& 7).toNat)
        original (AtomicFamily.amoWordLaneMask (sourceValue (.xreg rs1) pre))
        (resultValue (word_of_dword original ((sourceValue (.xreg rs1) pre) &&& 7).toNat))
        opened after)
    (runs : Program.Run (AtomicFamily.amoWordWindowProgram middle source rs1 rd) pre post) :
    (sourceValue (.xreg rs1) pre) &&& 3 = 0 ∧
    Assumptions.JoltRamStoreOk (amoWordBase (sourceValue (.xreg rs1) pre)) pre
      (AtomicFamily.amoWordLaneMerged (sourceValue (.xreg rs1) pre)
        (Mmu.ram_doubleword pre.sail.mem (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
        (resultValue (word_of_dword
          (Mmu.ram_doubleword pre.sail.mem (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
          ((sourceValue (.xreg rs1) pre) &&& 7).toNat))) 8 := by
  let address := sourceValue (.xreg rs1) pre
  let original := Mmu.ram_doubleword pre.sail.mem (amoWordBase address).toNat
  let old := amoWordOldVRegFor rd
  let dword := amoWordDwordVRegFor rd
  let lane := amoWordLaneVRegFor rd
  have oldWritable : WritableVReg old := AtomicFamily.amo_word_register_writable rd 2
  have dwordWritable : WritableVReg dword := AtomicFamily.amo_word_register_writable rd 0
  have laneWritable : WritableVReg lane := AtomicFamily.amo_word_register_writable rd 1
  have dwordLane : dword ≠ lane := AtomicFamily.amo_word_register_ne rd 0 1 (by decide)
  have oldDword : old ≠ dword := AtomicFamily.amo_word_register_ne rd 2 0 (by decide)
  have oldLane : old ≠ lane := AtomicFamily.amo_word_register_ne rd 2 1 (by decide)
  obtain ⟨loaded, loadRun, _⟩ := execProgram_instr_run_retire_inv _ _ pre post runs
  obtain ⟨aligned, _, readRun⟩ := wordOpen_conditions rs1 dword pre loaded inRam loadRun
  have openRun := AtomicFamily.amo_word_lane_pre_run rs1 old dword lane pre address original
    baseRead aligned readRun dwordWritable laneWritable oldWritable dwordLane
  let opened := stateAfterVRegWrite
    (stateAfterVRegWrite (stateAfterVRegWrite pre dword original) lane
      (AtomicFamily.amoWordLaneMask address)) old (AtomicFamily.amoWordLaneOld address original)
  have restRun : Program.Run (middle.append (amoWordMergeProgram rs1 rd source dword lane old))
      opened post := by
    change (execProgram ((amoPre64ProgramWithScratch rs1 old dword lane
      (.done RETIRE_SUCCESS)).append (middle.append
        (amoWordMergeProgram rs1 rd source dword lane old)))).run pre = _ at runs
    rw [execProgram_append_of_first_succeeds _ _ _ _ openRun] at runs
    exact runs
  obtain ⟨after, step⟩ := calculate original opened rfl
    (by
      change opened.vregs dword = original
      simp only [opened, stateAfterVRegWrite, ite_eq_right (Ne.symm oldDword),
        ite_eq_right dwordLane, ite_true])
    (by
      change opened.vregs lane = AtomicFamily.amoWordLaneMask address
      simp only [opened, stateAfterVRegWrite, ite_eq_right (Ne.symm oldLane), ite_true])
    (by
      change opened.vregs old = sign_extend (m := 64) (word_of_dword original (address &&& 7).toNat)
      simp only [opened, stateAfterVRegWrite, ite_true,
        AtomicFamily.amo_word_lane_old_eq address original aligned])
  unfold Program.Run at restRun
  rw [execProgram_append_of_first_succeeds _ _ _ _ step.run] at restRun
  have guard := wordLaneMerge_ram_guard rs1 dword lane source after post address original _
    (by rw [step.sail]; exact baseRead) step.dword_vreg step.lane_vreg step.value_read
    dwordWritable laneWritable dwordLane inRam _ restRun
  have setup := JoltIOSetupFrame.execProgram_setup middle opened after RETIRE_SUCCESS step.run
  refine ⟨aligned, guard.transfer ?_ ?_ ?_⟩
  · exact setup.1.symm
  · exact setup.2.symm
  · exact congrArg (fun state : SailState => state.mem) step.sail.symm

/-- Matching low words make the executed lane merge equal the bundle's AMO value.
For example, a sign-extended result and its zero-extended low word write the same lane.
Jolt at `ff6fc6568`: `shared.rs` (`expand_amo_w`). -/
theorem wordLaneValue_eq_storeValue (op : amoop) (address original source value : BitVec 64)
    (aligned : address &&& 3 = 0)
    (lowWord : (Sail.BitVec.extractLsb value 31 0 : BitVec 32) =
      AtomicFamily.amoWordSailResult op (Sail.BitVec.extractLsb source 31 0)
        (word_of_dword original (address &&& 7).toNat)) :
    AtomicFamily.amoWordLaneMerged address original value =
      amoWordStoreValue op address original source := by
  rw [AtomicFamily.amo_word_lane_merged_eq_spliced address original value aligned]
  have offset : (address - amoWordBase address).toNat = (address &&& 7).toNat :=
    StoreSplice.offset_toNat_eq_low_three rfl
  have sourceLow : source.setWidth 32 = (Sail.BitVec.extractLsb source 31 0 : BitVec 32) := by
    simpa only [Sail.BitVec.extractLsb, BitVec.extractLsb] using
      (BitVec.setWidth_eq_extractLsb' (x := source) (w := 32) (by decide))
  unfold AtomicFamily.amoWordSplicedDword amoWordStoreValue
  change StoreSplice.wordSplice original (Sail.BitVec.extractLsb value 31 0)
    (8 * (address - amoWordBase address).toNat) =
    StoreSplice.wordSplice original
      (amoValue op (source.setWidth 32)
        ((original >>> ((address - amoWordBase address).toNat * 8)).setWidth 32))
      ((address - amoWordBase address).toNat * 8)
  rw [offset, lowWord, sourceLow]
  simp only [word_of_dword, Nat.mul_comm]
  rfl

/-- The four binops and swap use the same opened-lane and merge templates.
For example, ADD inserts one ADD row between opening and merging the word.
The joint identity handles the x0 scratch allocation once for all five programs.
Jolt at `ff6fc6568`: `shared.rs` (`expand_amo_w`) and `amoswapw.rs`. -/
theorem wordTemplates (rd rs1 rs2 : regidx) :
    amoaddwProgramAuto rd rs1 rs2 = amoWordBinopProgram Instr.ADD rs2 rs1 rd ∧
    amoxorwProgramAuto rd rs1 rs2 = amoWordBinopProgram Instr.XOR rs2 rs1 rd ∧
    amoandwProgramAuto rd rs1 rs2 = amoWordBinopProgram Instr.AND rs2 rs1 rd ∧
    amoorwProgramAuto rd rs1 rs2 = amoWordBinopProgram Instr.OR rs2 rs1 rd ∧
    amoswapwProgramAuto rd rs1 rs2 =
      AtomicFamily.amoWordWindowProgram (.done RETIRE_SUCCESS) (.xreg rs2) rs1 rd := by
  cases zero : isX0 rd <;>
    simp only [amoaddwProgramAuto, amoxorwProgramAuto, amoandwProgramAuto, amoorwProgramAuto,
      amoswapwProgramAuto, amoWordBinopProgram, AtomicFamily.amoWordWindowProgram,
      amoPre64Program, amoPre64ProgramWithScratch, amoWordMergeProgram,
      laneWindowOpen, laneWindowExtract, laneWindowMerge, amoWordOldVRegFor,
      amoWordNewVRegFor, amoWordDwordVRegFor, amoWordLaneVRegFor, amoVRegFor,
      amoDstFor, sideEffectingRdZeroDst, zero, Bool.false_eq_true, ite_false, ite_true] <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- All four min/max word expansions open the same lane and select through
one comparison template.
For example, unsigned max reverses the SLTU operands.
The x0 allocator case is shared across the four identities.
Jolt at `ff6fc6568`: `shared.rs` (`expand_amo_minmax_w`). -/
theorem wordSelectTemplates (rd rs1 rs2 : regidx) :
    amominwProgramAuto rd rs1 rs2 = AtomicFamily.amoWordWindowProgram
      (AtomicFamily.amoWordSelectLaneMiddle Instr.SLT false rs2 rd)
      (.vreg (amoWordNewVRegFor rd)) rs1 rd ∧
    amomaxwProgramAuto rd rs1 rs2 = AtomicFamily.amoWordWindowProgram
      (AtomicFamily.amoWordSelectLaneMiddle Instr.SLT true rs2 rd)
      (.vreg (amoWordNewVRegFor rd)) rs1 rd ∧
    amominuwProgramAuto rd rs1 rs2 = AtomicFamily.amoWordWindowProgram
      (AtomicFamily.amoWordSelectLaneMiddle Instr.SLTU false rs2 rd)
      (.vreg (amoWordNewVRegFor rd)) rs1 rd ∧
    amomaxuwProgramAuto rd rs1 rs2 = AtomicFamily.amoWordWindowProgram
      (AtomicFamily.amoWordSelectLaneMiddle Instr.SLTU true rs2 rd)
      (.vreg (amoWordNewVRegFor rd)) rs1 rd := by
  cases zero : isX0 rd <;>
    simp only [amominwProgramAuto, amomaxwProgramAuto, amominuwProgramAuto,
      amomaxuwProgramAuto, AtomicFamily.amoWordWindowProgram,
      AtomicFamily.amoWordSelectLaneMiddle, AtomicFamily.amoWordSelectLaneTail,
      Program.append, amoPre64Program, amoPre64ProgramWithScratch, amoWordMergeProgram,
      laneWindowOpen, laneWindowExtract, laneWindowMerge, amoWordOldVRegFor,
      amoWordNewVRegFor, amoWordDwordVRegFor, amoWordLaneVRegFor, amoWordTakeVRegFor,
      amoVRegFor, amoDstFor, sideEffectingRdZeroDst, zero, Bool.false_eq_true,
      ite_false, ite_true] <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Extending both operands preserves each word min/max selection.
The two Boolean parameters choose signed versus unsigned order and min versus max.
For example, signed max compares old against new after sign extension.
Jolt at `ff6fc6568`: `shared.rs` (`expand_amo_minmax_w`). -/
theorem wordSelect_result (signed reverse : Bool) (source : BitVec 64) (old : BitVec 32) :
    (if AtomicFamily.amoWordSelectFlag (if signed then zopz0zI_s else zopz0zI_u) reverse
        (sign_extend (m := 64) (Sail.BitVec.extractLsb source 31 0 : BitVec 32))
        (sign_extend (m := 64) old)
      then (Sail.BitVec.extractLsb source 31 0 : BitVec 32) else old) =
    AtomicFamily.amoWordSailResult
      (if signed then (if reverse then .AMOMAX else .AMOMIN)
        else (if reverse then .AMOMAXU else .AMOMINU))
      (Sail.BitVec.extractLsb source 31 0) old := by
  cases signed <;> cases reverse <;>
    simp only [AtomicFamily.amoWordSelectFlag, Bool.false_eq_true, ite_false, ite_true,
      AtomicFamily.amo_word_sltu_sign_extend, AtomicFamily.amoWordSailResult,
      zopz0zI_s, zopz0zK_s, AtomicFamily.amo_word_toInt_signExtend32_64] <;> rfl

/-- A word comparison template checks its selected result before retiring.
For example, signed min stores the smaller low word while keeping the other lane.
The existing comparison certificate supplies selection; the retiring store supplies
protection of code and public input bytes.
Jolt at `ff6fc6568`: `shared.rs` (`expand_amo_minmax_w`). -/
theorem wordSelect_ram_guard (op : amoop)
    (cmp : Dst → Src → Src → Instr) (less : BitVec 64 → BitVec 64 → Bool)
    (reverse : Bool)
    (compareRun : ∀ dst lhs rhs js, WritableVReg dst →
      (execInstr (cmp (.vreg dst) (.vreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS (stateAfterVRegWrite js dst
          (zero_extend (m := 64) (bool_to_bit (less (js.vregs lhs) (js.vregs rhs))))))
    (selectResult : ∀ (source : BitVec 64) (old : BitVec 32),
      (if AtomicFamily.amoWordSelectFlag less reverse
          (sign_extend (m := 64) (Sail.BitVec.extractLsb source 31 0 : BitVec 32))
          (sign_extend (m := 64) old)
        then (Sail.BitVec.extractLsb source 31 0 : BitVec 32) else old) =
      AtomicFamily.amoWordSailResult op (Sail.BitVec.extractLsb source 31 0) old)
    (rs2 rs1 rd : regidx) (pre post : SailJoltState)
    (baseRead : rX_bits rs1 pre.sail = .ok (sourceValue (.xreg rs1) pre) pre.sail)
    (valueRead : rX_bits rs2 pre.sail = .ok (sourceValue (.xreg rs2) pre) pre.sail)
    (inRam : RAM_START_ADDRESS ≤ (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
    (runs : Program.Run (AtomicFamily.amoWordWindowProgram
      (AtomicFamily.amoWordSelectLaneMiddle cmp reverse rs2 rd)
      (.vreg (amoWordNewVRegFor rd)) rs1 rd) pre post) :
    Assumptions.JoltRamStoreOk (amoWordBase (sourceValue (.xreg rs1) pre)) pre
      (amoWordStoreValue op (sourceValue (.xreg rs1) pre)
        (Mmu.ram_doubleword pre.sail.mem (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
        (sourceValue (.xreg rs2) pre)) 8 := by
  let result : BitVec 32 → BitVec 64 := fun old =>
    if AtomicFamily.amoWordSelectFlag less reverse
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (sourceValue (.xreg rs2) pre) 31 0 : BitVec 32))
        (sign_extend (m := 64) old)
      then sourceValue (.xreg rs2) pre else sign_extend (m := 64) old
  obtain ⟨aligned, guard⟩ := wordRmw_ram_guard rd rs1
    (AtomicFamily.amoWordSelectLaneMiddle cmp reverse rs2 rd)
    (.vreg (amoWordNewVRegFor rd)) result pre post baseRead inRam (by
      intro original opened sailEq dwordEq laneEq oldEq
      exact AtomicFamily.amo_word_select_lane_middle_run cmp less compareRun reverse
        rs2 rd opened _ _ _ _ (by rw [sailEq]; exact valueRead) oldEq dwordEq laneEq) runs
  have lowWord : ∀ old,
      (Sail.BitVec.extractLsb (result old) 31 0 : BitVec 32) =
        AtomicFamily.amoWordSailResult op
          (Sail.BitVec.extractLsb (sourceValue (.xreg rs2) pre) 31 0) old := by
    intro old
    dsimp only [result]
    rw [AtomicFamily.amo_word_extract_select_result,
      show (Sail.BitVec.extractLsb (sign_extend (m := 64) old) 31 0 : BitVec 32) = old from
        AtomicFamily.sign_extend_64_setWidth_32 old]
    exact selectResult _ old
  rw [wordLaneValue_eq_storeValue op _ _ _ _ aligned (lowWord _)] at guard
  exact guard

/-- An executed word binop supplies acceptance of its actual computed lane.
For example, XOR preserves the containing word's other four bytes.
The existing row certificate supplies the calculation; execution supplies protection.
Jolt at `ff6fc6568`: `shared.rs` (`expand_amo_w`). -/
theorem wordBinop_ram_guard (op : amoop) (binop : Dst → Src → Src → Instr)
    (value : BitVec 64 → BitVec 64 → BitVec 64) (rs2 rs1 rd : regidx)
    (pre post : SailJoltState)
    (baseRead : rX_bits rs1 pre.sail = .ok (sourceValue (.xreg rs1) pre) pre.sail)
    (inRam : RAM_START_ADDRESS ≤ (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
    (calculate : ∀ (opened : SailJoltState) (old original mask : BitVec 64),
      opened.sail = pre.sail →
      opened.vregs (amoWordOldVRegFor rd) = old →
      opened.vregs (amoWordDwordVRegFor rd) = original →
      opened.vregs (amoWordLaneVRegFor rd) = mask →
      ∃ after, AtomicFamily.AmoWordMiddleStepInto
        (amoWordNewVRegFor rd) (amoWordOldVRegFor rd) (amoWordDwordVRegFor rd)
        (amoWordLaneVRegFor rd)
        (binop (.vreg (amoWordNewVRegFor rd)) (.vreg (amoWordOldVRegFor rd)) (.xreg rs2))
        old original mask (value (sourceValue (.xreg rs2) pre) old) opened after)
    (lowWord : ∀ (source : BitVec 64) (old : BitVec 32),
      (Sail.BitVec.extractLsb (value source (sign_extend (m := 64) old)) 31 0 : BitVec 32) =
        AtomicFamily.amoWordSailResult op (Sail.BitVec.extractLsb source 31 0) old)
    (runs : Program.Run (amoWordBinopProgram binop rs2 rs1 rd) pre post) :
    Assumptions.JoltRamStoreOk (amoWordBase (sourceValue (.xreg rs1) pre)) pre
      (amoWordStoreValue op (sourceValue (.xreg rs1) pre)
        (Mmu.ram_doubleword pre.sail.mem (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
        (sourceValue (.xreg rs2) pre)) 8 := by
  have dwordNew : amoWordDwordVRegFor rd ≠ amoWordNewVRegFor rd :=
    AtomicFamily.amo_word_register_ne rd 0 3 (by decide)
  obtain ⟨aligned, guard⟩ := wordRmw_ram_guard rd rs1
    (.instr (binop (.vreg (amoWordNewVRegFor rd)) (.vreg (amoWordOldVRegFor rd))
      (.xreg rs2)) (.done RETIRE_SUCCESS)) (.vreg (amoWordNewVRegFor rd))
    (fun old => value (sourceValue (.xreg rs2) pre) (sign_extend (m := 64) old))
    pre post baseRead inRam (by
      intro original opened sailEq dwordEq laneEq oldEq
      obtain ⟨after, step⟩ := calculate opened _ original _ sailEq oldEq dwordEq laneEq
      refine ⟨after, (execProgram_instr_run_retire _ _ _ _ step.run).trans rfl,
        step.sail, step.old_vreg, step.dword_vreg, step.shift_vreg, ?_⟩
      simp only [EStateM.run, readSrc_vreg, readVReg_run, stateAfterVRegWrite,
        ite_eq_right (Ne.symm dwordNew), step.result_vreg]) runs
  rw [wordLaneValue_eq_storeValue op _ _ _ _ aligned (lowWord _ _)] at guard
  exact guard

/-- A retiring word swap supplies the guard for its actual architectural source.
For example, swapping the same word into protected code passes the check.
Jolt at `ff6fc6568`: `amoswapw.rs` (`AMOSWAPW::expand`). -/
theorem wordSwap_ram_guard (rs2 rs1 rd : regidx) (pre post : SailJoltState)
    (baseRead : rX_bits rs1 pre.sail = .ok (sourceValue (.xreg rs1) pre) pre.sail)
    (valueRead : rX_bits rs2 pre.sail = .ok (sourceValue (.xreg rs2) pre) pre.sail)
    (inRam : RAM_START_ADDRESS ≤ (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
    (runs : Program.Run (AtomicFamily.amoWordWindowProgram (.done RETIRE_SUCCESS)
      (.xreg rs2) rs1 rd) pre post) :
    Assumptions.JoltRamStoreOk (amoWordBase (sourceValue (.xreg rs1) pre)) pre
      (amoWordStoreValue .AMOSWAP (sourceValue (.xreg rs1) pre)
        (Mmu.ram_doubleword pre.sail.mem (amoWordBase (sourceValue (.xreg rs1) pre)).toNat)
        (sourceValue (.xreg rs2) pre)) 8 := by
  obtain ⟨aligned, guard⟩ := wordRmw_ram_guard rd rs1 (.done RETIRE_SUCCESS) (.xreg rs2)
    (fun _ => sourceValue (.xreg rs2) pre) pre post baseRead inRam (by
      intro original opened sailEq dwordEq laneEq oldEq
      refine ⟨opened, rfl, rfl, oldEq, dwordEq, laneEq, ?_⟩
      apply readSrc_xreg_run_of_read
      change rX_bits rs2 opened.sail = .ok (sourceValue (.xreg rs2) pre) opened.sail
      rw [sailEq]
      exact valueRead) runs
  rw [wordLaneValue_eq_storeValue .AMOSWAP _ _ _ _ aligned rfl] at guard
  exact guard

end WholeRun
