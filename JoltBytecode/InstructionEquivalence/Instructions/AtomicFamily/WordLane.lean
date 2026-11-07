import JoltBytecode.JoltISA.Expansions.Atomics
import JoltBytecode.InstructionEquivalence.ProofSupport.ProgramComposition
import JoltBytecode.InstructionEquivalence.ProofSupport.StateLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Read
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualWindowMask
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.VirtualPext
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.ANDN
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.Add
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Write

open LeanRV64D

/-! Execution of the shared word lane used by atomic expansions.
The row order follows `LaneWindow` in
`crates/jolt-program/src/expand/memory/shared.rs`. -/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions
open virtaddr

namespace AtomicFamily

/-- The mask for the word addressed by `addr`; for example, address 12 selects
the upper 32 bits of its containing doubleword. -/
abbrev amoWordLaneMask (addr : BitVec 64) : BitVec 64 :=
  jolt_virtual_window_mask_w_value addr 0

/-- The sign-extended word extracted from `dword` at `addr`.
For example, extracting `0xffffffff` gives the 64-bit value -1. -/
abbrev amoWordLaneOld (addr dword : BitVec 64) : BitVec 64 :=
  jolt_virtual_pext_signed_value dword (amoWordLaneMask addr)

/-- An aligned floor load performs the containing-doubleword read and writes
its result, as in `floor_access::load` in `tracer/src/instruction/floor_access.rs`.
For example, an effective address of 12 reads the doubleword at 8. -/
theorem amo_word_floor_load_aligned_run
    (rs1 : regidx) (dst : JoltISA.VReg) (js : SailJoltState)
    (addr dword : BitVec 64)
    (hread : rX_bits rs1 js.sail = .ok addr js.sail)
    (halign : addr &&& (3 : BitVec 64) = 0)
    (hload : JoltISA.Mmu.load_doubleword (amoWordBase addr) js = .ok (.Ok dword) js)
    (hw : WritableVReg dst) :
    (JoltISA.execInstr (.VirtualLoadW .amo (.vreg dst) (.xreg rs1) 0
      (ExceptionType.E_SAMO_Addr_Align ()))).run js =
      .ok RETIRE_SUCCESS (stateAfterVRegWrite js dst dword) := by
  unfold JoltISA.execInstr JoltISA.readSrc liftSail
  simp only [hread, bind, EStateM.bind, EStateM.run]
  simp only [add_zero, halign, if_true]
  change (do
    match ← JoltISA.Mmu.load_doubleword (amoWordBase addr) with
    | .Ok value => JoltISA.writeDst (.vreg dst) value *> pure RETIRE_SUCCESS
    | .Err e => pure e) js = _
  simp only [bind, EStateM.bind, hload]
  exact JoltISA.writeVReg_retire_run_of_writable dst dword js hw

/-- A misaligned floor load fails before reading memory or writing its
destination; for example, address 2 raises the AMO alignment exception. -/
theorem amo_word_floor_load_misaligned_run
    (rs1 : regidx) (dst : JoltISA.Dst) (js : SailJoltState) (addr : BitVec 64)
    (hread : rX_bits rs1 js.sail = .ok addr js.sail)
    (halign : addr &&& (3 : BitVec 64) ≠ 0) :
    (JoltISA.execInstr (.VirtualLoadW .amo dst (.xreg rs1) 0
      (ExceptionType.E_SAMO_Addr_Align ()))).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  unfold JoltISA.execInstr JoltISA.readSrc liftSail
  simp only [hread, bind, EStateM.bind, EStateM.run]
  simp only [add_zero, halign, if_false]
  rfl

/-- The shared open/extract fragment loads a doubleword, creates its lane mask,
and extracts the signed old word into three distinct writable temporaries.
For example, a word swap uses this same fragment as a word addition. -/
theorem amo_word_lane_pre_run
    (rs1 : regidx) (old dword lane : JoltISA.VReg)
    (js : SailJoltState) (addr value : BitVec 64)
    (hread : rX_bits rs1 js.sail = .ok addr js.sail)
    (halign : addr &&& (3 : BitVec 64) = 0)
    (hload : JoltISA.Mmu.load_doubleword (amoWordBase addr) js = .ok (.Ok value) js)
    (hdword : WritableVReg dword) (hlane : WritableVReg lane)
    (hold : WritableVReg old) (hdl : dword ≠ lane) :
    JoltISA.Program.Run
      (JoltISA.amoPre64ProgramWithScratch rs1 old dword lane (.done RETIRE_SUCCESS))
      js
      (stateAfterVRegWrite
        (stateAfterVRegWrite (stateAfterVRegWrite js dword value) lane
          (amoWordLaneMask addr)) old (amoWordLaneOld addr value)) := by
  let loaded := stateAfterVRegWrite js dword value
  let masked := stateAfterVRegWrite loaded lane (amoWordLaneMask addr)
  have hld := amo_word_floor_load_aligned_run rs1 dword js addr value
    hread halign hload hdword
  have hmask := JoltISA.virtual_window_mask_w_run_vreg_xreg lane rs1 0
    loaded addr hread hlane
  have hextract := JoltISA.virtual_pext_signed_run_vreg_vreg_vreg old dword lane
    masked hold
  have hopen : JoltISA.Program.Run
      (JoltISA.laneWindowOpen .word (.vreg dword) (.vreg lane) (.xreg rs1) 0
        .amo (ExceptionType.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS))
      js masked := by
    change (JoltISA.execProgram (.instr
      (.VirtualLoadW .amo (.vreg dword) (.xreg rs1) 0 (ExceptionType.E_SAMO_Addr_Align ()))
      (.instr (JoltISA.Encoded.VirtualWindowMaskW (.vreg lane) (.xreg rs1) 0)
        (.done RETIRE_SUCCESS)))).run js = _
    rw [JoltISA.execProgram_instr_run_retire _ _ _ _ hld]
    rw [JoltISA.execProgram_instr_run_retire _ _ _ _ hmask]
    rfl
  have hget : JoltISA.Program.Run
      (JoltISA.laneWindowExtract (.vreg dword) (.vreg lane) (.vreg old) true
        (.done RETIRE_SUCCESS)) masked
      (stateAfterVRegWrite masked old (amoWordLaneOld addr value)) := by
    have hrow : (JoltISA.execInstr
        (.VirtualPextSigned (.vreg old) (.vreg dword) (.vreg lane))).run masked =
        .ok RETIRE_SUCCESS (stateAfterVRegWrite masked old (amoWordLaneOld addr value)) := by
      simpa only [masked, loaded, stateAfterVRegWrite, if_pos rfl, if_neg hdl] using! hextract
    change (JoltISA.execProgram (.instr
      (.VirtualPextSigned (.vreg old) (.vreg dword) (.vreg lane))
      (.done RETIRE_SUCCESS))).run masked = _
    rw [JoltISA.execProgram_instr_run_retire _ _ _ _ hrow]
    rfl
  exact hopen.append hget

/-- The word shifter reads an arbitrary source and an architectural base.
For example, both an AMO result temporary and a swap's source register can
supply the value whose low word is shifted into the addressed lane. -/
theorem amo_word_shift_data_run
    (dst : JoltISA.VReg) (value : JoltISA.Src) (rs1 : regidx)
    (js : SailJoltState) (value64 addr : BitVec 64)
    (hvalue : (JoltISA.readSrc value).run js = .ok value64 js)
    (hread : rX_bits rs1 js.sail = .ok addr js.sail)
    (hw : WritableVReg dst) :
    (JoltISA.execInstr (.VirtualShiftDataW (.vreg dst) value (.xreg rs1) 0)).run js =
      .ok RETIRE_SUCCESS
        (stateAfterVRegWrite js dst (jolt_virtual_shift_data_w_value value64 addr)) := by
  change ((JoltISA.readSrc value >>= fun x => do
    let address ← liftSail (rX_bits rs1)
    JoltISA.writeDst (.vreg dst) (jolt_virtual_shift_data_w_value x (address + 0))
    pure RETIRE_SUCCESS).run js) = _
  simp only [EStateM.run] at hvalue ⊢
  simp only [bind, EStateM.bind, hvalue, liftSail, hread, add_zero]
  exact JoltISA.writeVReg_retire_run_of_writable dst
    (jolt_virtual_shift_data_w_value value64 addr) js hw

/-- The floor store writes the containing doubleword, preserving registers.
For example, an effective address of 12 stores the doubleword at 8. -/
theorem amo_word_floor_store_run
    (rs1 : regidx) (value : JoltISA.VReg) (js : SailJoltState) (addr : BitVec 64)
    (hread : rX_bits rs1 js.sail = .ok addr js.sail)
    (halign : addr &&& (3 : BitVec 64) = 0)
    (hbase : amoWordBase addr &&& (7 : BitVec 64) = 0)
    (hram : JoltISA.RAM_START_ADDRESS ≤ (amoWordBase addr).toNat)
    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
    (JoltISA.execInstr (.VirtualStoreW (.xreg rs1) (.vreg value) 0
      (ExceptionType.E_SAMO_Addr_Align ()))).run js =
      .ok RETIRE_SUCCESS
        { js with sail := state_after_dword_store js.sail (amoWordBase addr) (js.vregs value) } := by
  have hstore := JoltISA.Mmu.store_doubleword_ram js (amoWordBase addr) (js.vregs value)
    hbase hram (JoltISA.Mmu.effective_address_ok_of_store hram hjolt)
  rw [JoltISA.Mmu.write_ram_doubleword_eq] at hstore
  unfold JoltISA.execInstr JoltISA.readSrc liftSail readVReg
  simp only [hread, bind, EStateM.bind, EStateM.run, add_zero, halign, if_true,
    get, getThe, MonadStateOf.get, EStateM.get]
  change (JoltISA.Mmu.store_doubleword (amoWordBase addr) (js.vregs value) >>= fun r =>
    match r with | .Ok _ => pure RETIRE_SUCCESS | .Err e => pure e) js = _
  simp only [bind, EStateM.bind, hstore, pure, EStateM.pure]

/-- The doubleword produced by clearing a word lane and adding its shifted
replacement; for example, replacing the upper word preserves the lower word. -/
abbrev amoWordLaneMerged (addr dword value : BitVec 64) : BitVec 64 :=
  (dword &&& ~~~amoWordLaneMask addr) + jolt_virtual_shift_data_w_value value addr

/-- The three register updates made by `LaneWindow::merge` before its store.
For example, the lane register ends holding the shifted replacement word. -/
def amoWordLaneMergeState (js : SailJoltState) (dword lane : JoltISA.VReg)
    (addr original value : BitVec 64) : SailJoltState :=
  stateAfterVRegWrite
    (stateAfterVRegWrite
      (stateAfterVRegWrite js dword (original &&& ~~~amoWordLaneMask addr))
      lane (jolt_virtual_shift_data_w_value value addr))
    dword (amoWordLaneMerged addr original value)

/-- Execute the four shared merge rows, using the supplied value read after
the doubleword's lane is cleared.
For example, a swap supplies an architectural source, while binops supply a
distinct temporary; both compose the same ANDN, shift, ADD and store proof. -/
theorem amo_word_lane_merge_run
    (rs1 : regidx) (dword lane : JoltISA.VReg) (source : JoltISA.Src)
    (js : SailJoltState) (addr original value : BitVec 64)
    (hread : rX_bits rs1 js.sail = .ok addr js.sail)
    (horiginal : js.vregs dword = original) (hmask : js.vregs lane = amoWordLaneMask addr)
    (hvalue : (JoltISA.readSrc source).run
      (stateAfterVRegWrite js dword (original &&& ~~~amoWordLaneMask addr)) =
      .ok value (stateAfterVRegWrite js dword (original &&& ~~~amoWordLaneMask addr)))
    (hdword : WritableVReg dword) (hlane : WritableVReg lane) (hdl : dword ≠ lane)
    (halign : addr &&& (3 : BitVec 64) = 0)
    (hbase : amoWordBase addr &&& (7 : BitVec 64) = 0)
    (hram : JoltISA.RAM_START_ADDRESS ≤ (amoWordBase addr).toNat)
    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
    JoltISA.Program.Run
      (JoltISA.laneWindowMerge .word (.vreg dword) (.vreg lane) (.xreg rs1) 0 source
        (ExceptionType.E_SAMO_Addr_Align ()) (.done RETIRE_SUCCESS)) js
      { amoWordLaneMergeState js dword lane addr original value with
        sail := state_after_dword_store js.sail (amoWordBase addr)
          (amoWordLaneMerged addr original value) } := by
  let cleared := stateAfterVRegWrite js dword (original &&& ~~~amoWordLaneMask addr)
  let shifted := stateAfterVRegWrite cleared lane (jolt_virtual_shift_data_w_value value addr)
  let merged := amoWordLaneMergeState js dword lane addr original value
  have hclear : (JoltISA.execInstr (.ANDN (.vreg dword) (.vreg dword) (.vreg lane))).run js =
      .ok RETIRE_SUCCESS cleared := by
    simpa only [horiginal, hmask, cleared, stateAfterVRegWrite] using
      JoltISA.andn_run_vreg_vreg_vreg dword dword lane js hdword
  have hshift := amo_word_shift_data_run lane source rs1 cleared value addr hvalue hread hlane
  have hadd : (JoltISA.execInstr (.ADD (.vreg dword) (.vreg dword) (.vreg lane))).run shifted =
      .ok RETIRE_SUCCESS merged := by
    simpa [shifted, cleared, merged, amoWordLaneMergeState, stateAfterVRegWrite, hdl,
      amoWordLaneMerged] using JoltISA.add_run_vreg_vreg_vreg dword dword lane shifted hdword
  have hstore := amo_word_floor_store_run rs1 dword merged addr hread halign hbase hram
    ⟨hjolt.below_heap_end, hjolt.outside_canary⟩
  have hstore' : (JoltISA.execInstr (.VirtualStoreW (.xreg rs1) (.vreg dword) 0
      (ExceptionType.E_SAMO_Addr_Align ()))).run merged =
      .ok RETIRE_SUCCESS { merged with
        sail := state_after_dword_store js.sail (amoWordBase addr)
          (amoWordLaneMerged addr original value) } := by
    simpa [merged, amoWordLaneMergeState, stateAfterVRegWrite] using hstore
  change (JoltISA.execProgram (.instr (.ANDN (.vreg dword) (.vreg dword) (.vreg lane))
    (.instr (.VirtualShiftDataW (.vreg lane) source (.xreg rs1) 0)
      (.instr (.ADD (.vreg dword) (.vreg dword) (.vreg lane))
        (.instr (.VirtualStoreW (.xreg rs1) (.vreg dword) 0
          (ExceptionType.E_SAMO_Addr_Align ())) (.done RETIRE_SUCCESS)))))).run js = _
  rw [JoltISA.execProgram_instr_run_retire _ _ _ _ hclear,
    JoltISA.execProgram_instr_run_retire _ _ _ _ hshift,
    JoltISA.execProgram_instr_run_retire _ _ _ _ hadd,
    JoltISA.execProgram_instr_run_retire _ _ _ _ hstore']
  rfl

/-- Copying an already sign-extended old word has the same row semantics as
extending it again, for any destination, including the rewritten x0 destination.
For example, copying the extracted value -1 leaves all 64 bits set. -/
theorem amo_word_copy_row_eq_sign_extend
    (dst : JoltISA.Dst) (old : JoltISA.VReg) (js : SailJoltState)
    (hext : sign_extend (m := 64)
      (Sail.BitVec.extractLsb (js.vregs old) 31 0 : BitVec 32) = js.vregs old) :
    (JoltISA.execInstr (JoltISA.Encoded.ADDI dst (.vreg old) 0)).run js =
      (JoltISA.execInstr (.VirtualSignExtendWord dst (.vreg old))).run js := by
  unfold JoltISA.Encoded.ADDI JoltISA.execInstr JoltISA.readSrc readVReg
  simp only [bind, EStateM.bind, EStateM.run, get, getThe, MonadStateOf.get,
    EStateM.get, pure, EStateM.pure]
  have hext' : jolt_virtual_sign_extend_word_value (js.vregs old) = js.vregs old := by
    simpa only [jolt_virtual_sign_extend_word_value, sign_extend, Sail.BitVec.signExtend,
      Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      Nat.reduceSub, Nat.reduceAdd, Nat.shiftRight_zero] using! hext
  rw [JoltISA.addWide_low]
  have hzero : sign_extend (m := 64) (0 : BitVec 12) = (0 : BitVec 64) := rfl
  rw [hzero, add_zero, hext']

end AtomicFamily
