import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Word

open Sail PreSail LeanRV64D.Functions
open virtaddr

noncomputable section
namespace AtomicFamily

/-- The old word selected from the containing doubleword in an AMO bundle.
For example, an address ending in 4 selects the upper word. -/
def amoWordBundleOld (op : amoop) (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions op rs2 rs1 rd js) : BitVec 32 :=
  word_of_dword
    (loaded_dword_at js.sail (amoWordBase h.rs1_val)
      (Assumptions.DwordPresent.memBytesPresentAt h.dword_present)
      (amo_word_base_no_ovf h.rs1_val))
    (h.rs1_val &&& (7 : BitVec 64)).toNat

/-- Relate a word-AMO program's successful or alignment-fault run to Sail.
The program supplies its bytecode execution and protected-register frame;
for example, binops and selects share this memory and projection argument. -/
theorem amo_word_program_eq_sail
    (op : amoop) (program : JoltISA.Program) (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions op rs2 rs1 rd js)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (hprotected : JoltISA.ProgramWritesNoProtectedVReg program)
    (haligned : h.rs1_val &&& (3 : BitVec 64) = 0 →
      ∃ jsf, JoltISA.Program.Run program js jsf ∧
        jsf.sail = amoWordFinalSailState rd js.sail h.rs1_val
          (amoWordSailResult op (Sail.BitVec.extractLsb h.rs2_val 31 0)
            (amoWordBundleOld op rs2 rs1 rd js h))
          (amoWordBundleOld op rs2 rs1 rd js h))
    (hmisaligned : h.rs1_val &&& (3 : BitVec 64) ≠ 0 →
      (JoltISA.execProgram program).run js =
        .ok (ExecutionResult.Memory_Exception
          (Virtaddr h.rs1_val, ExceptionType.E_SAMO_Addr_Align ())) js) :
    System.systemProjectResult ((JoltISA.execProgram program).run js) =
      (execute_AMO op false false rs2 rs1 4 rd).run js.sail := by
  let addr := h.rs1_val
  by_cases halign : addr &&& (3 : BitVec 64) = 0
  · let base := amoWordBase addr
    let offset := (addr &&& (7 : BitVec 64)).toNat
    have hbytes_base := Assumptions.DwordPresent.memBytesPresentAt h.dword_present
    have hoff : offset + 4 ≤ 8 := by
      rcases write_word_offset_cases addr halign with hzero | hfour
      · simp only [offset, hzero]; omega
      · simp only [offset, hfour]; omega
    have haddr : base + BitVec.ofNat 64 offset = addr := by
      exact addr_split_aligned_offset addr
    have hbytes : MemBytesPresentAt js.sail addr 4 := by
      rw [← haddr]
      exact memBytesPresentAt_subaccess hbytes_base hoff
        (by have := amo_word_base_no_ovf addr; dsimp only [base]; omega)
    have hpmp : Assumptions.AtomicPmpOk op addr 4 js.sail := by
      rw [← haddr]
      exact h.atomic_pmp.subaccess (offset := offset) (accessWidth := 4) hoff
    have hread : Assumptions.NotReadableMmio addr 4 js.sail := by
      rw [← haddr]
      exact h.not_readable_mmio.subaccess (offset := offset) (accessWidth := 4) hoff
    have hwrite : Assumptions.NotWritableMmio addr 4 js.sail := by
      rw [← haddr]
      exact h.not_writable_mmio.subaccess (offset := offset) (accessWidth := 4) hoff
    have hold : loaded_word_at js.sail addr hbytes
        (amo_word_aligned_no_ovf addr (amo_word_base_no_ovf addr) halign) =
        amoWordBundleOld op rs2 rs1 rd js h := by
      exact loaded_word_in_dword js.sail addr halign hbytes_base
        (amo_word_base_no_ovf addr) hbytes _
    let result := amoWordSailResult op (Sail.BitVec.extractLsb h.rs2_val 31 0)
      (amoWordBundleOld op rs2 rs1 rd js h)
    obtain ⟨jsf, hrun, hfinal⟩ := haligned halign
    have hsail := execute_AMO_word_non_cas_aligned op rs2 rs1 rd js
      h.cur_privilege h.mstatus_mprv addr h.rs2_val result h.rs1_read h.rs2_read
      h.rdReadable.exists_value hbytes hpmp hread hwrite halign hnot_cas
      (by rw [amo_word_trunc_4x8_eq_extract, amo_word_setWidth_4x8_eq_self, hold])
    have hframe := Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
      hprotected hrun
    have hproject := Projection.systemProject_eq_sail_of_memory_update_then_write
      js jsf (state_after_word_store js.sail addr result) rd _ hfinal rfl hframe h.linkedCSRs
    rw [hrun, hsail]
    simp only [System.systemProjectResult, hproject, hfinal, hold]
    rfl
  · rw [hmisaligned halign,
      execute_AMO_word_misaligned op rs2 rs1 rd js addr h.rs2_val
        h.rs1_read h.rs2_read halign]
    simp only [System.systemProjectResult]
    congr 1
    exact Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs

/-- The signed extraction is the sign extension of the selected 32-bit word.
For example, an upper word with its top bit set becomes a negative 64-bit value. -/
theorem amo_word_lane_old_eq (addr dword : BitVec 64)
    (halign : addr &&& (3 : BitVec 64) = 0) :
    amoWordLaneOld addr dword =
      sign_extend (m := 64) (word_of_dword dword (addr &&& (7 : BitVec 64)).toNat) := by
  have hzero : load_effective_address addr 0 = addr := amo_word_zero_offset_addr addr
  simpa only [hzero] using window_mask_w_pext_signed dword addr 0
    (by simpa only [hzero] using halign)

/-- Each of the five word-AMO scratch slots is writable, including when x0
rewriting reserves the first slot; for example, slot three holds a binop result. -/
theorem amo_word_register_writable (rd : regidx) (i : Fin 5) :
    WritableVReg (JoltISA.amoVRegFor rd i.val) := by
  have hi := i.isLt
  unfold JoltISA.amoVRegFor WritableVReg JoltISA.inlineTmp JoltISA.inlineRegisterBase
  split <;> simp only [BitVec.toNat_ofNat, JoltISA.riscvRegisterBase,
    JoltISA.numReservedVirtualRegisters, JoltISA.riscvRegisterCount] <;> omega

/-- Distinct word-AMO scratch slots name distinct registers under either
allocator offset; for example, the old-word and result slots never alias. -/
theorem amo_word_register_ne (rd : regidx) (i j : Fin 5) (h : i ≠ j) :
    JoltISA.amoVRegFor rd i.val ≠ JoltISA.amoVRegFor rd j.val := by
  have hi := i.isLt
  have hj := j.isLt
  have hij : i.val ≠ j.val := fun heq => h (Fin.ext heq)
  unfold JoltISA.amoVRegFor JoltISA.inlineTmp JoltISA.inlineRegisterBase
  split <;> intro heq <;>
    have heq' := congrArg BitVec.toNat heq <;>
    simp only [BitVec.toNat_ofNat] at heq' <;> omega

/-- A word lane opened around a caller's middle fragment, then merged from
`source`; for example, swap uses an empty middle and an architectural source. -/
def amoWordWindowProgram (middle : JoltISA.Program) (source : JoltISA.Src)
    (rs1 rd : regidx) : JoltISA.Program :=
  JoltISA.amoPre64Program rs1 (JoltISA.amoWordOldVRegFor rd)
    (JoltISA.amoWordDwordVRegFor rd) (JoltISA.amoWordLaneVRegFor rd)
    (middle.append (JoltISA.amoWordMergeProgram rs1 rd source
      (JoltISA.amoWordDwordVRegFor rd) (JoltISA.amoWordLaneVRegFor rd)
      (JoltISA.amoWordOldVRegFor rd)))

/-- A middle fragment preserves the opened word lane and supplies its replacement.
The source is read after the merge clears the old lane, so this contract also
covers a swap whose value comes directly from an architectural register. -/
structure AmoWordWindowStep (rd : regidx) (middle : JoltISA.Program) (source : JoltISA.Src)
    (old : BitVec 32) (dword lane value : BitVec 64) (before after : SailJoltState) : Prop where
  run : JoltISA.Program.Run middle before after
  sail : after.sail = before.sail
  old_vreg : after.vregs (JoltISA.amoWordOldVRegFor rd) = sign_extend (m := 64) old
  dword_vreg : after.vregs (JoltISA.amoWordDwordVRegFor rd) = dword
  lane_vreg : after.vregs (JoltISA.amoWordLaneVRegFor rd) = lane
  value_read : (JoltISA.readSrc source).run
      (stateAfterVRegWrite after (JoltISA.amoWordDwordVRegFor rd) (dword &&& ~~~lane)) =
    .ok value (stateAfterVRegWrite after (JoltISA.amoWordDwordVRegFor rd) (dword &&& ~~~lane))

/-- Compose an opened lane, a middle fragment and the shared merge/copy proof.
For example, the same argument serves both a swap and a five-row min/max middle. -/
theorem amo_word_window_program_aligned_run
    (middle : JoltISA.Program) (source : JoltISA.Src) (rs1 rd : regidx)
    (js : SailJoltState) (addr value : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hbytes : MemBytesPresentAt js.sail (amoWordBase addr) 8)
    (hread : Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail)
    (hwrite : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
    (halign : addr &&& (3 : BitVec 64) = 0)
    (hload : Assumptions.JoltRamLoadOk (amoWordBase addr) js)
    (hstore : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
    (hmiddle : ∀ pre,
      pre.sail = js.sail →
      pre.vregs (JoltISA.amoWordDwordVRegFor rd) =
        loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr) →
      pre.vregs (JoltISA.amoWordLaneVRegFor rd) = amoWordLaneMask addr →
      pre.vregs (JoltISA.amoWordOldVRegFor rd) = sign_extend (m := 64)
        (word_of_dword
          (loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr))
          (addr &&& (7 : BitVec 64)).toNat) →
      ∃ after, AmoWordWindowStep rd middle source
        (word_of_dword
          (loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr))
          (addr &&& (7 : BitVec 64)).toNat)
        (loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr))
        (amoWordLaneMask addr) value pre after) :
    ∃ jsf, JoltISA.Program.Run (amoWordWindowProgram middle source rs1 rd) js jsf ∧
      jsf.sail = amoWordFinalSailState rd js.sail addr (Sail.BitVec.extractLsb value 31 0)
        (word_of_dword
          (loaded_dword_at js.sail (amoWordBase addr) hbytes (amo_word_base_no_ovf addr))
          (addr &&& (7 : BitVec 64)).toNat) := by
  let old := JoltISA.amoWordOldVRegFor rd
  let dword := JoltISA.amoWordDwordVRegFor rd
  let lane := JoltISA.amoWordLaneVRegFor rd
  let post := JoltISA.amoWordMergeProgram rs1 rd source dword lane old
  obtain ⟨pre, hpre, hpre_sail, hdword, hlane, hold, hlayout⟩ :=
    amo_word_pre64_aligned_run_for rd (middle.append post) rs1 js addr hrs1 hbytes
      hread (amo_word_base_no_ovf addr) halign hload
  obtain ⟨after, hm⟩ := hmiddle pre hpre_sail hdword hlane
    (hold.trans (amo_word_lane_old_eq addr _ halign))
  have hsail : after.sail = js.sail := hm.sail.trans hpre_sail
  have hlayout' := (JoltIOSetupFrame.execProgram_rule middle pre after RETIRE_SUCCESS hm.run).1.trans hlayout
  have hregs : WritableVReg dword ∧ WritableVReg lane ∧
      dword ≠ lane ∧ old ≠ dword ∧ old ≠ lane := by
    dsimp [old, dword, lane, JoltISA.amoWordOldVRegFor, JoltISA.amoWordDwordVRegFor,
      JoltISA.amoWordLaneVRegFor, JoltISA.amoVRegFor, WritableVReg]
    split <;> decide
  obtain ⟨jsf, hmerge, hfinal⟩ := amo_word_merge_program_aligned_run rs1 rd dword lane old
    source after addr value _ (by rw [hsail]; exact hrs1) (by rw [hsail]; exact hbytes)
    (by simpa only [hsail] using hm.dword_vreg) hm.lane_vreg
    (by simpa only [dword, hm.dword_vreg] using hm.value_read)
    hm.old_vreg hregs.1 hregs.2.1 hregs.2.2.1 hregs.2.2.2.1 hregs.2.2.2.2 halign
    (by rw [hsail]; exact hwrite)
    ⟨by rw [hlayout']; exact hstore.below_heap_end,
     by rw [hlayout']; exact hstore.outside_canary⟩
  refine ⟨jsf, ?_, ?_⟩
  · change (JoltISA.execProgram _).run js = _
    unfold amoWordWindowProgram
    rw [hpre]
    exact hm.run.append hmerge
  · simpa only [hsail] using hfinal

/-- The four word binops share the same prelude, one caller-proved middle row,
and merge. For example, ADD and XOR differ only in their row and low-word rule. -/
theorem amo_word_binop_eq_sail
    (op : amoop) (binop : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (value : BitVec 64 → BitVec 64 → BitVec 64)
    (hrow : ∀ (new old dword lane : JoltISA.VReg) (rs2 : regidx)
      (js : SailJoltState) (rs2Val oldVal dwordVal laneVal : BitVec 64),
      rX_bits rs2 js.sail = .ok rs2Val js.sail →
      js.vregs old = oldVal → js.vregs dword = dwordVal → js.vregs lane = laneVal →
      WritableVReg new → old ≠ new → dword ≠ new → lane ≠ new →
      ∃ after, AmoWordMiddleStepInto new old dword lane
        (binop (.vreg new) (.vreg old) (.xreg rs2))
        oldVal dwordVal laneVal (value rs2Val oldVal) js after)
    (hvalue : ∀ (new : BitVec 64) (old : BitVec 32),
      (Sail.BitVec.extractLsb (value new (sign_extend (m := 64) old)) 31 0 : BitVec 32) =
        amoWordSailResult op (Sail.BitVec.extractLsb new 31 0) old)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions op rs2 rs1 rd js)
    (hprotected : JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amoWordBinopProgram binop rs2 rs1 rd)) :
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.amoWordBinopProgram binop rs2 rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 4 rd).run js.sail := by
  apply amo_word_program_eq_sail op _ rs2 rs1 rd js h hnot_cas hprotected
  · intro halign
    have hbytes := Assumptions.DwordPresent.memBytesPresentAt h.dword_present
    let dword := loaded_dword_at js.sail (amoWordBase h.rs1_val) hbytes
      (amo_word_base_no_ovf h.rs1_val)
    let old := amoWordLaneOld h.rs1_val dword
    have hold : old = sign_extend (m := 64) (amoWordBundleOld op rs2 rs1 rd js h) :=
      amo_word_lane_old_eq h.rs1_val dword halign
    apply amo_word_binop_program_concrete_aligned binop rs2 rs1 rd js h.rs1_val
      (value h.rs2_val old) _ h.rs1_read hbytes
      (by simpa using h.not_readable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega))
      (by simpa using h.not_writable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega))
      halign h.jolt_ram_load h.jolt_ram_store (by rw [hold]; exact hvalue _ _)
    intro pre hsail hdword hlane hold
    apply hrow _ _ _ _ rs2 pre h.rs2_val old dword (amoWordLaneMask h.rs1_val)
      (by rw [hsail]; exact h.rs2_read) hold hdword hlane
    all_goals
      simp only [JoltISA.amoWordNewVRegFor, JoltISA.amoWordOldVRegFor,
        JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor,
        JoltISA.amoVRegFor, WritableVReg]
      split <;> decide
  · intro halign
    exact amo_word_pre64_with_scratch_misaligned_run rs1 _ _ _ _ js h.rs1_val h.rs1_read halign

end AtomicFamily
end
