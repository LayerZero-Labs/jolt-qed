import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Word
import JoltBytecode.InstructionEquivalence.ProofSupport.ValueLemmas

open LeanRV64D

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions
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

/-- Sign-extending a word and taking its low word back gives the word.
For example, `0xffffffff` extends to `-1` and returns to `0xffffffff`. -/
theorem low_word_signExtend (o : BitVec 32) :
    (Sail.BitVec.extractLsb (o.signExtend 64) 31 0 : BitVec 32) = o := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_signExtend]
  have h32 : i < 32 := hi
  have h64 : i < 64 := by omega
  simp [h32, h64]

/-- The lane merge reads only the low word of its replacement value.
For example, sign-extending the replacement leaves the merged doubleword unchanged. -/
theorem amoWordLaneMerged_congr_low {addr dword v w : BitVec 64}
    (h : (Sail.BitVec.extractLsb v 31 0 : BitVec 32) = Sail.BitVec.extractLsb w 31 0) :
    amoWordLaneMerged addr dword v = amoWordLaneMerged addr dword w := by
  have hmask : v &&& (0xFFFF_FFFF : BitVec 64) = w &&& 0xFFFF_FFFF := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD i) h
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.getLsbD_extractLsb'] at hb
    simp only [BitVec.getLsbD_and]
    by_cases hi32 : i < 32
    · simp_all
    · have hz : (0xFFFF_FFFF : BitVec 64).getLsbD i = false := by
        have h1 : (0xFFFF_FFFF : BitVec 64) = BitVec.ofNat 64 (2 ^ 32 - 1) := rfl
        rw [h1, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
        simp [hi32]
      simp only [hz, Bool.and_false]
  simp only [amoWordLaneMerged, jolt_virtual_shift_data_w_value, hmask]

/-- Sign extension preserves the unsigned ordering of two equally wide words.
For example, 0x80000000 stays larger than 0x7fffffff after both are extended. -/
theorem amo_word_sltu_sign_extend (lhs rhs : BitVec 32) :
    (zopz0zI_u (sign_extend (m := 64) lhs) (sign_extend (m := 64) rhs) : Bool) =
      (zopz0zI_u lhs rhs : Bool) := by
  unfold zopz0zI_u BitVec.toNatInt sign_extend Sail.BitVec.signExtend
  have hl := lhs.isLt
  have hr := rhs.isLt
  simp only [BitVec.toNat_signExtend, BitVec.toNat_setWidth, BitVec.msb_eq_decide,
    Nat.reduceSub, decide_eq_true_eq]
  rw [decide_eq_decide]
  simp only [Int.ofNat_eq_natCast, Int.ofNat_lt]
  split_ifs <;> omega

/-- Sign extension preserves the signed ordering of two words.
For example, `0x80000000` stays below `0x7fffffff` after both are extended. -/
theorem slt_signExtend (a b : BitVec 32) :
    (a.signExtend 64).slt (b.signExtend 64) = a.slt b := by
  have ha := amo_word_toInt_signExtend32_64 a
  have hb := amo_word_toInt_signExtend32_64 b
  simp only [sign_extend, Sail.BitVec.signExtend] at ha hb
  simp only [BitVec.slt, ha, hb]

/-- Sign extension preserves the unsigned ordering of two words.
For example, `0x80000000` stays above `0x7fffffff` after both are extended. -/
theorem ult_signExtend (a b : BitVec 32) :
    (a.signExtend 64).ult (b.signExtend 64) = a.ult b := by
  have h := amo_word_sltu_sign_extend a b
  simp only [sign_extend, Sail.BitVec.signExtend] at h
  rw [ult_eq_zopz0zI_u, ult_eq_zopz0zI_u]
  exact h

/-- The doubleword named in the word-AMO store assumption is the lane merge of any
value whose low word is Sail's word-AMO result.
For example, for AMOADD.W the value may be the 64-bit sum of `rs2` and the
sign-extended old word. -/
theorem amoWordStoreValue_eq_merged (op : amoop) (ea orig rs2 value : BitVec 64)
    (hlow : (Sail.BitVec.extractLsb value 31 0 : BitVec 32) =
      amoWordSailResult op (Sail.BitVec.extractLsb rs2 31 0) (word_of_dword orig (ea.toNat % 8))) :
    JoltISA.amoWordStoreValue op ea orig rs2 = amoWordLaneMerged ea orig value := by
  unfold JoltISA.amoWordStoreValue
  show amoWordLaneMerged ea orig _ = _
  apply amoWordLaneMerged_congr_low
  rw [hlow]
  have hold : (((orig >>> (8 * (ea.toNat % 8))).setWidth 32).signExtend 64 : BitVec 64) =
      (word_of_dword orig (ea.toNat % 8)).signExtend 64 := rfl
  have hrs2 : rs2.setWidth 32 = (Sail.BitVec.extractLsb rs2 31 0 : BitVec 32) := by
    simpa only [Sail.BitVec.extractLsb, BitVec.extractLsb] using
      (BitVec.setWidth_eq_extractLsb' (x := rs2) (w := 32) (by decide))
  generalize word_of_dword orig (ea.toNat % 8) = o at hold ⊢
  cases op <;>
    simp only [hold, hrs2, amoWordSailResult, select_by_mul, apply_ite (fun x : BitVec 64 =>
      (Sail.BitVec.extractLsb x 31 0 : BitVec 32)), amo_word_extract_add_low,
      amo_word_extract_and_low, amo_word_extract_or_low, amo_word_extract_xor_low,
      low_word_signExtend, BitVec.add_comm, BitVec.and_comm, BitVec.or_comm, BitVec.xor_comm,
      slt_signExtend, ult_signExtend, ← slt_eq_zopz0zI_s, ← slt_eq_zopz0zK_s, ← ult_eq_zopz0zI_u,
      ← ult_eq_zopz0zK_u]

/-- The word-AMO bundle accepts the lane merge of any value with the required low word.
For example, sign-extending a negative result does not alter the merged lane. -/
theorem amo_word_bundle_store_lane_ok {op : amoop} {rs2 rs1 rd : regidx}
    {js : SailJoltState} (h : AmoWordProgramEqSailAssumptions op rs2 rs1 rd js)
    (value : BitVec 64)
    (hresult : (Sail.BitVec.extractLsb value 31 0 : BitVec 32) =
      amoWordSailResult op (Sail.BitVec.extractLsb h.rs2_val 31 0)
        (amoWordBundleOld op rs2 rs1 rd js h)) :
    Assumptions.JoltRamStoreOk (amoWordBase h.rs1_val) js
      (amoWordLaneMerged h.rs1_val
        (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase h.rs1_val).toNat) value) 8 := by
  have hoff : (h.rs1_val &&& (7 : BitVec 64)).toNat = h.rs1_val.toNat % 8 := by
    rw [BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]
  have hold : word_of_dword (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase h.rs1_val).toNat)
      (h.rs1_val.toNat % 8) = amoWordBundleOld op rs2 rs1 rd js h := by
    rw [JoltISA.Mmu.ram_doubleword_eq_loaded_dword_at js.sail _
      (Assumptions.DwordPresent.memBytesPresentAt h.dword_present)
      (amo_word_base_no_ovf h.rs1_val), ← hoff]
    rfl
  rw [← amoWordStoreValue_eq_merged op h.rs1_val _ h.rs2_val value (by rw [hresult, hold])]
  exact h.jolt_store.ram_store

/-- The word-AMO bundle accepts the XOR-mask splice of any value with the required low word.
For example, an aligned AMOSWAP.W at offset four replaces only the upper word. -/
theorem amo_word_bundle_store_spliced_ok {op : amoop} {rs2 rs1 rd : regidx}
    {js : SailJoltState} (h : AmoWordProgramEqSailAssumptions op rs2 rs1 rd js)
    (halign : h.rs1_val &&& (3 : BitVec 64) = 0) (value : BitVec 64)
    (hresult : (Sail.BitVec.extractLsb value 31 0 : BitVec 32) =
      amoWordSailResult op (Sail.BitVec.extractLsb h.rs2_val 31 0)
        (amoWordBundleOld op rs2 rs1 rd js h)) :
    Assumptions.JoltRamStoreOk (amoWordBase h.rs1_val) js
      (amoWordSplicedDword h.rs1_val value
        (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase h.rs1_val).toNat)) 8 := by
  rw [← amo_word_lane_merged_eq_spliced _ _ _ halign]
  exact amo_word_bundle_store_lane_ok h value hresult

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
      exact h.atomic_pmp.subaccess (offset := offset) (accessWidth := 4) (by decide) hoff
    have hread : Assumptions.NotReadableMmio addr 4 js.sail := by
      rw [← haddr]
      exact h.not_readable_mmio.subaccess (offset := offset) (accessWidth := 4) (by decide) hoff
    have hwrite : Assumptions.NotWritableMmio addr 4 js.sail := by
      rw [← haddr]
      exact h.not_writable_mmio.subaccess (offset := offset) (accessWidth := 4) (by decide) hoff
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
    (hstore : Assumptions.JoltRamStoreOk (amoWordBase addr) js (amoWordLaneMerged addr (JoltISA.Mmu.ram_doubleword js.sail.mem (amoWordBase addr).toNat) value) 8)
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
  obtain ⟨pre, hpre, hpre_sail, hdword, hlane, hold, hsetup⟩ :=
    amo_word_pre64_aligned_run_for rd (middle.append post) rs1 js addr hrs1 hbytes
      hread (amo_word_base_no_ovf addr) halign hload
  obtain ⟨after, hm⟩ := hmiddle pre hpre_sail hdword hlane
    (hold.trans (amo_word_lane_old_eq addr _ halign))
  have hsail : after.sail = js.sail := hm.sail.trans hpre_sail
  have hsetup' := hsetup.trans (JoltIOSetupFrame.execProgram_setup middle pre after RETIRE_SUCCESS hm.run)
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
    (by
      rw [hm.dword_vreg]
      rw [JoltISA.Mmu.ram_doubleword_eq_loaded_dword_at js.sail (amoWordBase addr)
        hbytes (amo_word_base_no_ovf addr)] at hstore
      simpa only [hsail] using hstore.transfer hsetup'.1 hsetup'.2
        (congrArg (fun s : SailState => s.mem) hsail))
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
      (by simpa using h.not_readable_mmio.subaccess (offset := 0) (accessWidth := 8) (by decide) (by omega))
      (by simpa using h.not_writable_mmio.subaccess (offset := 0) (accessWidth := 8) (by decide) (by omega))
      halign h.jolt_ram_load
      (amo_word_bundle_store_spliced_ok h halign _ (by rw [hold]; exact hvalue _ _))
      (by rw [hold]; exact hvalue _ _)
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
