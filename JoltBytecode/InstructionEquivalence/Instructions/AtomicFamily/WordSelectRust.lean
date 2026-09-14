import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Word



set_option linter.unusedVariables false



open Sail PreSail LeanRV64D.Functions

open virtaddr MemoryAccessType mem_payload



set_option autoImplicit true



noncomputable section



namespace AtomicFamily



/-!

# Rust-shaped word select AMO helpers

These helper lemmas mirror the Rust allocator order for RV64 word min/max atomics.
-/

theorem amo_word_rust_select_pre64_aligned_run
    (tail : JoltISA.Program)
    (rs1 : regidx) (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hbytes : MemBytesPresentAt js.sail (amoWordBase addr) 8)
    (hload_pmp : Assumptions.LoadPmpOk (amoWordBase addr) 8 js.sail)
    (hread_mmio : Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    ∃ js_pre : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoPre64ProgramWithScratch rs1 JoltISA.amoWordSelectOldVReg
          JoltISA.amoWordSelectDwordVReg JoltISA.amoWordSelectShiftVReg
          JoltISA.amoWordSelectNewVReg tail)).run js =
        (JoltISA.execProgram tail).run js_pre ∧
      js_pre.sail = js.sail ∧
      js_pre.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf ∧
      js_pre.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) ∧
      js_pre.vregs JoltISA.amoWordSelectOldVReg =
        amoWordShiftedOld addr
          (loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf) := by
  have hassert :=
    amo_word_virtual_assert_aligned_run rs1 js addr hrs1 h_align
  obtain ⟨js_base, _hrs1_base, hbase_sail, hbase_shift_raw,
      _hbase_preserves, hbase_run⟩ :=
    JoltISA.exists_state_after_andi_run_vreg_xreg_of_sail_eq
      JoltISA.amoWordSelectShiftVReg rs1 (-8 : BitVec 12)
      js js.sail addr rfl hrs1 (by unfold WritableVReg; decide)
  have hbase_shift :
      js_base.vregs JoltISA.amoWordSelectShiftVReg = amoWordBase addr := by
    rw [hbase_shift_raw]
    exact amo_word_base_mask addr
  have hpriv_base : Assumptions.CurPrivilegeMachine js_base.sail := by
    rw [hbase_sail]
    exact hpriv
  have hmprv_base : Assumptions.MstatusMprvZero js_base.sail := by
    rw [hbase_sail]
    exact hmprv
  have hbytes_base : MemBytesPresentAt js_base.sail (amoWordBase addr) 8 := by
    rw [hbase_sail]
    exact hbytes
  have hload_pmp_base :
      Assumptions.LoadPmpOk (amoWordBase addr) 8 js_base.sail := by
    rw [hbase_sail]
    exact hload_pmp
  have hread_mmio_base :
      Assumptions.NotReadableMmio (amoWordBase addr) 8 js_base.sail := by
    rw [hbase_sail]
    exact hread_mmio
  have hld :
      (JoltISA.execInstr
        (.LD .amo (.vreg JoltISA.amoWordSelectDwordVReg)
          (.vreg JoltISA.amoWordSelectShiftVReg) (0 : BitVec 12))).run js_base =
        .ok RETIRE_SUCCESS
          { sail := js_base.sail
            vregs := fun r =>
              if r = JoltISA.amoWordSelectDwordVReg then
                loaded_dword_at js_base.sail (amoWordBase addr)
                  hbytes_base h_no_ovf
              else js_base.vregs r } := by
    exact
      vreg_LD_run_of_aligned_dword_phys
        JoltISA.amoWordSelectDwordVReg JoltISA.amoWordSelectShiftVReg js_base
        (amoWordBase addr) hbase_shift
        hpriv_base hmprv_base
        (amo_word_base_aligned_access addr h_no_ovf)
        hbytes_base hload_pmp_base hread_mmio_base
        (by unfold WritableVReg; decide)
  let js_load : SailJoltState :=
    { sail := js_base.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
            hbytes_base h_no_ovf
        else js_base.vregs r }
  have hld_named :
      (JoltISA.execInstr
        (.LD .amo (.vreg JoltISA.amoWordSelectDwordVReg)
          (.vreg JoltISA.amoWordSelectShiftVReg) (0 : BitVec 12))).run js_base =
        .ok RETIRE_SUCCESS js_load := by
    exact hld
  have hload_sail : js_load.sail = js.sail := by
    exact hbase_sail
  have hload_dword :
      js_load.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf := by
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
            hbytes_base h_no_ovf
        else js_base.vregs JoltISA.amoWordSelectDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf
    rw [if_pos rfl]
    unfold loaded_dword_at loaded_byte_at loaded_byte_at_nat
    simp [hbase_sail]
  have hload_shift :
      js_load.vregs JoltISA.amoWordSelectShiftVReg = amoWordBase addr := by
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
            hbytes_base h_no_ovf
        else js_base.vregs JoltISA.amoWordSelectShiftVReg) =
        amoWordBase addr
    rw [if_neg (by decide)]
    exact hbase_shift
  have hrs1_load :
      rX_bits rs1 js_load.sail = .ok addr js_load.sail := by
    rw [hload_sail]
    exact hrs1
  have hmuli :
      (JoltISA.execInstr
        (.VirtualMULI (.vreg JoltISA.amoWordSelectShiftVReg)
          (.xreg rs1) (8 : BitVec 64))).run js_load =
      .ok RETIRE_SUCCESS
        { sail := js_load.sail
          vregs := fun r =>
            if r = JoltISA.amoWordSelectShiftVReg then
              jolt_virtual_muli_value addr (8 : BitVec 64)
            else js_load.vregs r } :=
    amo_word_virtual_muli_run_vreg_xreg
      JoltISA.amoWordSelectShiftVReg rs1 (8 : BitVec 64) js_load addr hrs1_load
      (by unfold WritableVReg; decide)
  let js_shift : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs r }
  have hmuli_named :
      (JoltISA.execInstr
        (.VirtualMULI (.vreg JoltISA.amoWordSelectShiftVReg)
          (.xreg rs1) (8 : BitVec 64))).run js_load =
      .ok RETIRE_SUCCESS js_shift := by
    exact hmuli
  have hshift_sail : js_shift.sail = js.sail := by
    exact hload_sail
  have hshift_dword :
      js_shift.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf := by
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs JoltISA.amoWordSelectDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf
    rw [if_neg (by decide)]
    exact hload_dword
  have hshift_shift :
      js_shift.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) := by
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs JoltISA.amoWordSelectShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_pos rfl]
    exact JoltISA.virtual_muli_eight_eq_shift_left_three addr
  have hbitmask :
      (JoltISA.execInstr
        (.VirtualShiftRightBitmask (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectShiftVReg))).run js_shift =
      .ok RETIRE_SUCCESS
        { sail := js_shift.sail
          vregs := fun r =>
            if r = JoltISA.amoWordSelectNewVReg then
              jolt_virtual_shift_right_bitmask_value
                (js_shift.vregs JoltISA.amoWordSelectShiftVReg)
            else js_shift.vregs r } :=
    JoltISA.virtual_shift_right_bitmask_run_vreg_vreg
      JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectShiftVReg js_shift
      (by unfold WritableVReg; decide)
  let js_bitmask : SailJoltState :=
    { sail := js_shift.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectNewVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSelectShiftVReg)
        else js_shift.vregs r }
  have hbitmask_named :
      (JoltISA.execInstr
        (.VirtualShiftRightBitmask (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectShiftVReg))).run js_shift =
      .ok RETIRE_SUCCESS js_bitmask := by
    exact hbitmask
  have hbitmask_sail : js_bitmask.sail = js.sail := by
    exact hshift_sail
  have hbitmask_dword :
      js_bitmask.vregs JoltISA.amoWordSelectDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf := by
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectNewVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSelectShiftVReg)
        else js_shift.vregs JoltISA.amoWordSelectDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf
    rw [if_neg (by decide)]
    exact hshift_dword
  have hbitmask_shift :
      js_bitmask.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) := by
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectNewVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSelectShiftVReg)
        else js_shift.vregs JoltISA.amoWordSelectShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_neg (by decide)]
    exact hshift_shift
  have hbitmask_tmp :
      js_bitmask.vregs JoltISA.amoWordSelectNewVReg =
        jolt_virtual_shift_right_bitmask_value
          (shift_bits_left addr (3 : BitVec 6)) := by
    change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectNewVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSelectShiftVReg)
        else js_shift.vregs JoltISA.amoWordSelectNewVReg) =
        jolt_virtual_shift_right_bitmask_value
          (shift_bits_left addr (3 : BitVec 6))
    rw [if_pos rfl, hshift_shift]
  have hsrl :
      (JoltISA.execInstr
        (.VirtualSRL (.vreg JoltISA.amoWordSelectOldVReg)
          (.vreg JoltISA.amoWordSelectDwordVReg)
          (.vreg JoltISA.amoWordSelectNewVReg))).run js_bitmask =
      .ok RETIRE_SUCCESS
        { sail := js_bitmask.sail
          vregs := fun r =>
            if r = JoltISA.amoWordSelectOldVReg then
              jolt_virtual_srl_value
                (js_bitmask.vregs JoltISA.amoWordSelectDwordVReg)
                (js_bitmask.vregs JoltISA.amoWordSelectNewVReg)
            else js_bitmask.vregs r } :=
    JoltISA.virtual_srl_run_vreg_vreg_vreg
      JoltISA.amoWordSelectOldVReg JoltISA.amoWordSelectDwordVReg
      JoltISA.amoWordSelectNewVReg js_bitmask
      (by unfold WritableVReg; decide)
  let js_pre : SailJoltState :=
    { sail := js_bitmask.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSelectDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSelectNewVReg)
        else js_bitmask.vregs r }
  have hsrl_named :
      (JoltISA.execInstr
        (.VirtualSRL (.vreg JoltISA.amoWordSelectOldVReg)
          (.vreg JoltISA.amoWordSelectDwordVReg)
          (.vreg JoltISA.amoWordSelectNewVReg))).run js_bitmask =
      .ok RETIRE_SUCCESS js_pre := by
    exact hsrl
  refine ⟨js_pre, ?_, ?_, ?_, ?_, ?_⟩
  · unfold JoltISA.amoPre64ProgramWithScratch
    rw [JoltISA.execProgram_instr_run_retire _ _ js js hassert]
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_base hbase_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_base js_load hld_named]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_load js_shift hmuli_named]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_shift js_bitmask hbitmask_named]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_bitmask js_pre hsrl_named]
  · exact hbitmask_sail
  · change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSelectDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSelectNewVReg)
        else js_bitmask.vregs JoltISA.amoWordSelectDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf
    rw [if_neg (by decide)]
    exact hbitmask_dword
  · change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSelectDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSelectNewVReg)
        else js_bitmask.vregs JoltISA.amoWordSelectShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_neg (by decide)]
    exact hbitmask_shift
  · change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSelectDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSelectNewVReg)
        else js_bitmask.vregs JoltISA.amoWordSelectOldVReg) =
        amoWordShiftedOld addr
          (loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf)
    rw [if_pos rfl, hbitmask_dword, hbitmask_tmp]
    exact
      JoltISA.virtual_srl_shift_right_bitmask_value_eq
        (loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf)
        (shift_bits_left addr (3 : BitVec 6))


/-- The first two postlude instructions seed the low-word mask and preserve the
loaded dword, lane shift, and old word. -/
theorem amo_word_rust_select_mask32_prefix_run
    (js : SailJoltState) (s : SailState) (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_shift : js.vregs JoltISA.amoWordSelectShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSelectMaskVReg =
        (0x00000000FFFFFFFF : BitVec 64) ∧
      js'.vregs JoltISA.amoWordSelectShiftVReg = shift64 ∧
      js'.vregs JoltISA.amoWordSelectDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      js'.vregs JoltISA.amoWordSelectNewVReg = js.vregs JoltISA.amoWordSelectNewVReg ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.ORI (.vreg JoltISA.amoWordSelectMaskVReg)
            (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
           .instr (.VirtualSRLI (.vreg JoltISA.amoWordSelectMaskVReg)
            (.vreg JoltISA.amoWordSelectMaskVReg)
            (JoltISA.srliBitmask (32 : BitVec 6))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js_ones, _hx0, hones_sail_raw, hones_mask_raw,
      hones_preserves, hones_run⟩ :=
    JoltISA.exists_state_after_ori_run_vreg_xreg_of_sail_eq
      JoltISA.amoWordSelectMaskVReg (regidx.Regidx 0) (-1 : BitVec 12)
      js s (0#64) h_sail (amo_word_read_x0_eq_zero s) (by unfold WritableVReg; decide)
  have hones_sail : js_ones.sail = s := by
    rw [hones_sail_raw, h_sail]
  have hones_mask : js_ones.vregs JoltISA.amoWordSelectMaskVReg = (-1 : BitVec 64) := by
    rw [hones_mask_raw]
    exact amo_word_seed_mask_value
  have hones_shift : js_ones.vregs JoltISA.amoWordSelectShiftVReg = shift64 := by
    rw [hones_preserves JoltISA.amoWordSelectShiftVReg (by decide)]
    exact h_shift
  have hones_dword : js_ones.vregs JoltISA.amoWordSelectDwordVReg = dword := by
    rw [hones_preserves JoltISA.amoWordSelectDwordVReg (by decide)]
    exact h_dword
  have hones_old : js_ones.vregs JoltISA.amoWordSelectOldVReg = old := by
    rw [hones_preserves JoltISA.amoWordSelectOldVReg (by decide)]
    exact h_old
  have hones_new :
      js_ones.vregs JoltISA.amoWordSelectNewVReg = js.vregs JoltISA.amoWordSelectNewVReg := by
    rw [hones_preserves JoltISA.amoWordSelectNewVReg (by decide)]
  obtain ⟨js_mask, hmask_sail_raw, hmask_raw, hmask_preserves,
      hmask_tail⟩ :=
    JoltISA.exists_state_after_srli_block_run_vreg_vreg
      JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectMaskVReg (32 : BitVec 6) js_ones
      (by unfold WritableVReg; decide)
  refine ⟨js_mask, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmask_sail_raw, hones_sail]
  · rw [hmask_raw, hones_mask]
    exact amo_word_low_word_mask_value
  · rw [hmask_preserves JoltISA.amoWordSelectShiftVReg (by decide)]
    exact hones_shift
  · rw [hmask_preserves JoltISA.amoWordSelectDwordVReg (by decide)]
    exact hones_dword
  · rw [hmask_preserves JoltISA.amoWordSelectOldVReg (by decide)]
    exact hones_old
  · rw [hmask_preserves JoltISA.amoWordSelectNewVReg (by decide)]
    exact hones_new
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_ones hones_run]
    have htail := hmask_tail tail
    unfold JoltISA.srliBlock at htail
    exact htail

/-- The postlude's mask-shift block turns the low-word mask into the selected
word-lane mask. -/
theorem amo_word_rust_select_shift_mask_prefix_run
    (js : SailJoltState) (s : SailState) (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_mask : js.vregs JoltISA.amoWordSelectMaskVReg =
      (0x00000000FFFFFFFF : BitVec 64))
    (h_shift : js.vregs JoltISA.amoWordSelectShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSelectMaskVReg =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoWordSelectShiftVReg = shift64 ∧
      js'.vregs JoltISA.amoWordSelectDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      js'.vregs JoltISA.amoWordSelectNewVReg = js.vregs JoltISA.amoWordSelectNewVReg ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoWordSelectInlineTmpVReg)
            (.vreg JoltISA.amoWordSelectShiftVReg)) <|
           .instr (.MUL (.vreg JoltISA.amoWordSelectMaskVReg)
            (.vreg JoltISA.amoWordSelectMaskVReg)
            (.vreg JoltISA.amoWordSelectInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', h_sail_raw, h_mask_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectMaskVReg
      JoltISA.amoWordSelectShiftVReg JoltISA.amoWordSelectInlineTmpVReg js (by decide) (by unfold WritableVReg; decide) (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_mask_raw, h_mask, h_shift]
  · rw [h_preserves JoltISA.amoWordSelectShiftVReg (by decide) (by decide)]
    exact h_shift
  · rw [h_preserves JoltISA.amoWordSelectDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSelectOldVReg (by decide) (by decide)]
    exact h_old
  · rw [h_preserves JoltISA.amoWordSelectNewVReg (by decide) (by decide)]
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- The postlude shifts the new word value from `rs2` into the selected dword
lane while preserving the prepared mask and old word. -/
theorem amo_word_rust_select_shift_new_prefix_run
    (rs2 : regidx) (js : SailJoltState) (s : SailState)
    (rs2Val shift64 shiftedMask dword old : BitVec 64)
    (h_sail : js.sail = s)
    (hrs2 : rX_bits rs2 s = .ok rs2Val s)
    (h_mask : js.vregs JoltISA.amoWordSelectMaskVReg = shiftedMask)
    (h_shift : js.vregs JoltISA.amoWordSelectShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left rs2Val (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoWordSelectMaskVReg = shiftedMask ∧
      js'.vregs JoltISA.amoWordSelectDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoWordSelectInlineTmpVReg)
            (.vreg JoltISA.amoWordSelectShiftVReg)) <|
           .instr (.MUL (.vreg JoltISA.amoWordSelectShiftVReg)
            (.xreg rs2) (.vreg JoltISA.amoWordSelectInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  have hrs2_current : rX_bits rs2 js.sail = .ok rs2Val js.sail := by
    rw [h_sail]
    exact hrs2
  obtain ⟨js', _hrs2, h_sail_raw, h_shift_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_xreg_vreg
      JoltISA.amoWordSelectShiftVReg rs2 JoltISA.amoWordSelectShiftVReg
      JoltISA.amoWordSelectInlineTmpVReg js rs2Val hrs2_current (by unfold WritableVReg; decide) (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_shift_raw, h_shift]
  · rw [h_preserves JoltISA.amoWordSelectMaskVReg (by decide) (by decide)]
    exact h_mask
  · rw [h_preserves JoltISA.amoWordSelectDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSelectOldVReg (by decide) (by decide)]
    exact h_old
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- The postlude shifts a virtual-register new word value into the selected
dword lane while preserving the prepared mask and old word. -/
theorem amo_word_rust_select_shift_new_vreg_prefix_run
    (new : JoltISA.VReg) (js : SailJoltState) (s : SailState)
    (newValue shift64 shiftedMask dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_new : js.vregs new = newValue)
    (h_mask : js.vregs JoltISA.amoWordSelectMaskVReg = shiftedMask)
    (h_shift : js.vregs JoltISA.amoWordSelectShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (hnew_ne_tmp : new ≠ JoltISA.amoWordSelectInlineTmpVReg) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left newValue (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoWordSelectMaskVReg = shiftedMask ∧
      js'.vregs JoltISA.amoWordSelectDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoWordSelectInlineTmpVReg)
            (.vreg JoltISA.amoWordSelectShiftVReg)) <|
           .instr (.MUL (.vreg JoltISA.amoWordSelectShiftVReg)
            (.vreg new) (.vreg JoltISA.amoWordSelectInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', h_sail_raw, h_shift_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      JoltISA.amoWordSelectShiftVReg new JoltISA.amoWordSelectShiftVReg
      JoltISA.amoWordSelectInlineTmpVReg js hnew_ne_tmp (by unfold WritableVReg; decide) (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_shift_raw, h_new, h_shift]
  · rw [h_preserves JoltISA.amoWordSelectMaskVReg (by decide) (by decide)]
    exact h_mask
  · rw [h_preserves JoltISA.amoWordSelectDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSelectOldVReg (by decide) (by decide)]
    exact h_old
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- The XOR/AND/XOR postlude block splices the shifted new word into the loaded
dword and preserves the shifted old word. -/
theorem amo_word_rust_select_splice_block_run
    (js : SailJoltState) (s : SailState)
    (addr newValue dword old : BitVec 64)
    (hsetup : StoreSplice.WordStoreFacts addr (amoWordBase addr))
    (h_sail : js.sail = s)
    (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (h_shift :
      js.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left newValue
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_mask :
      js.vregs JoltISA.amoWordSelectMaskVReg =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSelectDwordVReg =
        amoWordSplicedDword addr newValue dword ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.XOR (.vreg JoltISA.amoWordSelectShiftVReg)
            (.vreg JoltISA.amoWordSelectDwordVReg)
            (.vreg JoltISA.amoWordSelectShiftVReg)) <|
           .instr (.AND (.vreg JoltISA.amoWordSelectShiftVReg)
            (.vreg JoltISA.amoWordSelectShiftVReg)
            (.vreg JoltISA.amoWordSelectMaskVReg)) <|
           .instr (.XOR (.vreg JoltISA.amoWordSelectDwordVReg)
            (.vreg JoltISA.amoWordSelectDwordVReg)
            (.vreg JoltISA.amoWordSelectShiftVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let shiftedNew :=
    shift_bits_left newValue
      (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
  let shiftedMask :=
    shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
      (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
  obtain ⟨js_xor, hxor_sail_raw, hxor_shift_raw, hxor_preserves,
      hxor_run⟩ :=
    JoltISA.exists_state_after_xor_run_vreg_vreg_vreg
      JoltISA.amoWordSelectShiftVReg JoltISA.amoWordSelectDwordVReg
      JoltISA.amoWordSelectShiftVReg js dword shiftedNew h_dword h_shift (by unfold WritableVReg; decide)
  have hxor_sail : js_xor.sail = s := by
    rw [hxor_sail_raw, h_sail]
  have hxor_shift : js_xor.vregs JoltISA.amoWordSelectShiftVReg = dword ^^^ shiftedNew := by
    exact hxor_shift_raw
  have hxor_mask : js_xor.vregs JoltISA.amoWordSelectMaskVReg = shiftedMask := by
    rw [hxor_preserves JoltISA.amoWordSelectMaskVReg (by decide)]
    exact h_mask
  have hxor_dword : js_xor.vregs JoltISA.amoWordSelectDwordVReg = dword := by
    rw [hxor_preserves JoltISA.amoWordSelectDwordVReg (by decide)]
    exact h_dword
  have hxor_old : js_xor.vregs JoltISA.amoWordSelectOldVReg = old := by
    rw [hxor_preserves JoltISA.amoWordSelectOldVReg (by decide)]
    exact h_old
  obtain ⟨js_and, hand_sail_raw, hand_shift_raw, hand_preserves,
      hand_run⟩ :=
    amo_word_exists_state_after_and_run_vreg_vreg_vreg
      JoltISA.amoWordSelectShiftVReg JoltISA.amoWordSelectShiftVReg JoltISA.amoWordSelectMaskVReg
      js_xor (dword ^^^ shiftedNew) shiftedMask hxor_shift hxor_mask
      (by unfold WritableVReg; decide)
  have hand_sail : js_and.sail = s := by
    rw [hand_sail_raw, hxor_sail]
  have hand_shift : js_and.vregs JoltISA.amoWordSelectShiftVReg =
      (dword ^^^ shiftedNew) &&& shiftedMask := by
    exact hand_shift_raw
  have hand_dword : js_and.vregs JoltISA.amoWordSelectDwordVReg = dword := by
    rw [hand_preserves JoltISA.amoWordSelectDwordVReg (by decide)]
    exact hxor_dword
  have hand_old : js_and.vregs JoltISA.amoWordSelectOldVReg = old := by
    rw [hand_preserves JoltISA.amoWordSelectOldVReg (by decide)]
    exact hxor_old
  obtain ⟨js_splice, hsplice_sail_raw, hsplice_dword_raw,
      hsplice_preserves, hxor2_run⟩ :=
    JoltISA.exists_state_after_xor_run_vreg_vreg_vreg
      JoltISA.amoWordSelectDwordVReg JoltISA.amoWordSelectDwordVReg
      JoltISA.amoWordSelectShiftVReg js_and dword
      ((dword ^^^ shiftedNew) &&& shiftedMask) hand_dword hand_shift (by unfold WritableVReg; decide)
  have hspliced_value := amo_word_splice_shifted_eq addr newValue dword hsetup
  refine ⟨js_splice, ?_, ?_, ?_, ?_⟩
  · rw [hsplice_sail_raw, hand_sail]
  · rw [hsplice_dword_raw]
    exact hspliced_value
  · rw [hsplice_preserves JoltISA.amoWordSelectOldVReg (by decide)]
    exact hand_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_xor hxor_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_xor js_and hand_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_and js_splice hxor2_run]

/-- The postlude recomputes the enclosing dword base before storing it. -/
theorem amo_word_rust_select_store_base_prefix_run
    (rs1 : regidx) (js : SailJoltState) (s : SailState)
    (addr dwordNew old : BitVec 64)
    (h_sail : js.sail = s)
    (hrs1 : rX_bits rs1 s = .ok addr s)
    (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dwordNew)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSelectMaskVReg = amoWordBase addr ∧
      js'.vregs JoltISA.amoWordSelectDwordVReg = dwordNew ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.ANDI (.vreg JoltISA.amoWordSelectMaskVReg)
            (.xreg rs1) (-8 : BitVec 12)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', _hrs1, h_sail_raw, h_base_raw, h_preserves, hrun⟩ :=
    JoltISA.exists_state_after_andi_run_vreg_xreg_of_sail_eq
      JoltISA.amoWordSelectMaskVReg rs1 (-8 : BitVec 12) js s addr h_sail hrs1 (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_base_raw]
    exact amo_word_base_mask addr
  · rw [h_preserves JoltISA.amoWordSelectDwordVReg (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSelectOldVReg (by decide)]
    exact h_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hrun]

/-- The dword store instruction writes the spliced dword and preserves the
virtual-register file for the final writeback. -/
theorem amo_word_rust_select_sd_spliced_dword_run
    (js : SailJoltState) (s : SailState) (addr dwordNew old : BitVec 64)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 s)
    (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 s)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_sail : js.sail = s)
    (h_base : js.vregs JoltISA.amoWordSelectMaskVReg = amoWordBase addr)
    (h_dword : js.vregs JoltISA.amoWordSelectDwordVReg = dwordNew)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old) :
    ∃ js',
      js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
      js'.vregs JoltISA.amoWordSelectOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.SD (.vreg JoltISA.amoWordSelectMaskVReg)
            (.vreg JoltISA.amoWordSelectDwordVReg) (0 : BitVec 12)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  have hwrite_dword :
      vmem_write_addr (Virtaddr (amoWordBase addr)) 8 dwordNew
        (Store Data) false false false s =
      .ok (Ok true) (state_after_dword_store s (amoWordBase addr) dwordNew) :=
    vmem_write_addr_dword_store_reduces (amoWordBase addr) dwordNew s
      hpriv hmprv
      (amo_word_base_aligned_access addr h_no_ovf).toAlignedAccess
      hstore_pmp hwrite_mmio
  have hwrite_current :
      vmem_write_addr (Virtaddr (js.vregs JoltISA.amoWordSelectMaskVReg +
          sign_extend (m := 64) (0 : BitVec 12))) 8
        (js.vregs JoltISA.amoWordSelectDwordVReg)
        (Store Data) false false false js.sail =
      .ok (Ok true) (state_after_dword_store s (amoWordBase addr) dwordNew) := by
    rw [h_sail, h_base, h_dword, amo_word_zero_offset_addr (amoWordBase addr)]
    exact hwrite_dword
  let js' : SailJoltState :=
    { sail := state_after_dword_store s (amoWordBase addr) dwordNew
      vregs := js.vregs }
  have hsd_align :
      (js.vregs JoltISA.amoWordSelectMaskVReg + sign_extend (m := 64) (0 : BitVec 12)) &&&
          (7 : BitVec 64) =
        0 := by
    rw [h_base, amo_word_zero_offset_addr (amoWordBase addr)]
    exact amo_word_base_aligned addr
  have hsd :
      (JoltISA.execInstr
        (.SD (.vreg JoltISA.amoWordSelectMaskVReg)
          (.vreg JoltISA.amoWordSelectDwordVReg) (0 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS js' :=
    JoltISA.execInstr_sd_vreg_run_of_write
      JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectDwordVReg (0 : BitVec 12)
      js (state_after_dword_store s (amoWordBase addr) dwordNew) hsd_align hwrite_current
  refine ⟨js', rfl, ?_, ?_⟩
  · exact h_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hsd]

/-- The final postlude instruction writes the sign-extended old word to `rd`. -/
theorem amo_word_rust_select_writeback_old_run
    (rd : regidx) (js : SailJoltState) (s : SailState)
    (addr : BitVec 64) (result oldWord : BitVec 32) (old : BitVec 64)
    (h_sail : js.sail = state_after_word_store s addr result)
    (h_old : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (h_old_word :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) oldWord) :
    ∃ js',
      js'.sail = amoWordFinalSailState rd s addr result oldWord ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualSignExtendWord (JoltISA.amoDstFor rd)
          (.vreg JoltISA.amoWordSelectOldVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  exact
    amo_word_writeback_old_run_from JoltISA.amoWordSelectOldVReg
      rd js s addr result oldWord old h_sail h_old h_old_word

/-- The aligned word-AMO postlude stores the low 32 bits of a virtual-register
new value into the selected word lane and writes the sign-extended old word
into `rd`. -/
theorem amo_word_rust_select_post64_vreg_aligned_run
    (rs1 rd : regidx)
    (js js_pre : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (addr newValue dword : BitVec 64) (oldWord : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
    (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail)
    (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hdword :
      dword =
        loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf)
    (hpre_sail : js_pre.sail = js.sail)
    (hpre_new : js_pre.vregs JoltISA.amoWordSelectNewVReg = newValue)
    (hpre_dword :
      js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hpre_shift :
      js_pre.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6))
    (hpre_old :
      js_pre.vregs JoltISA.amoWordSelectOldVReg =
        amoWordShiftedOld addr dword)
    (hold :
      (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
        BitVec 32) = oldWord) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoPost64ProgramWithScratch rs1 rd (.vreg JoltISA.amoWordSelectNewVReg)
          JoltISA.amoWordSelectDwordVReg JoltISA.amoWordSelectShiftVReg
          JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectOldVReg
          JoltISA.amoWordSelectInlineTmpVReg)).run js_pre =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoWordFinalSailState rd js.sail addr
          (Sail.BitVec.extractLsb newValue 31 0) oldWord := by
  let shift64 := shift_bits_left addr (3 : BitVec 6)
  let shift6 := Sail.BitVec.extractLsb shift64 5 0
  let old := amoWordShiftedOld addr dword
  let mask32 := (0x00000000FFFFFFFF : BitVec 64)
  let shiftedMask := shift_bits_left mask32 shift6
  let dwordNew := amoWordSplicedDword addr newValue dword
  let wordResult : BitVec 32 := Sail.BitVec.extractLsb newValue 31 0
  have hsetup := amo_word_store_facts addr h_no_ovf h_align
  obtain ⟨js_mask32, hmask_sail, hmask_mask, hmask_shift, hmask_dword,
      hmask_old, hmask_new_preserve, hmask_tail⟩ :=
    amo_word_rust_select_mask32_prefix_run js_pre js.sail shift64 dword old
      hpre_sail hpre_shift hpre_dword (by simpa [old] using hpre_old)
  have hmask_new : js_mask32.vregs JoltISA.amoWordSelectNewVReg = newValue := by
    rw [hmask_new_preserve]
    exact hpre_new
  obtain ⟨js_shifted_mask, hshift_mask_sail, hshift_mask_mask,
      hshift_mask_shift, hshift_mask_dword, hshift_mask_old,
      hshift_mask_new_preserve, hshift_mask_tail⟩ :=
    amo_word_rust_select_shift_mask_prefix_run js_mask32 js.sail shift64 dword old
      hmask_sail hmask_mask hmask_shift hmask_dword hmask_old
  have hshift_mask_new :
      js_shifted_mask.vregs JoltISA.amoWordSelectNewVReg = newValue := by
    rw [hshift_mask_new_preserve]
    exact hmask_new
  obtain ⟨js_shifted_new, hshift_new_sail, hshift_new_shift,
      hshift_new_mask, hshift_new_dword, hshift_new_old,
      hshift_new_tail⟩ :=
    amo_word_rust_select_shift_new_vreg_prefix_run JoltISA.amoWordSelectNewVReg
      js_shifted_mask js.sail
      newValue shift64 shiftedMask dword old hshift_mask_sail
      hshift_mask_new hshift_mask_mask hshift_mask_shift
      hshift_mask_dword hshift_mask_old (by decide)
  obtain ⟨js_splice, hsplice_sail, hsplice_dword, hsplice_old,
      hsplice_tail⟩ :=
    amo_word_rust_select_splice_block_run js_shifted_new js.sail addr newValue
      dword old hsetup
      hshift_new_sail hshift_new_dword hshift_new_shift hshift_new_mask
      hshift_new_old
  obtain ⟨js_store_base, hstore_base_sail, hstore_base, hstore_base_dword,
      hstore_base_old, hstore_base_tail⟩ :=
    amo_word_rust_select_store_base_prefix_run rs1 js_splice js.sail addr dwordNew old
      hsplice_sail hrs1 hsplice_dword hsplice_old
  obtain ⟨js_store, hstore_sail, hstore_old, hstore_tail⟩ :=
    amo_word_rust_select_sd_spliced_dword_run js_store_base js.sail addr dwordNew old
      hpriv hmprv hstore_pmp hwrite_mmio h_no_ovf hstore_base_sail
      hstore_base hstore_base_dword hstore_base_old
  have hword_store :
      state_after_dword_store js.sail (amoWordBase addr) dwordNew =
        state_after_word_store js.sail addr wordResult := by
    subst dwordNew
    rw [hdword]
    exact
      amo_word_spliced_dword_store_eq_word_store
        js.sail addr newValue hsetup hbytes_base
  have hstore_sail_word :
      js_store.sail = state_after_word_store js.sail addr wordResult := by
    rw [hstore_sail, hword_store]
  have hold_writeback :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) oldWord := by
    exact
      amo_word_shifted_old_sign_extend_eq_loaded_word
        addr dword oldWord (by simpa [old] using hold)
  obtain ⟨jsf, hwriteback_sail, hwriteback_tail⟩ :=
    amo_word_rust_select_writeback_old_run rd js_store js.sail addr wordResult oldWord old
      hstore_sail_word hstore_old hold_writeback
  refine ⟨jsf, ?_, ?_⟩
  · unfold JoltISA.amoPost64ProgramWithScratch
    rw [hmask_tail]
    rw [hshift_mask_tail]
    rw [hshift_new_tail]
    rw [hsplice_tail]
    rw [hstore_base_tail]
    rw [hstore_tail]
    rw [hwriteback_tail]
    rfl
  · exact hwriteback_sail

/-- Selected-register version of `amo_word_rust_select_mask32_prefix_run`. -/
theorem amo_word_rust_select_mask32_prefix_run_for
    (rd : regidx) (js : SailJoltState) (s : SailState)
    (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_shift : js.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift64)
    (h_dword : js.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (h_old : js.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs (JoltISA.amoWordSelectMaskVRegFor rd) =
        (0x00000000FFFFFFFF : BitVec 64) ∧
      js'.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift64 ∧
      js'.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword ∧
      js'.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old ∧
      js'.vregs (JoltISA.amoWordSelectNewVRegFor rd) =
        js.vregs (JoltISA.amoWordSelectNewVRegFor rd) ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.ORI (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
            (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
           .instr (.VirtualSRLI (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
            (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
            (JoltISA.srliBitmask (32 : BitVec 6))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let maskReg := JoltISA.amoWordSelectMaskVRegFor rd
  let shiftReg := JoltISA.amoWordSelectShiftVRegFor rd
  let dwordReg := JoltISA.amoWordSelectDwordVRegFor rd
  let oldReg := JoltISA.amoWordSelectOldVRegFor rd
  let newReg := JoltISA.amoWordSelectNewVRegFor rd
  have hmask_w : WritableVReg maskReg := by
    unfold maskReg JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hshift_ne_mask : shiftReg ≠ maskReg := by
    unfold shiftReg maskReg JoltISA.amoWordSelectShiftVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_mask : dwordReg ≠ maskReg := by
    unfold dwordReg maskReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_mask : oldReg ≠ maskReg := by
    unfold oldReg maskReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hnew_ne_mask : newReg ≠ maskReg := by
    unfold newReg maskReg JoltISA.amoWordSelectNewVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  obtain ⟨js_ones, _hx0, hones_sail_raw, hones_mask_raw,
      hones_preserves, hones_run⟩ :=
    JoltISA.exists_state_after_ori_run_vreg_xreg_of_sail_eq
      maskReg (regidx.Regidx 0) (-1 : BitVec 12) js s (0#64)
      h_sail (amo_word_read_x0_eq_zero s) hmask_w
  have hones_sail : js_ones.sail = s := by
    rw [hones_sail_raw, h_sail]
  have hones_mask : js_ones.vregs maskReg = (-1 : BitVec 64) := by
    rw [hones_mask_raw]
    exact amo_word_seed_mask_value
  have hones_shift : js_ones.vregs shiftReg = shift64 := by
    rw [hones_preserves shiftReg hshift_ne_mask]
    exact h_shift
  have hones_dword : js_ones.vregs dwordReg = dword := by
    rw [hones_preserves dwordReg hdword_ne_mask]
    exact h_dword
  have hones_old : js_ones.vregs oldReg = old := by
    rw [hones_preserves oldReg hold_ne_mask]
    exact h_old
  have hones_new : js_ones.vregs newReg = js.vregs newReg := by
    rw [hones_preserves newReg hnew_ne_mask]
  obtain ⟨js_mask, hmask_sail_raw, hmask_raw, hmask_preserves,
      hmask_tail⟩ :=
    JoltISA.exists_state_after_srli_block_run_vreg_vreg
      maskReg maskReg (32 : BitVec 6) js_ones hmask_w
  refine ⟨js_mask, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmask_sail_raw, hones_sail]
  · rw [hmask_raw, hones_mask]
    exact amo_word_low_word_mask_value
  · rw [hmask_preserves shiftReg hshift_ne_mask]
    exact hones_shift
  · rw [hmask_preserves dwordReg hdword_ne_mask]
    exact hones_dword
  · rw [hmask_preserves oldReg hold_ne_mask]
    exact hones_old
  · rw [hmask_preserves newReg hnew_ne_mask]
    exact hones_new
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_ones hones_run]
    have htail := hmask_tail tail
    unfold JoltISA.srliBlock at htail
    simpa [maskReg] using htail

/-- Selected-register version of `amo_word_rust_select_shift_mask_prefix_run`. -/
theorem amo_word_rust_select_shift_mask_prefix_run_for
    (rd : regidx) (js : SailJoltState) (s : SailState)
    (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_mask : js.vregs (JoltISA.amoWordSelectMaskVRegFor rd) =
      (0x00000000FFFFFFFF : BitVec 64))
    (h_shift : js.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift64)
    (h_dword : js.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (h_old : js.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs (JoltISA.amoWordSelectMaskVRegFor rd) =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift64 ∧
      js'.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword ∧
      js'.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old ∧
      js'.vregs (JoltISA.amoWordSelectNewVRegFor rd) =
        js.vregs (JoltISA.amoWordSelectNewVRegFor rd) ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg (JoltISA.amoWordSelectInlineTmpVRegFor rd))
            (.vreg (JoltISA.amoWordSelectShiftVRegFor rd))) <|
           .instr (.MUL (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
            (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
            (.vreg (JoltISA.amoWordSelectInlineTmpVRegFor rd))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let maskReg := JoltISA.amoWordSelectMaskVRegFor rd
  let shiftReg := JoltISA.amoWordSelectShiftVRegFor rd
  let dwordReg := JoltISA.amoWordSelectDwordVRegFor rd
  let oldReg := JoltISA.amoWordSelectOldVRegFor rd
  let newReg := JoltISA.amoWordSelectNewVRegFor rd
  let tmpReg := JoltISA.amoWordSelectInlineTmpVRegFor rd
  have hmask_w : WritableVReg maskReg := by
    unfold maskReg JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have htmp_w : WritableVReg tmpReg := by
    unfold tmpReg JoltISA.amoWordSelectInlineTmpVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hmask_ne_tmp : maskReg ≠ tmpReg := by
    unfold maskReg tmpReg JoltISA.amoWordSelectMaskVRegFor
      JoltISA.amoWordSelectInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hshift_ne_mask : shiftReg ≠ maskReg := by
    unfold shiftReg maskReg JoltISA.amoWordSelectShiftVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hshift_ne_tmp : shiftReg ≠ tmpReg := by
    unfold shiftReg tmpReg JoltISA.amoWordSelectShiftVRegFor
      JoltISA.amoWordSelectInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_mask : dwordReg ≠ maskReg := by
    unfold dwordReg maskReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_tmp : dwordReg ≠ tmpReg := by
    unfold dwordReg tmpReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_mask : oldReg ≠ maskReg := by
    unfold oldReg maskReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_tmp : oldReg ≠ tmpReg := by
    unfold oldReg tmpReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hnew_ne_mask : newReg ≠ maskReg := by
    unfold newReg maskReg JoltISA.amoWordSelectNewVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hnew_ne_tmp : newReg ≠ tmpReg := by
    unfold newReg tmpReg JoltISA.amoWordSelectNewVRegFor
      JoltISA.amoWordSelectInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  obtain ⟨js', h_sail_raw, h_mask_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      maskReg maskReg shiftReg tmpReg js hmask_ne_tmp hmask_w htmp_w
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_mask_raw, h_mask, h_shift]
  · rw [h_preserves shiftReg hshift_ne_mask hshift_ne_tmp]
    exact h_shift
  · rw [h_preserves dwordReg hdword_ne_mask hdword_ne_tmp]
    exact h_dword
  · rw [h_preserves oldReg hold_ne_mask hold_ne_tmp]
    exact h_old
  · rw [h_preserves newReg hnew_ne_mask hnew_ne_tmp]
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    simpa [maskReg, shiftReg, tmpReg] using h

/-- Selected-register version of
`amo_word_rust_select_shift_new_vreg_prefix_run`, specialized to Rust's
word-select `new` register for `rd`. -/
theorem amo_word_rust_select_shift_new_vreg_prefix_run_for
    (rd : regidx) (js : SailJoltState) (s : SailState)
    (newValue shift64 shiftedMask dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_new : js.vregs (JoltISA.amoWordSelectNewVRegFor rd) = newValue)
    (h_mask : js.vregs (JoltISA.amoWordSelectMaskVRegFor rd) = shiftedMask)
    (h_shift : js.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift64)
    (h_dword : js.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (h_old : js.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs (JoltISA.amoWordSelectShiftVRegFor rd) =
        shift_bits_left newValue (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs (JoltISA.amoWordSelectMaskVRegFor rd) = shiftedMask ∧
      js'.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword ∧
      js'.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg (JoltISA.amoWordSelectInlineTmpVRegFor rd))
            (.vreg (JoltISA.amoWordSelectShiftVRegFor rd))) <|
           .instr (.MUL (.vreg (JoltISA.amoWordSelectShiftVRegFor rd))
            (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
            (.vreg (JoltISA.amoWordSelectInlineTmpVRegFor rd))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let maskReg := JoltISA.amoWordSelectMaskVRegFor rd
  let shiftReg := JoltISA.amoWordSelectShiftVRegFor rd
  let dwordReg := JoltISA.amoWordSelectDwordVRegFor rd
  let oldReg := JoltISA.amoWordSelectOldVRegFor rd
  let newReg := JoltISA.amoWordSelectNewVRegFor rd
  let tmpReg := JoltISA.amoWordSelectInlineTmpVRegFor rd
  have hshift_w : WritableVReg shiftReg := by
    unfold shiftReg JoltISA.amoWordSelectShiftVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have htmp_w : WritableVReg tmpReg := by
    unfold tmpReg JoltISA.amoWordSelectInlineTmpVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hnew_ne_tmp : newReg ≠ tmpReg := by
    unfold newReg tmpReg JoltISA.amoWordSelectNewVRegFor
      JoltISA.amoWordSelectInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hmask_ne_shift : maskReg ≠ shiftReg := by
    unfold maskReg shiftReg JoltISA.amoWordSelectMaskVRegFor
      JoltISA.amoWordSelectShiftVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hmask_ne_tmp : maskReg ≠ tmpReg := by
    unfold maskReg tmpReg JoltISA.amoWordSelectMaskVRegFor
      JoltISA.amoWordSelectInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_shift : dwordReg ≠ shiftReg := by
    unfold dwordReg shiftReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectShiftVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_tmp : dwordReg ≠ tmpReg := by
    unfold dwordReg tmpReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_shift : oldReg ≠ shiftReg := by
    unfold oldReg shiftReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectShiftVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_tmp : oldReg ≠ tmpReg := by
    unfold oldReg tmpReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  obtain ⟨js', h_sail_raw, h_shift_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      shiftReg newReg shiftReg tmpReg js hnew_ne_tmp hshift_w htmp_w
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_shift_raw, h_new, h_shift]
  · rw [h_preserves maskReg hmask_ne_shift hmask_ne_tmp]
    exact h_mask
  · rw [h_preserves dwordReg hdword_ne_shift hdword_ne_tmp]
    exact h_dword
  · rw [h_preserves oldReg hold_ne_shift hold_ne_tmp]
    exact h_old
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    simpa [shiftReg, newReg, tmpReg] using h

/-- Selected-register version of `amo_word_rust_select_splice_block_run`. -/
theorem amo_word_rust_select_splice_block_run_for
    (rd : regidx) (js : SailJoltState) (s : SailState)
    (addr newValue dword old : BitVec 64)
    (hsetup : StoreSplice.WordStoreFacts addr (amoWordBase addr))
    (h_sail : js.sail = s)
    (h_dword : js.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (h_shift :
      js.vregs (JoltISA.amoWordSelectShiftVRegFor rd) =
        shift_bits_left newValue
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_mask :
      js.vregs (JoltISA.amoWordSelectMaskVRegFor rd) =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_old : js.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs (JoltISA.amoWordSelectDwordVRegFor rd) =
        amoWordSplicedDword addr newValue dword ∧
      js'.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.XOR (.vreg (JoltISA.amoWordSelectShiftVRegFor rd))
            (.vreg (JoltISA.amoWordSelectDwordVRegFor rd))
            (.vreg (JoltISA.amoWordSelectShiftVRegFor rd))) <|
           .instr (.AND (.vreg (JoltISA.amoWordSelectShiftVRegFor rd))
            (.vreg (JoltISA.amoWordSelectShiftVRegFor rd))
            (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))) <|
           .instr (.XOR (.vreg (JoltISA.amoWordSelectDwordVRegFor rd))
            (.vreg (JoltISA.amoWordSelectDwordVRegFor rd))
            (.vreg (JoltISA.amoWordSelectShiftVRegFor rd))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let maskReg := JoltISA.amoWordSelectMaskVRegFor rd
  let shiftReg := JoltISA.amoWordSelectShiftVRegFor rd
  let dwordReg := JoltISA.amoWordSelectDwordVRegFor rd
  let oldReg := JoltISA.amoWordSelectOldVRegFor rd
  let shiftedNew :=
    shift_bits_left newValue
      (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
  let shiftedMask :=
    shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
      (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
  have hshift_w : WritableVReg shiftReg := by
    unfold shiftReg JoltISA.amoWordSelectShiftVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hdword_w : WritableVReg dwordReg := by
    unfold dwordReg JoltISA.amoWordSelectDwordVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hmask_ne_shift : maskReg ≠ shiftReg := by
    unfold maskReg shiftReg JoltISA.amoWordSelectMaskVRegFor
      JoltISA.amoWordSelectShiftVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_shift : dwordReg ≠ shiftReg := by
    unfold dwordReg shiftReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectShiftVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_shift : oldReg ≠ shiftReg := by
    unfold oldReg shiftReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectShiftVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_dword : oldReg ≠ dwordReg := by
    unfold oldReg dwordReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectDwordVRegFor JoltISA.amoVRegFor
    split <;> decide
  obtain ⟨js_xor, hxor_sail_raw, hxor_shift_raw, hxor_preserves,
      hxor_run⟩ :=
    JoltISA.exists_state_after_xor_run_vreg_vreg_vreg
      shiftReg dwordReg shiftReg js dword shiftedNew h_dword h_shift
      hshift_w
  have hxor_sail : js_xor.sail = s := by
    rw [hxor_sail_raw, h_sail]
  have hxor_shift : js_xor.vregs shiftReg = dword ^^^ shiftedNew := by
    exact hxor_shift_raw
  have hxor_mask : js_xor.vregs maskReg = shiftedMask := by
    rw [hxor_preserves maskReg hmask_ne_shift]
    exact h_mask
  have hxor_dword : js_xor.vregs dwordReg = dword := by
    rw [hxor_preserves dwordReg hdword_ne_shift]
    exact h_dword
  have hxor_old : js_xor.vregs oldReg = old := by
    rw [hxor_preserves oldReg hold_ne_shift]
    exact h_old
  obtain ⟨js_and, hand_sail_raw, hand_shift_raw, hand_preserves,
      hand_run⟩ :=
    amo_word_exists_state_after_and_run_vreg_vreg_vreg
      shiftReg shiftReg maskReg js_xor (dword ^^^ shiftedNew) shiftedMask
      hxor_shift hxor_mask hshift_w
  have hand_sail : js_and.sail = s := by
    rw [hand_sail_raw, hxor_sail]
  have hand_shift : js_and.vregs shiftReg =
      (dword ^^^ shiftedNew) &&& shiftedMask := by
    exact hand_shift_raw
  have hand_dword : js_and.vregs dwordReg = dword := by
    rw [hand_preserves dwordReg hdword_ne_shift]
    exact hxor_dword
  have hand_old : js_and.vregs oldReg = old := by
    rw [hand_preserves oldReg hold_ne_shift]
    exact hxor_old
  obtain ⟨js_splice, hsplice_sail_raw, hsplice_dword_raw,
      hsplice_preserves, hxor2_run⟩ :=
    JoltISA.exists_state_after_xor_run_vreg_vreg_vreg
      dwordReg dwordReg shiftReg js_and dword
      ((dword ^^^ shiftedNew) &&& shiftedMask) hand_dword hand_shift
      hdword_w
  have hspliced_value := amo_word_splice_shifted_eq addr newValue dword hsetup
  refine ⟨js_splice, ?_, ?_, ?_, ?_⟩
  · rw [hsplice_sail_raw, hand_sail]
  · rw [hsplice_dword_raw]
    exact hspliced_value
  · rw [hsplice_preserves oldReg hold_ne_dword]
    exact hand_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_xor hxor_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_xor js_and hand_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_and js_splice hxor2_run]

/-- Selected-register version of
`amo_word_rust_select_store_base_prefix_run`. -/
theorem amo_word_rust_select_store_base_prefix_run_for
    (rd rs1 : regidx) (js : SailJoltState) (s : SailState)
    (addr dwordNew old : BitVec 64)
    (h_sail : js.sail = s)
    (hrs1 : rX_bits rs1 s = .ok addr s)
    (h_dword : js.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dwordNew)
    (h_old : js.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs (JoltISA.amoWordSelectMaskVRegFor rd) = amoWordBase addr ∧
      js'.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dwordNew ∧
      js'.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.ANDI (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
            (.xreg rs1) (-8 : BitVec 12)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let maskReg := JoltISA.amoWordSelectMaskVRegFor rd
  let dwordReg := JoltISA.amoWordSelectDwordVRegFor rd
  let oldReg := JoltISA.amoWordSelectOldVRegFor rd
  have hmask_w : WritableVReg maskReg := by
    unfold maskReg JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hdword_ne_mask : dwordReg ≠ maskReg := by
    unfold dwordReg maskReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_mask : oldReg ≠ maskReg := by
    unfold oldReg maskReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  obtain ⟨js', _hrs1, h_sail_raw, h_base_raw, h_preserves, hrun⟩ :=
    JoltISA.exists_state_after_andi_run_vreg_xreg_of_sail_eq
      maskReg rs1 (-8 : BitVec 12) js s addr h_sail hrs1 hmask_w
  refine ⟨js', ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_base_raw]
    exact amo_word_base_mask addr
  · rw [h_preserves dwordReg hdword_ne_mask]
    exact h_dword
  · rw [h_preserves oldReg hold_ne_mask]
    exact h_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hrun]

/-- Selected-register version of `amo_word_rust_select_sd_spliced_dword_run`. -/
theorem amo_word_rust_select_sd_spliced_dword_run_for
    (rd : regidx)
    (js : SailJoltState) (s : SailState) (addr dwordNew old : BitVec 64)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 s)
    (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 s)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_sail : js.sail = s)
    (h_base : js.vregs (JoltISA.amoWordSelectMaskVRegFor rd) = amoWordBase addr)
    (h_dword : js.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dwordNew)
    (h_old : js.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old) :
    ∃ js',
      js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
      js'.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.SD (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
            (.vreg (JoltISA.amoWordSelectDwordVRegFor rd))
            (0 : BitVec 12)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let maskReg := JoltISA.amoWordSelectMaskVRegFor rd
  let dwordReg := JoltISA.amoWordSelectDwordVRegFor rd
  have hwrite_dword :
      vmem_write_addr (Virtaddr (amoWordBase addr)) 8 dwordNew
        (Store Data) false false false s =
      .ok (Ok true) (state_after_dword_store s (amoWordBase addr) dwordNew) :=
    vmem_write_addr_dword_store_reduces (amoWordBase addr) dwordNew s
      hpriv hmprv
      (amo_word_base_aligned_access addr h_no_ovf).toAlignedAccess
      hstore_pmp hwrite_mmio
  have hwrite_current :
      vmem_write_addr (Virtaddr (js.vregs maskReg +
          sign_extend (m := 64) (0 : BitVec 12))) 8
        (js.vregs dwordReg)
        (Store Data) false false false js.sail =
      .ok (Ok true) (state_after_dword_store s (amoWordBase addr) dwordNew) := by
    rw [h_sail, h_base, h_dword, amo_word_zero_offset_addr (amoWordBase addr)]
    exact hwrite_dword
  let js' : SailJoltState :=
    { sail := state_after_dword_store s (amoWordBase addr) dwordNew
      vregs := js.vregs }
  have hsd_align :
      (js.vregs maskReg + sign_extend (m := 64) (0 : BitVec 12)) &&&
          (7 : BitVec 64) =
        0 := by
    rw [h_base, amo_word_zero_offset_addr (amoWordBase addr)]
    exact amo_word_base_aligned addr
  have hsd :
      (JoltISA.execInstr
        (.SD (.vreg maskReg) (.vreg dwordReg) (0 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS js' :=
    JoltISA.execInstr_sd_vreg_run_of_write
      maskReg dwordReg (0 : BitVec 12)
      js (state_after_dword_store s (amoWordBase addr) dwordNew)
      hsd_align hwrite_current
  refine ⟨js', rfl, ?_, ?_⟩
  · exact h_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hsd]

/-- Selected-register version of
`amo_word_rust_select_writeback_old_run`. -/
theorem amo_word_rust_select_writeback_old_run_for
    (rd : regidx) (js : SailJoltState) (s : SailState)
    (addr : BitVec 64) (result oldWord : BitVec 32) (old : BitVec 64)
    (h_sail : js.sail = state_after_word_store s addr result)
    (h_old : js.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old)
    (h_old_word :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) oldWord) :
    ∃ js',
      js'.sail = amoWordFinalSailState rd s addr result oldWord ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualSignExtendWord (JoltISA.amoDstFor rd)
          (.vreg (JoltISA.amoWordSelectOldVRegFor rd))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  exact
    amo_word_writeback_old_run_from (JoltISA.amoWordSelectOldVRegFor rd)
      rd js s addr result oldWord old h_sail h_old h_old_word

/-- Selected-register version of
`amo_word_rust_select_post64_vreg_aligned_run`. -/
theorem amo_word_rust_select_post64_vreg_aligned_run_for
    (rs1 rd : regidx)
    (js js_pre : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (addr newValue dword : BitVec 64) (oldWord : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
    (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail)
    (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hdword :
      dword =
        loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf)
    (hpre_sail : js_pre.sail = js.sail)
    (hpre_new : js_pre.vregs (JoltISA.amoWordSelectNewVRegFor rd) = newValue)
    (hpre_dword :
      js_pre.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (hpre_shift :
      js_pre.vregs (JoltISA.amoWordSelectShiftVRegFor rd) =
        shift_bits_left addr (3 : BitVec 6))
    (hpre_old :
      js_pre.vregs (JoltISA.amoWordSelectOldVRegFor rd) =
        amoWordShiftedOld addr dword)
    (hold :
      (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
        BitVec 32) = oldWord) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoPost64ProgramWithScratch rs1 rd
          (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
          (JoltISA.amoWordSelectDwordVRegFor rd)
          (JoltISA.amoWordSelectShiftVRegFor rd)
          (JoltISA.amoWordSelectMaskVRegFor rd)
          (JoltISA.amoWordSelectOldVRegFor rd)
          (JoltISA.amoWordSelectInlineTmpVRegFor rd))).run js_pre =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoWordFinalSailState rd js.sail addr
          (Sail.BitVec.extractLsb newValue 31 0) oldWord := by
  let shift64 := shift_bits_left addr (3 : BitVec 6)
  let shift6 := Sail.BitVec.extractLsb shift64 5 0
  let old := amoWordShiftedOld addr dword
  let mask32 := (0x00000000FFFFFFFF : BitVec 64)
  let shiftedMask := shift_bits_left mask32 shift6
  let dwordNew := amoWordSplicedDword addr newValue dword
  let wordResult : BitVec 32 := Sail.BitVec.extractLsb newValue 31 0
  have hsetup := amo_word_store_facts addr h_no_ovf h_align
  obtain ⟨js_mask32, hmask_sail, hmask_mask, hmask_shift, hmask_dword,
      hmask_old, hmask_new_preserve, hmask_tail⟩ :=
    amo_word_rust_select_mask32_prefix_run_for rd js_pre js.sail shift64
      dword old hpre_sail hpre_shift hpre_dword
      (by simpa [old] using hpre_old)
  have hmask_new :
      js_mask32.vregs (JoltISA.amoWordSelectNewVRegFor rd) = newValue := by
    rw [hmask_new_preserve]
    exact hpre_new
  obtain ⟨js_shifted_mask, hshift_mask_sail, hshift_mask_mask,
      hshift_mask_shift, hshift_mask_dword, hshift_mask_old,
      hshift_mask_new_preserve, hshift_mask_tail⟩ :=
    amo_word_rust_select_shift_mask_prefix_run_for rd js_mask32 js.sail
      shift64 dword old hmask_sail hmask_mask hmask_shift hmask_dword
      hmask_old
  have hshift_mask_new :
      js_shifted_mask.vregs (JoltISA.amoWordSelectNewVRegFor rd) =
        newValue := by
    rw [hshift_mask_new_preserve]
    exact hmask_new
  obtain ⟨js_shifted_new, hshift_new_sail, hshift_new_shift,
      hshift_new_mask, hshift_new_dword, hshift_new_old,
      hshift_new_tail⟩ :=
    amo_word_rust_select_shift_new_vreg_prefix_run_for rd js_shifted_mask
      js.sail newValue shift64 shiftedMask dword old hshift_mask_sail
      hshift_mask_new hshift_mask_mask hshift_mask_shift hshift_mask_dword
      hshift_mask_old
  obtain ⟨js_splice, hsplice_sail, hsplice_dword, hsplice_old,
      hsplice_tail⟩ :=
    amo_word_rust_select_splice_block_run_for rd js_shifted_new js.sail addr
      newValue dword old hsetup hshift_new_sail hshift_new_dword
      hshift_new_shift hshift_new_mask hshift_new_old
  obtain ⟨js_store_base, hstore_base_sail, hstore_base, hstore_base_dword,
      hstore_base_old, hstore_base_tail⟩ :=
    amo_word_rust_select_store_base_prefix_run_for rd rs1 js_splice js.sail
      addr dwordNew old hsplice_sail hrs1 hsplice_dword hsplice_old
  obtain ⟨js_store, hstore_sail, hstore_old, hstore_tail⟩ :=
    amo_word_rust_select_sd_spliced_dword_run_for rd js_store_base js.sail
      addr dwordNew old hpriv hmprv hstore_pmp hwrite_mmio h_no_ovf
      hstore_base_sail hstore_base hstore_base_dword hstore_base_old
  have hword_store :
      state_after_dword_store js.sail (amoWordBase addr) dwordNew =
        state_after_word_store js.sail addr wordResult := by
    subst dwordNew
    rw [hdword]
    exact
      amo_word_spliced_dword_store_eq_word_store
        js.sail addr newValue hsetup hbytes_base
  have hstore_sail_word :
      js_store.sail = state_after_word_store js.sail addr wordResult := by
    rw [hstore_sail, hword_store]
  have hold_writeback :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) oldWord := by
    exact
      amo_word_shifted_old_sign_extend_eq_loaded_word
        addr dword oldWord (by simpa [old] using hold)
  obtain ⟨jsf, hwriteback_sail, hwriteback_tail⟩ :=
    amo_word_rust_select_writeback_old_run_for rd js_store js.sail addr
      wordResult oldWord old hstore_sail_word hstore_old hold_writeback
  refine ⟨jsf, ?_, ?_⟩
  · unfold JoltISA.amoPost64ProgramWithScratch
    rw [hmask_tail]
    rw [hshift_mask_tail]
    rw [hshift_new_tail]
    rw [hsplice_tail]
    rw [hstore_base_tail]
    rw [hstore_tail]
    rw [hwriteback_tail]
    rfl
  · exact hwriteback_sail

def amoWordSelectRustExtendProgram
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (rs2 : regidx) (tail : JoltISA.Program) : JoltISA.Program :=
  .instr (extend (.vreg JoltISA.amoWordSelectNewVReg) (.xreg rs2)) <|
  .instr (extend (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg JoltISA.amoWordSelectOldVReg)) <|
  tail

/-- The word-select comparison overwrites `amoMaskVReg` with the selected
comparison flag. -/
def amoWordSelectRustCompareProgram
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (tail : JoltISA.Program) :
    JoltISA.Program :=
  .instr (cmpInstr (.vreg JoltISA.amoWordSelectMaskVReg) cmpLhs cmpRhs) tail

/-- The word-select tail computes `(rs2 - old) * flag + old` into
`amoNewVReg`. -/
def amoWordSelectRustTailProgram
    (rs2 : regidx) (tail : JoltISA.Program) : JoltISA.Program :=
  .instr (.SUB (.vreg JoltISA.amoWordSelectNewVReg)
    (.xreg rs2) (.vreg JoltISA.amoWordSelectOldVReg)) <|
  .instr (.MUL (.vreg JoltISA.amoWordSelectNewVReg)
    (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg)) <|
  .instr (.ADD (.vreg JoltISA.amoWordSelectNewVReg)
    (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectOldVReg)) <|
  tail

/-- The word-select middle is the extension phase, comparison phase, and
select-tail phase composed around an arbitrary continuation. -/
def amoWordSelectRustMiddleProgram
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (tail : JoltISA.Program) : JoltISA.Program :=
  amoWordSelectRustExtendProgram extend rs2 <|
  amoWordSelectRustCompareProgram cmpInstr cmpLhs cmpRhs <|
  amoWordSelectRustTailProgram rs2 tail

/-- Selected-register version of `amoWordSelectRustExtendProgram`. -/
def amoWordSelectRustExtendProgramFor
    (rd : regidx)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (rs2 : regidx) (tail : JoltISA.Program) : JoltISA.Program :=
  .instr (extend (.vreg (JoltISA.amoWordSelectNewVRegFor rd)) (.xreg rs2)) <|
  .instr (extend (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
    (.vreg (JoltISA.amoWordSelectOldVRegFor rd))) <|
  tail

/-- Selected-register version of `amoWordSelectRustCompareProgram`. -/
def amoWordSelectRustCompareProgramFor
    (rd : regidx)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (tail : JoltISA.Program) :
    JoltISA.Program :=
  .instr (cmpInstr (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
    cmpLhs cmpRhs) tail

/-- Selected-register version of `amoWordSelectRustTailProgram`. -/
def amoWordSelectRustTailProgramFor
    (rd : regidx) (rs2 : regidx) (tail : JoltISA.Program) :
    JoltISA.Program :=
  .instr (.SUB (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
    (.xreg rs2) (.vreg (JoltISA.amoWordSelectOldVRegFor rd))) <|
  .instr (.MUL (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
    (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
    (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))) <|
  .instr (.ADD (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
    (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
    (.vreg (JoltISA.amoWordSelectOldVRegFor rd))) <|
  tail

/-- Selected-register version of `amoWordSelectRustMiddleProgram`. -/
def amoWordSelectRustMiddleProgramFor
    (rd : regidx)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (tail : JoltISA.Program) : JoltISA.Program :=
  amoWordSelectRustExtendProgramFor rd extend rs2 <|
  amoWordSelectRustCompareProgramFor rd cmpInstr cmpLhs cmpRhs <|
  amoWordSelectRustTailProgramFor rd rs2 tail

/-- Shape produced by the extension phase of a word select AMO.

The phase writes the extended `rs2` word into `amoNewVReg`, the extended old
word into `amoMaskVReg`, and preserves the prelude values needed later. -/
structure AmoWordSelectRustExtendStep
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (rs2 : regidx)
    (old dword shift rs2Ext oldExt : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectRustExtendProgram extend rs2 tail)).run js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  rs2_ext_vreg : js_after.vregs JoltISA.amoWordSelectNewVReg = rs2Ext
  old_ext_vreg : js_after.vregs JoltISA.amoWordSelectMaskVReg = oldExt
  old_vreg : js_after.vregs JoltISA.amoWordSelectOldVReg = old
  dword_vreg : js_after.vregs JoltISA.amoWordSelectDwordVReg = dword
  shift_vreg : js_after.vregs JoltISA.amoWordSelectShiftVReg = shift

/-- Shape produced by the comparison phase of a word select AMO.

The phase overwrites `amoMaskVReg` with the comparison flag and preserves the
prelude values needed by the select tail and postlude. -/
structure AmoWordSelectRustCompareStep
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (old dword shift flag : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectRustCompareProgram cmpInstr cmpLhs cmpRhs tail)).run
          js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  flag_vreg : js_after.vregs JoltISA.amoWordSelectMaskVReg = flag
  old_vreg : js_after.vregs JoltISA.amoWordSelectOldVReg = old
  dword_vreg : js_after.vregs JoltISA.amoWordSelectDwordVReg = dword
  shift_vreg : js_after.vregs JoltISA.amoWordSelectShiftVReg = shift

/-- Shape produced by the select-tail phase of a word select AMO. -/
structure AmoWordSelectRustTailStep
    (rs2 : regidx) (old dword shift result : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectRustTailProgram rs2 tail)).run js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  result_vreg : js_after.vregs JoltISA.amoWordSelectNewVReg = result
  old_vreg : js_after.vregs JoltISA.amoWordSelectOldVReg = old
  dword_vreg : js_after.vregs JoltISA.amoWordSelectDwordVReg = dword
  shift_vreg : js_after.vregs JoltISA.amoWordSelectShiftVReg = shift

/-- Shape produced by the full word-select middle block. -/
structure AmoWordSelectRustMiddleStep
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (old dword shift result : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectRustMiddleProgram extend cmpInstr cmpLhs cmpRhs rs2
          tail)).run js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  result_vreg : js_after.vregs JoltISA.amoWordSelectNewVReg = result
  old_vreg : js_after.vregs JoltISA.amoWordSelectOldVReg = old
  dword_vreg : js_after.vregs JoltISA.amoWordSelectDwordVReg = dword
  shift_vreg : js_after.vregs JoltISA.amoWordSelectShiftVReg = shift

/-- Shape produced by the selected-register word-select middle block. -/
structure AmoWordSelectRustMiddleStepFor
    (rd : regidx)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (old dword shift result : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectRustMiddleProgramFor rd extend cmpInstr cmpLhs cmpRhs rs2
          tail)).run js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  result_vreg : js_after.vregs (JoltISA.amoWordSelectNewVRegFor rd) = result
  old_vreg : js_after.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old
  dword_vreg : js_after.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword
  shift_vreg : js_after.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift

structure AmoWordSelectRustExtendStepFor
    (rd : regidx)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (rs2 : regidx)
    (old dword shift rs2Ext oldExt : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectRustExtendProgramFor rd extend rs2 tail)).run js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  rs2_ext_vreg : js_after.vregs (JoltISA.amoWordSelectNewVRegFor rd) = rs2Ext
  old_ext_vreg : js_after.vregs (JoltISA.amoWordSelectMaskVRegFor rd) = oldExt
  old_vreg : js_after.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old
  dword_vreg : js_after.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword
  shift_vreg : js_after.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift

structure AmoWordSelectRustCompareStepFor
    (rd : regidx)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (old dword shift flag : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectRustCompareProgramFor rd cmpInstr cmpLhs cmpRhs tail)).run
          js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  flag_vreg : js_after.vregs (JoltISA.amoWordSelectMaskVRegFor rd) = flag
  old_vreg : js_after.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old
  dword_vreg : js_after.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword
  shift_vreg : js_after.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift

structure AmoWordSelectRustTailStepFor
    (rd : regidx) (rs2 : regidx) (old dword shift result : BitVec 64)
    (js_before js_after : SailJoltState) : Prop where
  run :
    ∀ tail,
      (JoltISA.execProgram
        (amoWordSelectRustTailProgramFor rd rs2 tail)).run js_before =
        (JoltISA.execProgram tail).run js_after
  sail : js_after.sail = js_before.sail
  result_vreg : js_after.vregs (JoltISA.amoWordSelectNewVRegFor rd) = result
  old_vreg : js_after.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old
  dword_vreg : js_after.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword
  shift_vreg : js_after.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift

theorem amo_word_rust_select_signed_extend_phase_run
    (rs2 : regidx) (js : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterExt : SailJoltState,
      AmoWordSelectRustExtendStep
        (fun dst src => .VirtualSignExtendWord dst src) rs2
        old dword shift
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
        js js_afterExt := by
  let rs2Ext : BitVec 64 :=
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
  let oldExt : BitVec 64 :=
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb old 31 0 : BitVec 32)
  let js_afterRs2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectNewVReg then rs2Ext else js.vregs r }
  let js_afterExt : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectMaskVReg then oldExt else js_afterRs2.vregs r }
  have hrs2_run :
      (JoltISA.execInstr
        (.VirtualSignExtendWord (.vreg JoltISA.amoWordSelectNewVReg)
          (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterRs2 := by
    exact
      JoltISA.virtual_sign_extend_word_run_vreg_xreg
        JoltISA.amoWordSelectNewVReg rs2 js rs2Val hrs2
        (by unfold WritableVReg; decide)
  have hold_afterRs2 :
      js_afterRs2.vregs JoltISA.amoWordSelectOldVReg = old := by
    change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold]
  have hold_run :
      (JoltISA.execInstr
        (.VirtualSignExtendWord (.vreg JoltISA.amoWordSelectMaskVReg)
          (.vreg JoltISA.amoWordSelectOldVReg))).run js_afterRs2 =
        .ok RETIRE_SUCCESS js_afterExt := by
    rw [JoltISA.virtual_sign_extend_word_run_vreg_vreg
      JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectOldVReg js_afterRs2
      (by unfold WritableVReg; decide)]
    unfold js_afterExt oldExt
    rw [hold_afterRs2]
  refine ⟨js_afterExt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustExtendProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterRs2 hrs2_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterRs2 js_afterExt hold_run]
  · rfl
  · change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectNewVReg) = rs2Ext
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectNewVReg) = rs2Ext
    rw [if_pos rfl]
  · change
      (if JoltISA.amoWordSelectMaskVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectMaskVReg) = oldExt
    rw [if_pos rfl]
  · change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold_afterRs2]
  · change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  · change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hshift]

/-- The unsigned word-select extension phase prepares unsigned comparison
operands for `AMOMINU.W` and `AMOMAXU.W`. -/
theorem amo_word_rust_select_unsigned_extend_phase_run
    (rs2 : regidx) (js : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterExt : SailJoltState,
      AmoWordSelectRustExtendStep
        (fun dst src => .VirtualZeroExtendWord dst src) rs2
        old dword shift
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
        js js_afterExt := by
  let rs2Ext : BitVec 64 :=
    zero_extend (m := 64)
      (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
  let oldExt : BitVec 64 :=
    zero_extend (m := 64)
      (Sail.BitVec.extractLsb old 31 0 : BitVec 32)
  let js_afterRs2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectNewVReg then rs2Ext else js.vregs r }
  let js_afterExt : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectMaskVReg then oldExt else js_afterRs2.vregs r }
  have hrs2_run :
      (JoltISA.execInstr
        (.VirtualZeroExtendWord (.vreg JoltISA.amoWordSelectNewVReg)
          (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterRs2 := by
    exact
      JoltISA.virtual_zero_extend_word_run_vreg_xreg
        JoltISA.amoWordSelectNewVReg rs2 js rs2Val hrs2
        (by unfold WritableVReg; decide)
  have hold_afterRs2 :
      js_afterRs2.vregs JoltISA.amoWordSelectOldVReg = old := by
    change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold]
  have hold_run :
      (JoltISA.execInstr
        (.VirtualZeroExtendWord (.vreg JoltISA.amoWordSelectMaskVReg)
          (.vreg JoltISA.amoWordSelectOldVReg))).run js_afterRs2 =
        .ok RETIRE_SUCCESS js_afterExt := by
    rw [amo_word_virtual_zero_extend_word_run_vreg_vreg
      JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectOldVReg js_afterRs2
      (by unfold WritableVReg; decide)]
    unfold js_afterExt oldExt
    rw [hold_afterRs2]
  refine ⟨js_afterExt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustExtendProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterRs2 hrs2_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterRs2 js_afterExt hold_run]
  · rfl
  · change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectNewVReg) = rs2Ext
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectNewVReg) = rs2Ext
    rw [if_pos rfl]
  · change
      (if JoltISA.amoWordSelectMaskVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectMaskVReg) = oldExt
    rw [if_pos rfl]
  · change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold_afterRs2]
  · change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  · change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectMaskVReg then oldExt
        else js_afterRs2.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide)]
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectNewVReg then rs2Ext
        else js.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hshift]

/-- A signed word-select comparison phase writes the signed less-than flag
between two prepared virtual operands. -/
theorem amo_word_rust_select_slt_compare_phase_run_vreg_vreg
    (lhs rhs : JoltISA.VReg) (js : SailJoltState)
    (x y old dword shift : BitVec 64)
    (hlhs : js.vregs lhs = x)
    (hrhs : js.vregs rhs = y)
    (hold : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterCmp : SailJoltState,
      AmoWordSelectRustCompareStep
        (fun dst lhs rhs => .SLT dst lhs rhs) (.vreg lhs) (.vreg rhs)
        old dword shift
        (zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y)))
        js js_afterCmp := by
  let flag : BitVec 64 :=
    zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y))
  let js_afterCmp : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectMaskVReg then flag else js.vregs r }
  have hcmp_run :
      (JoltISA.execInstr
        (.SLT (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg lhs) (.vreg rhs))).run
          js =
        .ok RETIRE_SUCCESS js_afterCmp := by
    rw [amo_word_slt_run_vreg_vreg_vreg JoltISA.amoWordSelectMaskVReg lhs rhs js
      (by unfold WritableVReg; decide)]
    unfold js_afterCmp flag
    rw [hlhs, hrhs]
  refine ⟨js_afterCmp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustCompareProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterCmp hcmp_run]
  · rfl
  · change
      (if JoltISA.amoWordSelectMaskVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectMaskVReg) =
      zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y))
    rw [if_pos rfl]
  · change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold]
  · change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  · change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hshift]

/-- An unsigned word-select comparison phase writes the unsigned less-than flag
between two prepared virtual operands. -/
theorem amo_word_rust_select_sltu_compare_phase_run_vreg_vreg
    (lhs rhs : JoltISA.VReg) (js : SailJoltState)
    (x y old dword shift : BitVec 64)
    (hlhs : js.vregs lhs = x)
    (hrhs : js.vregs rhs = y)
    (hold : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterCmp : SailJoltState,
      AmoWordSelectRustCompareStep
        (fun dst lhs rhs => .SLTU dst lhs rhs) (.vreg lhs) (.vreg rhs)
        old dword shift (jolt_sltu_value x y) js js_afterCmp := by
  let flag : BitVec 64 := jolt_sltu_value x y
  let js_afterCmp : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectMaskVReg then flag else js.vregs r }
  have hcmp_run :
      (JoltISA.execInstr
        (.SLTU (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg lhs) (.vreg rhs))).run
          js =
        .ok RETIRE_SUCCESS js_afterCmp := by
    rw [amo_word_sltu_run_vreg_vreg_vreg JoltISA.amoWordSelectMaskVReg lhs rhs js
      (by unfold WritableVReg; decide)]
    unfold js_afterCmp flag
    rw [hlhs, hrhs]
  refine ⟨js_afterCmp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustCompareProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterCmp hcmp_run]
  · rfl
  · change
      (if JoltISA.amoWordSelectMaskVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectMaskVReg) = jolt_sltu_value x y
    rw [if_pos rfl]
  · change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold]
  · change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  · change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectMaskVReg then flag
        else js.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hshift]

/-- The word-select tail turns the comparison flag into the selected new value
while preserving the prelude registers needed by the postlude. -/
theorem amo_word_rust_select_tail_phase_run
    (rs2 : regidx) (js : SailJoltState)
    (rs2Val old flag dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs JoltISA.amoWordSelectOldVReg = old)
    (hflag : js.vregs JoltISA.amoWordSelectMaskVReg = flag)
    (hdword : js.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterTail : SailJoltState,
      AmoWordSelectRustTailStep rs2 old dword shift
        ((rs2Val - old) * flag + old) js js_afterTail := by
  let delta : BitVec 64 := rs2Val - old
  let scaled : BitVec 64 := delta * flag
  let js_afterSub : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectNewVReg then delta else js.vregs r }
  let js_afterMul : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectNewVReg then scaled else js_afterSub.vregs r }
  let js_afterAdd : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSelectNewVReg then scaled + old else js_afterMul.vregs r }
  have hsub_new : js_afterSub.vregs JoltISA.amoWordSelectNewVReg = delta := by
    change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectNewVReg then delta
        else js.vregs JoltISA.amoWordSelectNewVReg) = delta
    rw [if_pos rfl]
  have hsub_flag : js_afterSub.vregs JoltISA.amoWordSelectMaskVReg = flag := by
    change
      (if JoltISA.amoWordSelectMaskVReg = JoltISA.amoWordSelectNewVReg then delta
        else js.vregs JoltISA.amoWordSelectMaskVReg) = flag
    rw [if_neg (by decide), hflag]
  have hsub_old : js_afterSub.vregs JoltISA.amoWordSelectOldVReg = old := by
    change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectNewVReg then delta
        else js.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hold]
  have hsub_dword : js_afterSub.vregs JoltISA.amoWordSelectDwordVReg = dword := by
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectNewVReg then delta
        else js.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hdword]
  have hsub_shift : js_afterSub.vregs JoltISA.amoWordSelectShiftVReg = shift := by
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectNewVReg then delta
        else js.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hshift]
  have hsub_run :
      (JoltISA.execInstr
        (.SUB (.vreg JoltISA.amoWordSelectNewVReg)
          (.xreg rs2) (.vreg JoltISA.amoWordSelectOldVReg))).run js =
        .ok RETIRE_SUCCESS js_afterSub := by
    rw [JoltISA.sub_run_vreg_xreg_vreg
      JoltISA.amoWordSelectNewVReg rs2 JoltISA.amoWordSelectOldVReg js rs2Val hrs2
      (by unfold WritableVReg; decide)]
    unfold js_afterSub delta
    rw [hold]
  have hmul_new : js_afterMul.vregs JoltISA.amoWordSelectNewVReg = scaled := by
    change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectNewVReg then scaled
        else js_afterSub.vregs JoltISA.amoWordSelectNewVReg) = scaled
    rw [if_pos rfl]
  have hmul_old : js_afterMul.vregs JoltISA.amoWordSelectOldVReg = old := by
    change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectNewVReg then scaled
        else js_afterSub.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hsub_old]
  have hmul_dword : js_afterMul.vregs JoltISA.amoWordSelectDwordVReg = dword := by
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectNewVReg then scaled
        else js_afterSub.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hsub_dword]
  have hmul_shift : js_afterMul.vregs JoltISA.amoWordSelectShiftVReg = shift := by
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectNewVReg then scaled
        else js_afterSub.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hsub_shift]
  have hmul_run :
      (JoltISA.execInstr
        (.MUL (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectMaskVReg))).run js_afterSub =
        .ok RETIRE_SUCCESS js_afterMul := by
    rw [JoltISA.mul_run_vreg_vreg_vreg
      JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectMaskVReg
      js_afterSub (by unfold WritableVReg; decide)]
    unfold js_afterMul scaled
    rw [hsub_new, hsub_flag]
  have hadd_result :
      js_afterAdd.vregs JoltISA.amoWordSelectNewVReg =
        (rs2Val - old) * flag + old := by
    change
      (if JoltISA.amoWordSelectNewVReg = JoltISA.amoWordSelectNewVReg then scaled + old
        else js_afterMul.vregs JoltISA.amoWordSelectNewVReg) =
      (rs2Val - old) * flag + old
    rw [if_pos rfl]
  have hadd_old : js_afterAdd.vregs JoltISA.amoWordSelectOldVReg = old := by
    change
      (if JoltISA.amoWordSelectOldVReg = JoltISA.amoWordSelectNewVReg then scaled + old
        else js_afterMul.vregs JoltISA.amoWordSelectOldVReg) = old
    rw [if_neg (by decide), hmul_old]
  have hadd_dword : js_afterAdd.vregs JoltISA.amoWordSelectDwordVReg = dword := by
    change
      (if JoltISA.amoWordSelectDwordVReg = JoltISA.amoWordSelectNewVReg then scaled + old
        else js_afterMul.vregs JoltISA.amoWordSelectDwordVReg) = dword
    rw [if_neg (by decide), hmul_dword]
  have hadd_shift : js_afterAdd.vregs JoltISA.amoWordSelectShiftVReg = shift := by
    change
      (if JoltISA.amoWordSelectShiftVReg = JoltISA.amoWordSelectNewVReg then scaled + old
        else js_afterMul.vregs JoltISA.amoWordSelectShiftVReg) = shift
    rw [if_neg (by decide), hmul_shift]
  have hadd_run :
      (JoltISA.execInstr
        (.ADD (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectOldVReg))).run js_afterMul =
        .ok RETIRE_SUCCESS js_afterAdd := by
    rw [JoltISA.add_run_vreg_vreg_vreg
      JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectOldVReg
      js_afterMul (by unfold WritableVReg; decide)]
    unfold js_afterAdd
    rw [hmul_new, hmul_old]
  refine ⟨js_afterAdd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustTailProgram
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSub hsub_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterSub js_afterMul hmul_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterMul js_afterAdd hadd_run]
  · rfl
  · exact hadd_result
  · exact hadd_old
  · exact hadd_dword
  · exact hadd_shift
theorem amo_word_rust_select_middle_phase_run
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (js : SailJoltState)
    (rs2Val old dword shift rs2Ext oldExt flag result : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hext :
      ∃ js_afterExt : SailJoltState,
        AmoWordSelectRustExtendStep extend rs2 old dword shift rs2Ext oldExt
          js js_afterExt)
    (hcompare :
      ∀ js_afterExt : SailJoltState,
        AmoWordSelectRustExtendStep extend rs2 old dword shift rs2Ext oldExt
          js js_afterExt →
        ∃ js_afterCmp : SailJoltState,
          AmoWordSelectRustCompareStep cmpInstr cmpLhs cmpRhs old dword shift
            flag js_afterExt js_afterCmp)
    (hresult : (rs2Val - old) * flag + old = result) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStep extend cmpInstr cmpLhs cmpRhs rs2
        old dword shift result js js_afterMiddle := by
  obtain ⟨js_afterExt, hext_step⟩ := hext
  obtain ⟨js_afterCmp, hcmp_step⟩ := hcompare js_afterExt hext_step
  have hrs2_afterCmp :
      rX_bits rs2 js_afterCmp.sail = .ok rs2Val js_afterCmp.sail := by
    rw [hcmp_step.sail, hext_step.sail]
    exact hrs2
  obtain ⟨js_afterTail, htail_step⟩ :=
    amo_word_rust_select_tail_phase_run rs2 js_afterCmp rs2Val old flag dword shift
      hrs2_afterCmp hcmp_step.old_vreg hcmp_step.flag_vreg
      hcmp_step.dword_vreg hcmp_step.shift_vreg
  refine ⟨js_afterTail, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustMiddleProgram
    rw [hext_step.run
      (amoWordSelectRustCompareProgram cmpInstr cmpLhs cmpRhs
        (amoWordSelectRustTailProgram rs2 tail))]
    rw [hcmp_step.run (amoWordSelectRustTailProgram rs2 tail)]
    rw [htail_step.run tail]
  · rw [htail_step.sail, hcmp_step.sail, hext_step.sail]
  · rw [htail_step.result_vreg, hresult]
  · exact htail_step.old_vreg
  · exact htail_step.dword_vreg
  · exact htail_step.shift_vreg

/-- Selected-register signed extension phase for word-select AMOs. -/
theorem amo_word_rust_select_signed_extend_phase_run_for
    (rd rs2 : regidx) (js : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old)
    (hdword : js.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (hshift : js.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift) :
    ∃ js_afterExt : SailJoltState,
      AmoWordSelectRustExtendStepFor rd
        (fun dst src => .VirtualSignExtendWord dst src) rs2
        old dword shift
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
        js js_afterExt := by
  let newReg := JoltISA.amoWordSelectNewVRegFor rd
  let maskReg := JoltISA.amoWordSelectMaskVRegFor rd
  let oldReg := JoltISA.amoWordSelectOldVRegFor rd
  let dwordReg := JoltISA.amoWordSelectDwordVRegFor rd
  let shiftReg := JoltISA.amoWordSelectShiftVRegFor rd
  let rs2Ext : BitVec 64 :=
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
  let oldExt : BitVec 64 :=
    sign_extend (m := 64)
      (Sail.BitVec.extractLsb old 31 0 : BitVec 32)
  have hnew_w : WritableVReg newReg := by
    unfold newReg JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hmask_w : WritableVReg maskReg := by
    unfold maskReg JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hnew_ne_mask : newReg ≠ maskReg := by
    unfold newReg maskReg JoltISA.amoWordSelectNewVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_new : oldReg ≠ newReg := by
    unfold oldReg newReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_mask : oldReg ≠ maskReg := by
    unfold oldReg maskReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_new : dwordReg ≠ newReg := by
    unfold dwordReg newReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_mask : dwordReg ≠ maskReg := by
    unfold dwordReg maskReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hshift_ne_new : shiftReg ≠ newReg := by
    unfold shiftReg newReg JoltISA.amoWordSelectShiftVRegFor
      JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hshift_ne_mask : shiftReg ≠ maskReg := by
    unfold shiftReg maskReg JoltISA.amoWordSelectShiftVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  let js_afterRs2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = newReg then rs2Ext else js.vregs r }
  let js_afterExt : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = maskReg then oldExt else js_afterRs2.vregs r }
  have hrs2_run :
      (JoltISA.execInstr
        (.VirtualSignExtendWord (.vreg newReg) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterRs2 := by
    exact
      JoltISA.virtual_sign_extend_word_run_vreg_xreg
        newReg rs2 js rs2Val hrs2 hnew_w
  have hold_afterRs2 : js_afterRs2.vregs oldReg = old := by
    change (if oldReg = newReg then rs2Ext else js.vregs oldReg) = old
    rw [if_neg hold_ne_new, hold]
  have hold_run :
      (JoltISA.execInstr
        (.VirtualSignExtendWord (.vreg maskReg) (.vreg oldReg))).run
          js_afterRs2 =
        .ok RETIRE_SUCCESS js_afterExt := by
    rw [JoltISA.virtual_sign_extend_word_run_vreg_vreg
      maskReg oldReg js_afterRs2 hmask_w]
    unfold js_afterExt oldExt
    rw [hold_afterRs2]
  refine ⟨js_afterExt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustExtendProgramFor
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterRs2 hrs2_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterRs2 js_afterExt hold_run]
  · rfl
  · change (if newReg = maskReg then oldExt else js_afterRs2.vregs newReg) =
      rs2Ext
    rw [if_neg hnew_ne_mask]
    change (if newReg = newReg then rs2Ext else js.vregs newReg) = rs2Ext
    rw [if_pos rfl]
  · change (if maskReg = maskReg then oldExt else js_afterRs2.vregs maskReg) =
      oldExt
    rw [if_pos rfl]
  · change (if oldReg = maskReg then oldExt else js_afterRs2.vregs oldReg) =
      old
    rw [if_neg hold_ne_mask, hold_afterRs2]
  · change (if dwordReg = maskReg then oldExt else js_afterRs2.vregs dwordReg) =
      dword
    rw [if_neg hdword_ne_mask]
    change (if dwordReg = newReg then rs2Ext else js.vregs dwordReg) = dword
    rw [if_neg hdword_ne_new, hdword]
  · change (if shiftReg = maskReg then oldExt else js_afterRs2.vregs shiftReg) =
      shift
    rw [if_neg hshift_ne_mask]
    change (if shiftReg = newReg then rs2Ext else js.vregs shiftReg) = shift
    rw [if_neg hshift_ne_new, hshift]

/-- Selected-register unsigned extension phase for word-select AMOs. -/
theorem amo_word_rust_select_unsigned_extend_phase_run_for
    (rd rs2 : regidx) (js : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old)
    (hdword : js.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (hshift : js.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift) :
    ∃ js_afterExt : SailJoltState,
      AmoWordSelectRustExtendStepFor rd
        (fun dst src => .VirtualZeroExtendWord dst src) rs2
        old dword shift
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
        js js_afterExt := by
  let newReg := JoltISA.amoWordSelectNewVRegFor rd
  let maskReg := JoltISA.amoWordSelectMaskVRegFor rd
  let oldReg := JoltISA.amoWordSelectOldVRegFor rd
  let dwordReg := JoltISA.amoWordSelectDwordVRegFor rd
  let shiftReg := JoltISA.amoWordSelectShiftVRegFor rd
  let rs2Ext : BitVec 64 :=
    zero_extend (m := 64)
      (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
  let oldExt : BitVec 64 :=
    zero_extend (m := 64)
      (Sail.BitVec.extractLsb old 31 0 : BitVec 32)
  have hnew_w : WritableVReg newReg := by
    unfold newReg JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hmask_w : WritableVReg maskReg := by
    unfold maskReg JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hnew_ne_mask : newReg ≠ maskReg := by
    unfold newReg maskReg JoltISA.amoWordSelectNewVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_new : oldReg ≠ newReg := by
    unfold oldReg newReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_mask : oldReg ≠ maskReg := by
    unfold oldReg maskReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_new : dwordReg ≠ newReg := by
    unfold dwordReg newReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_mask : dwordReg ≠ maskReg := by
    unfold dwordReg maskReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hshift_ne_new : shiftReg ≠ newReg := by
    unfold shiftReg newReg JoltISA.amoWordSelectShiftVRegFor
      JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hshift_ne_mask : shiftReg ≠ maskReg := by
    unfold shiftReg maskReg JoltISA.amoWordSelectShiftVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  let js_afterRs2 : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = newReg then rs2Ext else js.vregs r }
  let js_afterExt : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = maskReg then oldExt else js_afterRs2.vregs r }
  have hrs2_run :
      (JoltISA.execInstr
        (.VirtualZeroExtendWord (.vreg newReg) (.xreg rs2))).run js =
        .ok RETIRE_SUCCESS js_afterRs2 := by
    exact
      JoltISA.virtual_zero_extend_word_run_vreg_xreg
        newReg rs2 js rs2Val hrs2 hnew_w
  have hold_afterRs2 : js_afterRs2.vregs oldReg = old := by
    change (if oldReg = newReg then rs2Ext else js.vregs oldReg) = old
    rw [if_neg hold_ne_new, hold]
  have hold_run :
      (JoltISA.execInstr
        (.VirtualZeroExtendWord (.vreg maskReg) (.vreg oldReg))).run
          js_afterRs2 =
        .ok RETIRE_SUCCESS js_afterExt := by
    rw [amo_word_virtual_zero_extend_word_run_vreg_vreg
      maskReg oldReg js_afterRs2 hmask_w]
    unfold js_afterExt oldExt
    rw [hold_afterRs2]
  refine ⟨js_afterExt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustExtendProgramFor
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterRs2 hrs2_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterRs2 js_afterExt hold_run]
  · rfl
  · change (if newReg = maskReg then oldExt else js_afterRs2.vregs newReg) =
      rs2Ext
    rw [if_neg hnew_ne_mask]
    change (if newReg = newReg then rs2Ext else js.vregs newReg) = rs2Ext
    rw [if_pos rfl]
  · change (if maskReg = maskReg then oldExt else js_afterRs2.vregs maskReg) =
      oldExt
    rw [if_pos rfl]
  · change (if oldReg = maskReg then oldExt else js_afterRs2.vregs oldReg) =
      old
    rw [if_neg hold_ne_mask, hold_afterRs2]
  · change (if dwordReg = maskReg then oldExt else js_afterRs2.vregs dwordReg) =
      dword
    rw [if_neg hdword_ne_mask]
    change (if dwordReg = newReg then rs2Ext else js.vregs dwordReg) = dword
    rw [if_neg hdword_ne_new, hdword]
  · change (if shiftReg = maskReg then oldExt else js_afterRs2.vregs shiftReg) =
      shift
    rw [if_neg hshift_ne_mask]
    change (if shiftReg = newReg then rs2Ext else js.vregs shiftReg) = shift
    rw [if_neg hshift_ne_new, hshift]

/-- Selected-register signed comparison phase for word-select AMOs. -/
theorem amo_word_rust_select_slt_compare_phase_run_vreg_vreg_for
    (rd : regidx) (lhs rhs : JoltISA.VReg) (js : SailJoltState)
    (x y old dword shift : BitVec 64)
    (hlhs : js.vregs lhs = x)
    (hrhs : js.vregs rhs = y)
    (hold : js.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old)
    (hdword : js.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (hshift : js.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift) :
    ∃ js_afterCmp : SailJoltState,
      AmoWordSelectRustCompareStepFor rd
        (fun dst lhs rhs => .SLT dst lhs rhs) (.vreg lhs) (.vreg rhs)
        old dword shift
        (zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y)))
        js js_afterCmp := by
  let maskReg := JoltISA.amoWordSelectMaskVRegFor rd
  let oldReg := JoltISA.amoWordSelectOldVRegFor rd
  let dwordReg := JoltISA.amoWordSelectDwordVRegFor rd
  let shiftReg := JoltISA.amoWordSelectShiftVRegFor rd
  let flag : BitVec 64 :=
    zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y))
  let js_afterCmp : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = maskReg then flag else js.vregs r }
  have hmask_w : WritableVReg maskReg := by
    unfold maskReg JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hold_ne_mask : oldReg ≠ maskReg := by
    unfold oldReg maskReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_mask : dwordReg ≠ maskReg := by
    unfold dwordReg maskReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hshift_ne_mask : shiftReg ≠ maskReg := by
    unfold shiftReg maskReg JoltISA.amoWordSelectShiftVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hcmp_run :
      (JoltISA.execInstr
        (.SLT (.vreg maskReg) (.vreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS js_afterCmp := by
    rw [amo_word_slt_run_vreg_vreg_vreg maskReg lhs rhs js hmask_w]
    unfold js_afterCmp flag
    rw [hlhs, hrhs]
  refine ⟨js_afterCmp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustCompareProgramFor
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterCmp hcmp_run]
  · rfl
  · change (if maskReg = maskReg then flag else js.vregs maskReg) =
      zero_extend (m := 64) (bool_to_bit (zopz0zI_s x y))
    rw [if_pos rfl]
  · change (if oldReg = maskReg then flag else js.vregs oldReg) = old
    rw [if_neg hold_ne_mask, hold]
  · change (if dwordReg = maskReg then flag else js.vregs dwordReg) = dword
    rw [if_neg hdword_ne_mask, hdword]
  · change (if shiftReg = maskReg then flag else js.vregs shiftReg) = shift
    rw [if_neg hshift_ne_mask, hshift]

/-- Selected-register unsigned comparison phase for word-select AMOs. -/
theorem amo_word_rust_select_sltu_compare_phase_run_vreg_vreg_for
    (rd : regidx) (lhs rhs : JoltISA.VReg) (js : SailJoltState)
    (x y old dword shift : BitVec 64)
    (hlhs : js.vregs lhs = x)
    (hrhs : js.vregs rhs = y)
    (hold : js.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old)
    (hdword : js.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (hshift : js.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift) :
    ∃ js_afterCmp : SailJoltState,
      AmoWordSelectRustCompareStepFor rd
        (fun dst lhs rhs => .SLTU dst lhs rhs) (.vreg lhs) (.vreg rhs)
        old dword shift (jolt_sltu_value x y) js js_afterCmp := by
  let maskReg := JoltISA.amoWordSelectMaskVRegFor rd
  let oldReg := JoltISA.amoWordSelectOldVRegFor rd
  let dwordReg := JoltISA.amoWordSelectDwordVRegFor rd
  let shiftReg := JoltISA.amoWordSelectShiftVRegFor rd
  let flag : BitVec 64 := jolt_sltu_value x y
  let js_afterCmp : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = maskReg then flag else js.vregs r }
  have hmask_w : WritableVReg maskReg := by
    unfold maskReg JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hold_ne_mask : oldReg ≠ maskReg := by
    unfold oldReg maskReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_mask : dwordReg ≠ maskReg := by
    unfold dwordReg maskReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hshift_ne_mask : shiftReg ≠ maskReg := by
    unfold shiftReg maskReg JoltISA.amoWordSelectShiftVRegFor
      JoltISA.amoWordSelectMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hcmp_run :
      (JoltISA.execInstr
        (.SLTU (.vreg maskReg) (.vreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS js_afterCmp := by
    rw [amo_word_sltu_run_vreg_vreg_vreg maskReg lhs rhs js hmask_w]
    unfold js_afterCmp flag
    rw [hlhs, hrhs]
  refine ⟨js_afterCmp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustCompareProgramFor
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterCmp hcmp_run]
  · rfl
  · change (if maskReg = maskReg then flag else js.vregs maskReg) =
      jolt_sltu_value x y
    rw [if_pos rfl]
  · change (if oldReg = maskReg then flag else js.vregs oldReg) = old
    rw [if_neg hold_ne_mask, hold]
  · change (if dwordReg = maskReg then flag else js.vregs dwordReg) = dword
    rw [if_neg hdword_ne_mask, hdword]
  · change (if shiftReg = maskReg then flag else js.vregs shiftReg) = shift
    rw [if_neg hshift_ne_mask, hshift]

/-- Selected-register select tail for word-select AMOs. -/
theorem amo_word_rust_select_tail_phase_run_for
    (rd rs2 : regidx) (js : SailJoltState)
    (rs2Val old flag dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hold : js.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old)
    (hflag : js.vregs (JoltISA.amoWordSelectMaskVRegFor rd) = flag)
    (hdword : js.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (hshift : js.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift) :
    ∃ js_afterTail : SailJoltState,
      AmoWordSelectRustTailStepFor rd rs2 old dword shift
        ((rs2Val - old) * flag + old) js js_afterTail := by
  let newReg := JoltISA.amoWordSelectNewVRegFor rd
  let maskReg := JoltISA.amoWordSelectMaskVRegFor rd
  let oldReg := JoltISA.amoWordSelectOldVRegFor rd
  let dwordReg := JoltISA.amoWordSelectDwordVRegFor rd
  let shiftReg := JoltISA.amoWordSelectShiftVRegFor rd
  let delta : BitVec 64 := rs2Val - old
  let scaled : BitVec 64 := delta * flag
  let js_afterSub : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = newReg then delta else js.vregs r }
  let js_afterMul : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = newReg then scaled else js_afterSub.vregs r }
  let js_afterAdd : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = newReg then scaled + old else js_afterMul.vregs r }
  have hnew_w : WritableVReg newReg := by
    unfold newReg JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hmask_ne_new : maskReg ≠ newReg := by
    unfold maskReg newReg JoltISA.amoWordSelectMaskVRegFor
      JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_new : oldReg ≠ newReg := by
    unfold oldReg newReg JoltISA.amoWordSelectOldVRegFor
      JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_new : dwordReg ≠ newReg := by
    unfold dwordReg newReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hshift_ne_new : shiftReg ≠ newReg := by
    unfold shiftReg newReg JoltISA.amoWordSelectShiftVRegFor
      JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hsub_new : js_afterSub.vregs newReg = delta := by
    change (if newReg = newReg then delta else js.vregs newReg) = delta
    rw [if_pos rfl]
  have hsub_flag : js_afterSub.vregs maskReg = flag := by
    change (if maskReg = newReg then delta else js.vregs maskReg) = flag
    rw [if_neg hmask_ne_new, hflag]
  have hsub_old : js_afterSub.vregs oldReg = old := by
    change (if oldReg = newReg then delta else js.vregs oldReg) = old
    rw [if_neg hold_ne_new, hold]
  have hsub_dword : js_afterSub.vregs dwordReg = dword := by
    change (if dwordReg = newReg then delta else js.vregs dwordReg) = dword
    rw [if_neg hdword_ne_new, hdword]
  have hsub_shift : js_afterSub.vregs shiftReg = shift := by
    change (if shiftReg = newReg then delta else js.vregs shiftReg) = shift
    rw [if_neg hshift_ne_new, hshift]
  have hsub_run :
      (JoltISA.execInstr
        (.SUB (.vreg newReg) (.xreg rs2) (.vreg oldReg))).run js =
        .ok RETIRE_SUCCESS js_afterSub := by
    rw [JoltISA.sub_run_vreg_xreg_vreg newReg rs2 oldReg js rs2Val hrs2
      hnew_w]
    unfold js_afterSub delta
    rw [hold]
  have hmul_new : js_afterMul.vregs newReg = scaled := by
    change (if newReg = newReg then scaled else js_afterSub.vregs newReg) =
      scaled
    rw [if_pos rfl]
  have hmul_old : js_afterMul.vregs oldReg = old := by
    change (if oldReg = newReg then scaled else js_afterSub.vregs oldReg) =
      old
    rw [if_neg hold_ne_new, hsub_old]
  have hmul_dword : js_afterMul.vregs dwordReg = dword := by
    change (if dwordReg = newReg then scaled else js_afterSub.vregs dwordReg) =
      dword
    rw [if_neg hdword_ne_new, hsub_dword]
  have hmul_shift : js_afterMul.vregs shiftReg = shift := by
    change (if shiftReg = newReg then scaled else js_afterSub.vregs shiftReg) =
      shift
    rw [if_neg hshift_ne_new, hsub_shift]
  have hmul_run :
      (JoltISA.execInstr
        (.MUL (.vreg newReg) (.vreg newReg) (.vreg maskReg))).run js_afterSub =
        .ok RETIRE_SUCCESS js_afterMul := by
    rw [JoltISA.mul_run_vreg_vreg_vreg newReg newReg maskReg js_afterSub
      hnew_w]
    unfold js_afterMul scaled
    rw [hsub_new, hsub_flag]
  have hadd_result :
      js_afterAdd.vregs newReg = (rs2Val - old) * flag + old := by
    change (if newReg = newReg then scaled + old else js_afterMul.vregs newReg) =
      (rs2Val - old) * flag + old
    rw [if_pos rfl]
  have hadd_old : js_afterAdd.vregs oldReg = old := by
    change (if oldReg = newReg then scaled + old else js_afterMul.vregs oldReg) =
      old
    rw [if_neg hold_ne_new, hmul_old]
  have hadd_dword : js_afterAdd.vregs dwordReg = dword := by
    change
      (if dwordReg = newReg then scaled + old else js_afterMul.vregs dwordReg) =
        dword
    rw [if_neg hdword_ne_new, hmul_dword]
  have hadd_shift : js_afterAdd.vregs shiftReg = shift := by
    change
      (if shiftReg = newReg then scaled + old else js_afterMul.vregs shiftReg) =
        shift
    rw [if_neg hshift_ne_new, hmul_shift]
  have hadd_run :
      (JoltISA.execInstr
        (.ADD (.vreg newReg) (.vreg newReg) (.vreg oldReg))).run js_afterMul =
        .ok RETIRE_SUCCESS js_afterAdd := by
    rw [JoltISA.add_run_vreg_vreg_vreg newReg newReg oldReg js_afterMul hnew_w]
    unfold js_afterAdd
    rw [hmul_new, hmul_old]
  refine ⟨js_afterAdd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustTailProgramFor
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_afterSub hsub_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterSub js_afterMul hmul_run]
    rw [JoltISA.execProgram_instr_run_retire
      _ _ js_afterMul js_afterAdd hadd_run]
  · rfl
  · exact hadd_result
  · exact hadd_old
  · exact hadd_dword
  · exact hadd_shift

theorem amo_word_rust_select_middle_phase_run_for
    (rd : regidx)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src) (rs2 : regidx)
    (js : SailJoltState)
    (rs2Val old dword shift rs2Ext oldExt flag result : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hext :
      ∃ js_afterExt : SailJoltState,
        AmoWordSelectRustExtendStepFor rd extend rs2 old dword shift rs2Ext
          oldExt js js_afterExt)
    (hcompare :
      ∀ js_afterExt : SailJoltState,
        AmoWordSelectRustExtendStepFor rd extend rs2 old dword shift rs2Ext
          oldExt js js_afterExt →
        ∃ js_afterCmp : SailJoltState,
          AmoWordSelectRustCompareStepFor rd cmpInstr cmpLhs cmpRhs old dword
            shift flag js_afterExt js_afterCmp)
    (hresult : (rs2Val - old) * flag + old = result) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStepFor rd extend cmpInstr cmpLhs cmpRhs rs2
        old dword shift result js js_afterMiddle := by
  obtain ⟨js_afterExt, hext_step⟩ := hext
  obtain ⟨js_afterCmp, hcmp_step⟩ := hcompare js_afterExt hext_step
  have hrs2_afterCmp :
      rX_bits rs2 js_afterCmp.sail = .ok rs2Val js_afterCmp.sail := by
    rw [hcmp_step.sail, hext_step.sail]
    exact hrs2
  obtain ⟨js_afterTail, htail_step⟩ :=
    amo_word_rust_select_tail_phase_run_for rd rs2 js_afterCmp rs2Val old flag
      dword shift hrs2_afterCmp hcmp_step.old_vreg hcmp_step.flag_vreg
      hcmp_step.dword_vreg hcmp_step.shift_vreg
  refine ⟨js_afterTail, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tail
    unfold amoWordSelectRustMiddleProgramFor
    rw [hext_step.run
      (amoWordSelectRustCompareProgramFor rd cmpInstr cmpLhs cmpRhs
        (amoWordSelectRustTailProgramFor rd rs2 tail))]
    rw [hcmp_step.run (amoWordSelectRustTailProgramFor rd rs2 tail)]
    rw [htail_step.run tail]
  · rw [htail_step.sail, hcmp_step.sail, hext_step.sail]
  · rw [htail_step.result_vreg, hresult]
  · exact htail_step.old_vreg
  · exact htail_step.dword_vreg
  · exact htail_step.shift_vreg

/-- `AMOMIN.W`'s select middle chooses the full `rs2` scratch value exactly
when the low words satisfy signed `<`. -/
theorem amo_word_rust_select_min_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js_pre.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStep
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg) rs2
        old dword shift
        (if (zopz0zI_s
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_rust_select_middle_phase_run
      (fun dst src => .VirtualSignExtendWord dst src)
      (fun dst lhs rhs => .SLT dst lhs rhs)
      (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg) rs2
      js_pre rs2Val old dword shift
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (bool_to_bit
          (zopz0zI_s
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb old 31 0 : BitVec 32)))))
      (if (zopz0zI_s
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_rust_select_signed_extend_phase_run rs2 js_pre rs2Val old dword
        shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_rust_select_slt_compare_phase_run_vreg_vreg
          JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectMaskVReg js_afterExt
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          old dword shift hext_step.rs2_ext_vreg hext_step.old_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_slt_sext old rs2Val)

/-- `AMOMAX.W`'s select middle chooses the full `rs2` scratch value exactly
when the low words satisfy signed `>`. -/
theorem amo_word_rust_select_max_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js_pre.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStep
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg JoltISA.amoWordSelectNewVReg) rs2
        old dword shift
        (if (zopz0zK_s
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_rust_select_middle_phase_run
      (fun dst src => .VirtualSignExtendWord dst src)
      (fun dst lhs rhs => .SLT dst lhs rhs)
      (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg JoltISA.amoWordSelectNewVReg) rs2
      js_pre rs2Val old dword shift
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (bool_to_bit
          (zopz0zI_s
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)))))
      (if (zopz0zK_s
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_rust_select_signed_extend_phase_run rs2 js_pre rs2Val old dword
        shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_rust_select_slt_compare_phase_run_vreg_vreg
          JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectNewVReg js_afterExt
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          old dword shift hext_step.old_ext_vreg hext_step.rs2_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_sgt_sext old rs2Val)

/-- `AMOMINU.W`'s select middle chooses the full `rs2` scratch value exactly
when the low words satisfy unsigned `<`. -/
theorem amo_word_rust_select_minu_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js_pre.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStep
        (fun dst src => .VirtualZeroExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg) rs2
        old dword shift
        (if (zopz0zI_u
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_rust_select_middle_phase_run
      (fun dst src => .VirtualZeroExtendWord dst src)
      (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg JoltISA.amoWordSelectNewVReg) (.vreg JoltISA.amoWordSelectMaskVReg) rs2
      js_pre rs2Val old dword shift
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (jolt_sltu_value
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32)))
      (if (zopz0zI_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_rust_select_unsigned_extend_phase_run rs2 js_pre rs2Val old dword
        shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_rust_select_sltu_compare_phase_run_vreg_vreg
          JoltISA.amoWordSelectNewVReg JoltISA.amoWordSelectMaskVReg js_afterExt
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          old dword shift hext_step.rs2_ext_vreg hext_step.old_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_sltu_zext old rs2Val)

/-- `AMOMAXU.W`'s select middle chooses the full `rs2` scratch value exactly
when the low words satisfy unsigned `>`. -/
theorem amo_word_rust_select_maxu_middle_run
    (rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs JoltISA.amoWordSelectOldVReg = old)
    (hdword : js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword)
    (hshift : js_pre.vregs JoltISA.amoWordSelectShiftVReg = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStep
        (fun dst src => .VirtualZeroExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg JoltISA.amoWordSelectNewVReg) rs2
        old dword shift
        (if (zopz0zK_u
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_rust_select_middle_phase_run
      (fun dst src => .VirtualZeroExtendWord dst src)
      (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg JoltISA.amoWordSelectMaskVReg) (.vreg JoltISA.amoWordSelectNewVReg) rs2
      js_pre rs2Val old dword shift
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (jolt_sltu_value
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)))
      (if (zopz0zK_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_rust_select_unsigned_extend_phase_run rs2 js_pre rs2Val old dword
        shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_rust_select_sltu_compare_phase_run_vreg_vreg
          JoltISA.amoWordSelectMaskVReg JoltISA.amoWordSelectNewVReg js_afterExt
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          old dword shift hext_step.old_ext_vreg hext_step.rs2_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_sgtu_zext old rs2Val)

/-- Selected-register version of `amo_word_rust_select_min_middle_run`. -/
theorem amo_word_rust_select_min_middle_run_for
    (rd rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old)
    (hdword : js_pre.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (hshift : js_pre.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStepFor rd
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
        (.vreg (JoltISA.amoWordSelectMaskVRegFor rd)) rs2
        old dword shift
        (if (zopz0zI_s
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_rust_select_middle_phase_run_for rd
      (fun dst src => .VirtualSignExtendWord dst src)
      (fun dst lhs rhs => .SLT dst lhs rhs)
      (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
      (.vreg (JoltISA.amoWordSelectMaskVRegFor rd)) rs2 js_pre rs2Val old
      dword shift
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (bool_to_bit
          (zopz0zI_s
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb old 31 0 : BitVec 32)))))
      (if (zopz0zI_s
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_rust_select_signed_extend_phase_run_for rd rs2 js_pre rs2Val
        old dword shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_rust_select_slt_compare_phase_run_vreg_vreg_for rd
          (JoltISA.amoWordSelectNewVRegFor rd)
          (JoltISA.amoWordSelectMaskVRegFor rd) js_afterExt
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          old dword shift hext_step.rs2_ext_vreg hext_step.old_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_slt_sext old rs2Val)

/-- Selected-register version of `amo_word_rust_select_max_middle_run`. -/
theorem amo_word_rust_select_max_middle_run_for
    (rd rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old)
    (hdword : js_pre.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (hshift : js_pre.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStepFor rd
        (fun dst src => .VirtualSignExtendWord dst src)
        (fun dst lhs rhs => .SLT dst lhs rhs)
        (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
        (.vreg (JoltISA.amoWordSelectNewVRegFor rd)) rs2
        old dword shift
        (if (zopz0zK_s
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_rust_select_middle_phase_run_for rd
      (fun dst src => .VirtualSignExtendWord dst src)
      (fun dst lhs rhs => .SLT dst lhs rhs)
      (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
      (.vreg (JoltISA.amoWordSelectNewVRegFor rd)) rs2 js_pre rs2Val old
      dword shift
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (sign_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (bool_to_bit
          (zopz0zI_s
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
            (sign_extend (m := 64)
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)))))
      (if (zopz0zK_s
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_rust_select_signed_extend_phase_run_for rd rs2 js_pre rs2Val
        old dword shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_rust_select_slt_compare_phase_run_vreg_vreg_for rd
          (JoltISA.amoWordSelectMaskVRegFor rd)
          (JoltISA.amoWordSelectNewVRegFor rd) js_afterExt
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          old dword shift hext_step.old_ext_vreg hext_step.rs2_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_sgt_sext old rs2Val)

/-- Selected-register version of `amo_word_rust_select_minu_middle_run`. -/
theorem amo_word_rust_select_minu_middle_run_for
    (rd rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old)
    (hdword : js_pre.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (hshift : js_pre.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStepFor rd
        (fun dst src => .VirtualZeroExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
        (.vreg (JoltISA.amoWordSelectMaskVRegFor rd)) rs2
        old dword shift
        (if (zopz0zI_u
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_rust_select_middle_phase_run_for rd
      (fun dst src => .VirtualZeroExtendWord dst src)
      (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
      (.vreg (JoltISA.amoWordSelectMaskVRegFor rd)) rs2 js_pre rs2Val old
      dword shift
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (jolt_sltu_value
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32)))
      (if (zopz0zI_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_rust_select_unsigned_extend_phase_run_for rd rs2 js_pre rs2Val
        old dword shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_rust_select_sltu_compare_phase_run_vreg_vreg_for rd
          (JoltISA.amoWordSelectNewVRegFor rd)
          (JoltISA.amoWordSelectMaskVRegFor rd) js_afterExt
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          old dword shift hext_step.rs2_ext_vreg hext_step.old_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_sltu_zext old rs2Val)

/-- Selected-register version of `amo_word_rust_select_maxu_middle_run`. -/
theorem amo_word_rust_select_maxu_middle_run_for
    (rd rs2 : regidx) (js_pre : SailJoltState)
    (rs2Val old dword shift : BitVec 64)
    (hrs2 : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail)
    (hold : js_pre.vregs (JoltISA.amoWordSelectOldVRegFor rd) = old)
    (hdword : js_pre.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword)
    (hshift : js_pre.vregs (JoltISA.amoWordSelectShiftVRegFor rd) = shift) :
    ∃ js_afterMiddle : SailJoltState,
      AmoWordSelectRustMiddleStepFor rd
        (fun dst src => .VirtualZeroExtendWord dst src)
        (fun dst lhs rhs => .SLTU dst lhs rhs)
        (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
        (.vreg (JoltISA.amoWordSelectNewVRegFor rd)) rs2
        old dword shift
        (if (zopz0zK_u
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
          rs2Val
        else
          old)
        js_pre js_afterMiddle := by
  exact
    amo_word_rust_select_middle_phase_run_for rd
      (fun dst src => .VirtualZeroExtendWord dst src)
      (fun dst lhs rhs => .SLTU dst lhs rhs)
      (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
      (.vreg (JoltISA.amoWordSelectNewVRegFor rd)) rs2 js_pre rs2Val old
      dword shift
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
      (zero_extend (m := 64)
        (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
      (jolt_sltu_value
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
        (zero_extend (m := 64)
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)))
      (if (zopz0zK_u
          (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
          (Sail.BitVec.extractLsb old 31 0 : BitVec 32) : Bool) then
        rs2Val
      else
        old)
      hrs2
      (amo_word_rust_select_unsigned_extend_phase_run_for rd rs2 js_pre rs2Val
        old dword shift hrs2 hold hdword hshift)
      (fun js_afterExt hext_step =>
        amo_word_rust_select_sltu_compare_phase_run_vreg_vreg_for rd
          (JoltISA.amoWordSelectMaskVRegFor rd)
          (JoltISA.amoWordSelectNewVRegFor rd) js_afterExt
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb old 31 0 : BitVec 32))
          (zero_extend (m := 64)
            (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32))
          old dword shift hext_step.old_ext_vreg hext_step.rs2_ext_vreg
          hext_step.old_vreg hext_step.dword_vreg hext_step.shift_vreg)
      (amo_word_select_value_of_sgtu_zext old rs2Val)

/-- After the common word prelude, the `AMOMIN.W` middle block is ready for the
shared word-select program helper. -/
theorem amo_word_rust_select_min_middle_after_pre
    (rs2 : regidx) (js : SailJoltState)
    (addr rs2Val dword : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword →
      js_pre.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoWordSelectOldVReg =
        amoWordShiftedOld addr dword →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectRustMiddleStep
          (fun dst src => .VirtualSignExtendWord dst src)
          (fun dst lhs rhs => .SLT dst lhs rhs)
          (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectMaskVReg) rs2
          (amoWordShiftedOld addr dword) dword
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zI_s
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld addr dword)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_rust_select_min_middle_run rs2 js_pre rs2Val
      (amoWordShiftedOld addr dword) dword (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- After the common word prelude, the `AMOMAX.W` middle block is ready for the
shared word-select program helper. -/
theorem amo_word_rust_select_max_middle_after_pre
    (rs2 : regidx) (js : SailJoltState)
    (addr rs2Val dword : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword →
      js_pre.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoWordSelectOldVReg =
        amoWordShiftedOld addr dword →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectRustMiddleStep
          (fun dst src => .VirtualSignExtendWord dst src)
          (fun dst lhs rhs => .SLT dst lhs rhs)
          (.vreg JoltISA.amoWordSelectMaskVReg)
          (.vreg JoltISA.amoWordSelectNewVReg) rs2
          (amoWordShiftedOld addr dword) dword
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zK_s
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld addr dword)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_rust_select_max_middle_run rs2 js_pre rs2Val
      (amoWordShiftedOld addr dword) dword (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- After the common word prelude, the `AMOMINU.W` middle block is ready for
the shared word-select program helper. -/
theorem amo_word_rust_select_minu_middle_after_pre
    (rs2 : regidx) (js : SailJoltState)
    (addr rs2Val dword : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword →
      js_pre.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoWordSelectOldVReg =
        amoWordShiftedOld addr dword →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectRustMiddleStep
          (fun dst src => .VirtualZeroExtendWord dst src)
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg JoltISA.amoWordSelectNewVReg)
          (.vreg JoltISA.amoWordSelectMaskVReg) rs2
          (amoWordShiftedOld addr dword) dword
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zI_u
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld addr dword)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_rust_select_minu_middle_run rs2 js_pre rs2Val
      (amoWordShiftedOld addr dword) dword (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- After the common word prelude, the `AMOMAXU.W` middle block is ready for
the shared word-select program helper. -/
theorem amo_word_rust_select_maxu_middle_after_pre
    (rs2 : regidx) (js : SailJoltState)
    (addr rs2Val dword : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs JoltISA.amoWordSelectDwordVReg = dword →
      js_pre.vregs JoltISA.amoWordSelectShiftVReg =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs JoltISA.amoWordSelectOldVReg =
        amoWordShiftedOld addr dword →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectRustMiddleStep
          (fun dst src => .VirtualZeroExtendWord dst src)
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg JoltISA.amoWordSelectMaskVReg)
          (.vreg JoltISA.amoWordSelectNewVReg) rs2
          (amoWordShiftedOld addr dword) dword
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zK_u
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld addr dword)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_rust_select_maxu_middle_run rs2 js_pre rs2Val
      (amoWordShiftedOld addr dword) dword (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- Selected-register version of `amo_word_rust_select_min_middle_after_pre`. -/
theorem amo_word_rust_select_min_middle_after_pre_for
    (rd rs2 : regidx) (js : SailJoltState)
    (addr rs2Val dword : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword →
      js_pre.vregs (JoltISA.amoWordSelectShiftVRegFor rd) =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs (JoltISA.amoWordSelectOldVRegFor rd) =
        amoWordShiftedOld addr dword →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectRustMiddleStepFor rd
          (fun dst src => .VirtualSignExtendWord dst src)
          (fun dst lhs rhs => .SLT dst lhs rhs)
          (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
          (.vreg (JoltISA.amoWordSelectMaskVRegFor rd)) rs2
          (amoWordShiftedOld addr dword) dword
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zI_s
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld addr dword)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_rust_select_min_middle_run_for rd rs2 js_pre rs2Val
      (amoWordShiftedOld addr dword) dword (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- Selected-register version of `amo_word_rust_select_max_middle_after_pre`. -/
theorem amo_word_rust_select_max_middle_after_pre_for
    (rd rs2 : regidx) (js : SailJoltState)
    (addr rs2Val dword : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword →
      js_pre.vregs (JoltISA.amoWordSelectShiftVRegFor rd) =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs (JoltISA.amoWordSelectOldVRegFor rd) =
        amoWordShiftedOld addr dword →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectRustMiddleStepFor rd
          (fun dst src => .VirtualSignExtendWord dst src)
          (fun dst lhs rhs => .SLT dst lhs rhs)
          (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
          (.vreg (JoltISA.amoWordSelectNewVRegFor rd)) rs2
          (amoWordShiftedOld addr dword) dword
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zK_s
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld addr dword)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_rust_select_max_middle_run_for rd rs2 js_pre rs2Val
      (amoWordShiftedOld addr dword) dword (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- Selected-register version of `amo_word_rust_select_minu_middle_after_pre`. -/
theorem amo_word_rust_select_minu_middle_after_pre_for
    (rd rs2 : regidx) (js : SailJoltState)
    (addr rs2Val dword : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword →
      js_pre.vregs (JoltISA.amoWordSelectShiftVRegFor rd) =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs (JoltISA.amoWordSelectOldVRegFor rd) =
        amoWordShiftedOld addr dword →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectRustMiddleStepFor rd
          (fun dst src => .VirtualZeroExtendWord dst src)
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg (JoltISA.amoWordSelectNewVRegFor rd))
          (.vreg (JoltISA.amoWordSelectMaskVRegFor rd)) rs2
          (amoWordShiftedOld addr dword) dword
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zI_u
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld addr dword)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_rust_select_minu_middle_run_for rd rs2 js_pre rs2Val
      (amoWordShiftedOld addr dword) dword (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

/-- Selected-register version of `amo_word_rust_select_maxu_middle_after_pre`. -/
theorem amo_word_rust_select_maxu_middle_after_pre_for
    (rd rs2 : regidx) (js : SailJoltState)
    (addr rs2Val dword : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail) :
    ∀ js_pre : SailJoltState,
      js_pre.sail = js.sail →
      js_pre.vregs (JoltISA.amoWordSelectDwordVRegFor rd) = dword →
      js_pre.vregs (JoltISA.amoWordSelectShiftVRegFor rd) =
        shift_bits_left addr (3 : BitVec 6) →
      js_pre.vregs (JoltISA.amoWordSelectOldVRegFor rd) =
        amoWordShiftedOld addr dword →
      ∃ js_afterMiddle : SailJoltState,
        AmoWordSelectRustMiddleStepFor rd
          (fun dst src => .VirtualZeroExtendWord dst src)
          (fun dst lhs rhs => .SLTU dst lhs rhs)
          (.vreg (JoltISA.amoWordSelectMaskVRegFor rd))
          (.vreg (JoltISA.amoWordSelectNewVRegFor rd)) rs2
          (amoWordShiftedOld addr dword) dword
          (shift_bits_left addr (3 : BitVec 6))
          (if (zopz0zK_u
              (Sail.BitVec.extractLsb rs2Val 31 0 : BitVec 32)
              (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
                BitVec 32) : Bool) then
            rs2Val
          else
            amoWordShiftedOld addr dword)
          js_pre js_afterMiddle := by
  intro js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hrs2_pre : rX_bits rs2 js_pre.sail = .ok rs2Val js_pre.sail := by
    rw [hpre_sail]
    exact hrs2
  exact
    amo_word_rust_select_maxu_middle_run_for rd rs2 js_pre rs2Val
      (amoWordShiftedOld addr dword) dword (shift_bits_left addr (3 : BitVec 6))
      hrs2_pre hpre_old hpre_dword hpre_shift

theorem amo_word_rust_select_program_concrete_aligned
    (op : amoop)
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (addr result64 : BitVec 64) (result oldWord : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
    (hload_pmp : Assumptions.LoadPmpOk (amoWordBase addr) 8 js.sail)
    (hread_mmio : Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail)
    (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail)
    (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hresult : (Sail.BitVec.extractLsb result64 31 0 : BitVec 32) = result)
    (hold :
      (Sail.BitVec.extractLsb
        (amoWordShiftedOld addr
          (loaded_dword_at js.sail (amoWordBase addr) hbytes_base
            ((amo_word_base_no_ovf addr) :
              (amoWordBase addr).toNat + 7 < 2 ^ 64)))
        31 0 : BitVec 32) = oldWord)
    (hmiddle :
      ∀ js_pre : SailJoltState,
        js_pre.sail = js.sail →
        js_pre.vregs (JoltISA.amoWordSelectDwordVRegFor rd) =
          loaded_dword_at js.sail (amoWordBase addr) hbytes_base
            ((amo_word_base_no_ovf addr) :
              (amoWordBase addr).toNat + 7 < 2 ^ 64) →
        js_pre.vregs (JoltISA.amoWordSelectShiftVRegFor rd) =
          shift_bits_left addr (3 : BitVec 6) →
        js_pre.vregs (JoltISA.amoWordSelectOldVRegFor rd) =
          amoWordShiftedOld addr
            (loaded_dword_at js.sail (amoWordBase addr) hbytes_base
              ((amo_word_base_no_ovf addr) :
                (amoWordBase addr).toNat + 7 < 2 ^ 64)) →
        ∃ js_afterMiddle : SailJoltState,
          AmoWordSelectRustMiddleStepFor rd extend cmpInstr cmpLhs cmpRhs rs2
            (amoWordShiftedOld addr
              (loaded_dword_at js.sail (amoWordBase addr) hbytes_base
                ((amo_word_base_no_ovf addr) :
                  (amoWordBase addr).toNat + 7 < 2 ^ 64)))
            (loaded_dword_at js.sail (amoWordBase addr) hbytes_base
              ((amo_word_base_no_ovf addr) :
                (amoWordBase addr).toNat + 7 < 2 ^ 64))
            (shift_bits_left addr (3 : BitVec 6))
            result64 js_pre js_afterMiddle) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoWordSelectRustProgram extend cmpInstr cmpLhs cmpRhs
          rs2 rs1 rd)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail = amoWordFinalSailState rd js.sail addr result oldWord := by
  let oldReg := JoltISA.amoWordSelectOldVRegFor rd
  let dwordReg := JoltISA.amoWordSelectDwordVRegFor rd
  let shiftReg := JoltISA.amoWordSelectShiftVRegFor rd
  let newReg := JoltISA.amoWordSelectNewVRegFor rd
  let maskReg := JoltISA.amoWordSelectMaskVRegFor rd
  let tmpReg := JoltISA.amoWordSelectInlineTmpVRegFor rd
  let post : JoltISA.Program :=
    amoWordSelectRustMiddleProgramFor rd extend cmpInstr cmpLhs cmpRhs rs2
      (JoltISA.amoPost64ProgramWithScratch rs1 rd (.vreg newReg)
        dwordReg shiftReg maskReg oldReg tmpReg)
  have h_no_ovf := amo_word_base_no_ovf addr
  let dword : BitVec 64 :=
    loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf
  let old : BitVec 64 := amoWordShiftedOld addr dword
  have hshift_w : WritableVReg shiftReg := by
    unfold shiftReg JoltISA.amoWordSelectShiftVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hdword_w : WritableVReg dwordReg := by
    unfold dwordReg JoltISA.amoWordSelectDwordVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hnew_w : WritableVReg newReg := by
    unfold newReg JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hold_w : WritableVReg oldReg := by
    unfold oldReg JoltISA.amoWordSelectOldVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hshift_ne_dword : shiftReg ≠ dwordReg := by
    unfold shiftReg dwordReg JoltISA.amoWordSelectShiftVRegFor
      JoltISA.amoWordSelectDwordVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_new : dwordReg ≠ newReg := by
    unfold dwordReg newReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hshift_ne_new : shiftReg ≠ newReg := by
    unfold shiftReg newReg JoltISA.amoWordSelectShiftVRegFor
      JoltISA.amoWordSelectNewVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_old : dwordReg ≠ oldReg := by
    unfold dwordReg oldReg JoltISA.amoWordSelectDwordVRegFor
      JoltISA.amoWordSelectOldVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hshift_ne_old : shiftReg ≠ oldReg := by
    unfold shiftReg oldReg JoltISA.amoWordSelectShiftVRegFor
      JoltISA.amoWordSelectOldVRegFor JoltISA.amoVRegFor
    split <;> decide
  obtain ⟨js_pre, hpre_run, hpre_sail, hpre_dword, hpre_shift, hpre_old⟩ :=
    amo_word_pre64_aligned_run_with rs1 oldReg dwordReg shiftReg newReg post
      js hpriv hmprv addr hrs1 hbytes_base hload_pmp hread_mmio h_no_ovf
      h_align hshift_w hdword_w hnew_w hold_w hshift_ne_dword
      hdword_ne_new hshift_ne_new hdword_ne_old hshift_ne_old
  obtain ⟨js_afterMiddle, hmiddle_step⟩ :=
    hmiddle js_pre hpre_sail hpre_dword hpre_shift hpre_old
  have hmiddle_sail : js_afterMiddle.sail = js.sail := by
    rw [hmiddle_step.sail, hpre_sail]
  obtain ⟨jsf, hpost_run, hpost_sail⟩ :=
    amo_word_rust_select_post64_vreg_aligned_run_for rs1 rd
      js js_afterMiddle hpriv hmprv addr result64 dword oldWord hrs1
      hbytes_base hstore_pmp hwrite_mmio h_no_ovf h_align rfl
      hmiddle_sail hmiddle_step.result_vreg
      hmiddle_step.dword_vreg hmiddle_step.shift_vreg hmiddle_step.old_vreg
      (by simpa [dword] using hold)
  refine ⟨jsf, ?_, ?_⟩
  · unfold JoltISA.amoWordSelectRustProgram
    change
      (JoltISA.execProgram
        (JoltISA.amoPre64ProgramWithScratch rs1 oldReg dwordReg shiftReg
          newReg post)).run js =
        .ok RETIRE_SUCCESS jsf
    rw [hpre_run]
    rw [hmiddle_step.run
      (JoltISA.amoPost64ProgramWithScratch rs1 rd (.vreg newReg)
        dwordReg shiftReg maskReg oldReg tmpReg)]
    exact hpost_run
  · rw [hpost_sail, hresult]

/-- Shared misaligned concrete execution for word AMO select expansions. -/
theorem amo_word_rust_select_program_concrete_misaligned
    (extend : JoltISA.Dst → JoltISA.Src → JoltISA.Instr)
    (cmpInstr : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (cmpLhs cmpRhs : JoltISA.Src)
    (rs2 rs1 rd : regidx) (js : SailJoltState) (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_align : addr &&& (3 : BitVec 64) ≠ 0) :
    (JoltISA.execProgram
      (JoltISA.amoWordSelectRustProgram extend cmpInstr cmpLhs cmpRhs
        rs2 rs1 rd)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
  unfold JoltISA.amoWordSelectRustProgram
  unfold JoltISA.amoPre64ProgramWithScratch
  exact amo_word_assert_prefix_misaligned_run rs1 _ js addr hrs1 h_align

end AtomicFamily

end
