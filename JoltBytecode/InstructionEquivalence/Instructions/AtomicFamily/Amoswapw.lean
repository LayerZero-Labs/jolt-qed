import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.WordProgram
import JoltBytecode.JoltISA.ExpansionsAutomated

open LeanRV64D

set_option linter.unusedVariables false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

theorem amoswapwProgram_doesNotWriteProtectedVRegs
    (rs2 rs1 rd : regidx) :
    JoltISA.ProgramWritesNoProtectedVReg
      (JoltISA.amoswapwProgramAuto rd rs1 rs2) := by
  unfold JoltISA.amoswapwProgramAuto
  split <;>
    simp only [JoltISA.ProgramWritesNoProtectedVReg,
      JoltISA.InstrWritesNoProtectedVReg, JoltISA.DstWritesNoProtectedVReg,
      true_and, and_true] <;>
    repeat' apply And.intro
  all_goals exact JoltISA.not_protected_of_instructionTmp rfl


/-- The selected-register swap prelude for `AMOSWAP.W`, with scratch
registers chosen from the destination register. -/
theorem amo_word_swap_pre64_aligned_run_for
    (rd : regidx) (tail : JoltISA.Program) (rs1 : regidx) (js : SailJoltState)
    (addr : BitVec 64) (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hbytes : MemBytesPresentAt js.sail (amoWordBase addr) 8)
    (hread : Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (halign : addr &&& (3 : BitVec 64) = 0)
    (hjolt : Assumptions.JoltRamLoadOk (amoWordBase addr) js) :
    ∃ pre,
      (JoltISA.execProgram (JoltISA.amoPre64Program rs1 (JoltISA.amoWordOldVRegFor rd)
        (JoltISA.amoWordDwordVRegFor rd) (JoltISA.amoWordLaneVRegFor rd) tail)).run js =
        (JoltISA.execProgram tail).run pre ∧
      pre.sail = js.sail ∧
      pre.vregs (JoltISA.amoWordDwordVRegFor rd) =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf ∧
      pre.vregs (JoltISA.amoWordLaneVRegFor rd) = amoWordLaneMask addr ∧
      pre.vregs (JoltISA.amoWordOldVRegFor rd) = amoWordLaneOld addr
        (loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf) ∧
      pre.jolt_device.memory_layout = js.jolt_device.memory_layout :=
  amo_word_pre64_aligned_run_for rd tail rs1 js addr hrs1 hbytes hread h_no_ovf halign hjolt

/-- The first two postlude instructions seed the low-word mask and preserve the
loaded dword, lane shift, and old word. -/
theorem amo_word_swap_mask32_prefix_run
    (js : SailJoltState) (s : SailState) (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_shift : js.vregs JoltISA.amoWordSwapShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSwapDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSwapMaskVReg =
        (0x00000000FFFFFFFF : BitVec 64) ∧
      js'.vregs JoltISA.amoWordSwapShiftVReg = shift64 ∧
      js'.vregs JoltISA.amoWordSwapDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (JoltISA.Encoded.ORI (.vreg JoltISA.amoWordSwapMaskVReg)
            (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
           .instr (.VirtualSRLI (.vreg JoltISA.amoWordSwapMaskVReg)
            (.vreg JoltISA.amoWordSwapMaskVReg)
            (JoltISA.srliBitmask (32 : BitVec 6))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js_ones, _hx0, hones_sail_raw, hones_mask_raw,
      hones_preserves, hones_run⟩ :=
    JoltISA.exists_state_after_ori_run_vreg_xreg_of_sail_eq
      JoltISA.amoWordSwapMaskVReg (regidx.Regidx 0) (-1 : BitVec 12)
      js s (0#64) h_sail (amo_word_read_x0_eq_zero s)
      (by unfold WritableVReg; decide)
  have hones_sail : js_ones.sail = s := by
    rw [hones_sail_raw, h_sail]
  have hones_mask : js_ones.vregs JoltISA.amoWordSwapMaskVReg = (-1 : BitVec 64) := by
    rw [hones_mask_raw]
    exact amo_word_seed_mask_value
  have hones_shift : js_ones.vregs JoltISA.amoWordSwapShiftVReg = shift64 := by
    rw [hones_preserves JoltISA.amoWordSwapShiftVReg (by decide)]
    exact h_shift
  have hones_dword : js_ones.vregs JoltISA.amoWordSwapDwordVReg = dword := by
    rw [hones_preserves JoltISA.amoWordSwapDwordVReg (by decide)]
    exact h_dword
  have hones_old : js_ones.vregs JoltISA.amoWordSwapOldVReg = old := by
    rw [hones_preserves JoltISA.amoWordSwapOldVReg (by decide)]
    exact h_old
  obtain ⟨js_mask, hmask_sail_raw, hmask_raw, hmask_preserves,
      hmask_tail⟩ :=
    JoltISA.exists_state_after_srli_block_run_vreg_vreg
      JoltISA.amoWordSwapMaskVReg JoltISA.amoWordSwapMaskVReg
      (32 : BitVec 6) js_ones (by unfold WritableVReg; decide)
  refine ⟨js_mask, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmask_sail_raw, hones_sail]
  · rw [hmask_raw, hones_mask]
    exact amo_word_low_word_mask_value
  · rw [hmask_preserves JoltISA.amoWordSwapShiftVReg (by decide)]
    exact hones_shift
  · rw [hmask_preserves JoltISA.amoWordSwapDwordVReg (by decide)]
    exact hones_dword
  · rw [hmask_preserves JoltISA.amoWordSwapOldVReg (by decide)]
    exact hones_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_ones hones_run]
    have htail := hmask_tail tail
    unfold JoltISA.srliBlock at htail
    exact htail

/-- Selected-register version of `amo_word_swap_mask32_prefix_run`. -/
theorem amo_word_swap_mask32_prefix_run_for
    (rd : regidx)
    (js : SailJoltState) (s : SailState) (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_shift : js.vregs (JoltISA.amoWordSwapShiftVRegFor rd) = shift64)
    (h_dword : js.vregs (JoltISA.amoWordSwapDwordVRegFor rd) = dword)
    (h_old : js.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs (JoltISA.amoWordSwapMaskVRegFor rd) =
        (0x00000000FFFFFFFF : BitVec 64) ∧
      js'.vregs (JoltISA.amoWordSwapShiftVRegFor rd) = shift64 ∧
      js'.vregs (JoltISA.amoWordSwapDwordVRegFor rd) = dword ∧
      js'.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (JoltISA.Encoded.ORI (.vreg (JoltISA.amoWordSwapMaskVRegFor rd))
            (.xreg (regidx.Regidx 0)) (-1 : BitVec 12)) <|
           .instr (.VirtualSRLI (.vreg (JoltISA.amoWordSwapMaskVRegFor rd))
            (.vreg (JoltISA.amoWordSwapMaskVRegFor rd))
            (JoltISA.srliBitmask (32 : BitVec 6))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let maskReg := JoltISA.amoWordSwapMaskVRegFor rd
  let shiftReg := JoltISA.amoWordSwapShiftVRegFor rd
  let dwordReg := JoltISA.amoWordSwapDwordVRegFor rd
  let oldReg := JoltISA.amoWordSwapOldVRegFor rd
  have hmask_w : WritableVReg maskReg := by
    unfold maskReg JoltISA.amoWordSwapMaskVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hshift_ne_mask : shiftReg ≠ maskReg := by
    unfold shiftReg maskReg JoltISA.amoWordSwapShiftVRegFor
      JoltISA.amoWordSwapMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_mask : dwordReg ≠ maskReg := by
    unfold dwordReg maskReg JoltISA.amoWordSwapDwordVRegFor
      JoltISA.amoWordSwapMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_mask : oldReg ≠ maskReg := by
    unfold oldReg maskReg JoltISA.amoWordSwapOldVRegFor
      JoltISA.amoWordSwapMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  obtain ⟨js_ones, _hx0, hones_sail_raw, hones_mask_raw,
      hones_preserves, hones_run⟩ :=
    JoltISA.exists_state_after_ori_run_vreg_xreg_of_sail_eq
      maskReg (regidx.Regidx 0) (-1 : BitVec 12)
      js s (0#64) h_sail (amo_word_read_x0_eq_zero s) hmask_w
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
  obtain ⟨js_mask, hmask_sail_raw, hmask_raw, hmask_preserves,
      hmask_tail⟩ :=
    JoltISA.exists_state_after_srli_block_run_vreg_vreg
      maskReg maskReg (32 : BitVec 6) js_ones hmask_w
  refine ⟨js_mask, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmask_sail_raw, hones_sail]
  · rw [hmask_raw, hones_mask]
    exact amo_word_low_word_mask_value
  · rw [hmask_preserves shiftReg hshift_ne_mask]
    exact hones_shift
  · rw [hmask_preserves dwordReg hdword_ne_mask]
    exact hones_dword
  · rw [hmask_preserves oldReg hold_ne_mask]
    exact hones_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_ones hones_run]
    have htail := hmask_tail tail
    unfold JoltISA.srliBlock at htail
    simpa [maskReg] using htail

/-- The postlude's mask-shift block turns the low-word mask into the selected
word-lane mask. -/
theorem amo_word_swap_shift_mask_prefix_run
    (js : SailJoltState) (s : SailState) (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_mask : js.vregs JoltISA.amoWordSwapMaskVReg =
      (0x00000000FFFFFFFF : BitVec 64))
    (h_shift : js.vregs JoltISA.amoWordSwapShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSwapDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSwapMaskVReg =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoWordSwapShiftVReg = shift64 ∧
      js'.vregs JoltISA.amoWordSwapDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoWordSwapInlineTmpVReg)
            (.vreg JoltISA.amoWordSwapShiftVReg) (0 : BitVec 64)) <|
           .instr (.MUL (.vreg JoltISA.amoWordSwapMaskVReg)
            (.vreg JoltISA.amoWordSwapMaskVReg)
            (.vreg JoltISA.amoWordSwapInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', h_sail_raw, h_mask_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      JoltISA.amoWordSwapMaskVReg JoltISA.amoWordSwapMaskVReg
      JoltISA.amoWordSwapShiftVReg JoltISA.amoWordSwapInlineTmpVReg js
      (by decide) (by unfold WritableVReg; decide)
      (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_mask_raw, h_mask, h_shift]
  · rw [h_preserves JoltISA.amoWordSwapShiftVReg (by decide) (by decide)]
    exact h_shift
  · rw [h_preserves JoltISA.amoWordSwapDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSwapOldVReg (by decide) (by decide)]
    exact h_old
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- Selected-register version of `amo_word_swap_shift_mask_prefix_run`. -/
theorem amo_word_swap_shift_mask_prefix_run_for
    (rd : regidx)
    (js : SailJoltState) (s : SailState) (shift64 dword old : BitVec 64)
    (h_sail : js.sail = s)
    (h_mask : js.vregs (JoltISA.amoWordSwapMaskVRegFor rd) =
      (0x00000000FFFFFFFF : BitVec 64))
    (h_shift : js.vregs (JoltISA.amoWordSwapShiftVRegFor rd) = shift64)
    (h_dword : js.vregs (JoltISA.amoWordSwapDwordVRegFor rd) = dword)
    (h_old : js.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs (JoltISA.amoWordSwapMaskVRegFor rd) =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs (JoltISA.amoWordSwapShiftVRegFor rd) = shift64 ∧
      js'.vregs (JoltISA.amoWordSwapDwordVRegFor rd) = dword ∧
      js'.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg (JoltISA.amoWordSwapInlineTmpVRegFor rd))
            (.vreg (JoltISA.amoWordSwapShiftVRegFor rd)) (0 : BitVec 64)) <|
           .instr (.MUL (.vreg (JoltISA.amoWordSwapMaskVRegFor rd))
            (.vreg (JoltISA.amoWordSwapMaskVRegFor rd))
            (.vreg (JoltISA.amoWordSwapInlineTmpVRegFor rd))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let maskReg := JoltISA.amoWordSwapMaskVRegFor rd
  let shiftReg := JoltISA.amoWordSwapShiftVRegFor rd
  let dwordReg := JoltISA.amoWordSwapDwordVRegFor rd
  let oldReg := JoltISA.amoWordSwapOldVRegFor rd
  let tmpReg := JoltISA.amoWordSwapInlineTmpVRegFor rd
  have hmask_w : WritableVReg maskReg := by
    unfold maskReg JoltISA.amoWordSwapMaskVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have htmp_w : WritableVReg tmpReg := by
    unfold tmpReg JoltISA.amoWordSwapInlineTmpVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hmask_ne_tmp : maskReg ≠ tmpReg := by
    unfold maskReg tmpReg JoltISA.amoWordSwapMaskVRegFor
      JoltISA.amoWordSwapInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hshift_ne_mask : shiftReg ≠ maskReg := by
    unfold shiftReg maskReg JoltISA.amoWordSwapShiftVRegFor
      JoltISA.amoWordSwapMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hshift_ne_tmp : shiftReg ≠ tmpReg := by
    unfold shiftReg tmpReg JoltISA.amoWordSwapShiftVRegFor
      JoltISA.amoWordSwapInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_mask : dwordReg ≠ maskReg := by
    unfold dwordReg maskReg JoltISA.amoWordSwapDwordVRegFor
      JoltISA.amoWordSwapMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_tmp : dwordReg ≠ tmpReg := by
    unfold dwordReg tmpReg JoltISA.amoWordSwapDwordVRegFor
      JoltISA.amoWordSwapInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_mask : oldReg ≠ maskReg := by
    unfold oldReg maskReg JoltISA.amoWordSwapOldVRegFor
      JoltISA.amoWordSwapMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_tmp : oldReg ≠ tmpReg := by
    unfold oldReg tmpReg JoltISA.amoWordSwapOldVRegFor
      JoltISA.amoWordSwapInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  obtain ⟨js', h_sail_raw, h_mask_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_vreg_vreg
      maskReg maskReg shiftReg tmpReg js hmask_ne_tmp hmask_w htmp_w
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_mask_raw, h_mask, h_shift]
  · rw [h_preserves shiftReg hshift_ne_mask hshift_ne_tmp]
    exact h_shift
  · rw [h_preserves dwordReg hdword_ne_mask hdword_ne_tmp]
    exact h_dword
  · rw [h_preserves oldReg hold_ne_mask hold_ne_tmp]
    exact h_old
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    simpa [maskReg, shiftReg, tmpReg] using h

/-- The postlude shifts the new word value from `rs2` into the selected dword
lane while preserving the prepared mask and old word. -/
theorem amo_word_swap_shift_new_prefix_run
    (rs2 : regidx) (js : SailJoltState) (s : SailState)
    (rs2Val shift64 shiftedMask dword old : BitVec 64)
    (h_sail : js.sail = s)
    (hrs2 : rX_bits rs2 s = .ok rs2Val s)
    (h_mask : js.vregs JoltISA.amoWordSwapMaskVReg = shiftedMask)
    (h_shift : js.vregs JoltISA.amoWordSwapShiftVReg = shift64)
    (h_dword : js.vregs JoltISA.amoWordSwapDwordVReg = dword)
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSwapShiftVReg =
        shift_bits_left rs2Val (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs JoltISA.amoWordSwapMaskVReg = shiftedMask ∧
      js'.vregs JoltISA.amoWordSwapDwordVReg = dword ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg JoltISA.amoWordSwapInlineTmpVReg)
            (.vreg JoltISA.amoWordSwapShiftVReg) (0 : BitVec 64)) <|
           .instr (.MUL (.vreg JoltISA.amoWordSwapShiftVReg)
            (.xreg rs2) (.vreg JoltISA.amoWordSwapInlineTmpVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  have hrs2_current : rX_bits rs2 js.sail = .ok rs2Val js.sail := by
    rw [h_sail]
    exact hrs2
  obtain ⟨js', _hrs2, h_sail_raw, h_shift_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_xreg_vreg
      JoltISA.amoWordSwapShiftVReg rs2 JoltISA.amoWordSwapShiftVReg
      JoltISA.amoWordSwapInlineTmpVReg js rs2Val hrs2_current
      (by unfold WritableVReg; decide) (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_shift_raw, h_shift]
  · rw [h_preserves JoltISA.amoWordSwapMaskVReg (by decide) (by decide)]
    exact h_mask
  · rw [h_preserves JoltISA.amoWordSwapDwordVReg (by decide) (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSwapOldVReg (by decide) (by decide)]
    exact h_old
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    exact h

/-- Selected-register version of `amo_word_swap_shift_new_prefix_run`. -/
theorem amo_word_swap_shift_new_prefix_run_for
    (rd : regidx)
    (rs2 : regidx) (js : SailJoltState) (s : SailState)
    (rs2Val shift64 shiftedMask dword old : BitVec 64)
    (h_sail : js.sail = s)
    (hrs2 : rX_bits rs2 s = .ok rs2Val s)
    (h_mask : js.vregs (JoltISA.amoWordSwapMaskVRegFor rd) = shiftedMask)
    (h_shift : js.vregs (JoltISA.amoWordSwapShiftVRegFor rd) = shift64)
    (h_dword : js.vregs (JoltISA.amoWordSwapDwordVRegFor rd) = dword)
    (h_old : js.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs (JoltISA.amoWordSwapShiftVRegFor rd) =
        shift_bits_left rs2Val (Sail.BitVec.extractLsb shift64 5 0) ∧
      js'.vregs (JoltISA.amoWordSwapMaskVRegFor rd) = shiftedMask ∧
      js'.vregs (JoltISA.amoWordSwapDwordVRegFor rd) = dword ∧
      js'.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualPow2 (.vreg (JoltISA.amoWordSwapInlineTmpVRegFor rd))
            (.vreg (JoltISA.amoWordSwapShiftVRegFor rd)) (0 : BitVec 64)) <|
           .instr (.MUL (.vreg (JoltISA.amoWordSwapShiftVRegFor rd))
            (.xreg rs2) (.vreg (JoltISA.amoWordSwapInlineTmpVRegFor rd))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let maskReg := JoltISA.amoWordSwapMaskVRegFor rd
  let shiftReg := JoltISA.amoWordSwapShiftVRegFor rd
  let dwordReg := JoltISA.amoWordSwapDwordVRegFor rd
  let oldReg := JoltISA.amoWordSwapOldVRegFor rd
  let tmpReg := JoltISA.amoWordSwapInlineTmpVRegFor rd
  have hshift_w : WritableVReg shiftReg := by
    unfold shiftReg JoltISA.amoWordSwapShiftVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have htmp_w : WritableVReg tmpReg := by
    unfold tmpReg JoltISA.amoWordSwapInlineTmpVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hshift_ne_tmp : shiftReg ≠ tmpReg := by
    unfold shiftReg tmpReg JoltISA.amoWordSwapShiftVRegFor
      JoltISA.amoWordSwapInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hmask_ne_shift : maskReg ≠ shiftReg := by
    unfold maskReg shiftReg JoltISA.amoWordSwapMaskVRegFor
      JoltISA.amoWordSwapShiftVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hmask_ne_tmp : maskReg ≠ tmpReg := by
    unfold maskReg tmpReg JoltISA.amoWordSwapMaskVRegFor
      JoltISA.amoWordSwapInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_shift : dwordReg ≠ shiftReg := by
    unfold dwordReg shiftReg JoltISA.amoWordSwapDwordVRegFor
      JoltISA.amoWordSwapShiftVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_tmp : dwordReg ≠ tmpReg := by
    unfold dwordReg tmpReg JoltISA.amoWordSwapDwordVRegFor
      JoltISA.amoWordSwapInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_shift : oldReg ≠ shiftReg := by
    unfold oldReg shiftReg JoltISA.amoWordSwapOldVRegFor
      JoltISA.amoWordSwapShiftVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_tmp : oldReg ≠ tmpReg := by
    unfold oldReg tmpReg JoltISA.amoWordSwapOldVRegFor
      JoltISA.amoWordSwapInlineTmpVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hrs2_current : rX_bits rs2 js.sail = .ok rs2Val js.sail := by
    rw [h_sail]
    exact hrs2
  obtain ⟨js', _hrs2, h_sail_raw, h_shift_raw, h_preserves, htail⟩ :=
    JoltISA.exists_state_after_sll_block_run_vreg_xreg_vreg
      shiftReg rs2 shiftReg tmpReg js rs2Val hrs2_current
      hshift_w htmp_w
  refine ⟨js', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_shift_raw, h_shift]
  · rw [h_preserves maskReg hmask_ne_shift hmask_ne_tmp]
    exact h_mask
  · rw [h_preserves dwordReg hdword_ne_shift hdword_ne_tmp]
    exact h_dword
  · rw [h_preserves oldReg hold_ne_shift hold_ne_tmp]
    exact h_old
  · intro tail
    have h := htail tail
    unfold JoltISA.sllBlock at h
    simpa [shiftReg, tmpReg] using h

/-- The XOR/AND/XOR postlude block splices the shifted new word into the loaded
dword and preserves the shifted old word. -/
theorem amo_word_swap_splice_block_run
    (js : SailJoltState) (s : SailState)
    (addr newValue dword old : BitVec 64)
    (hsetup : StoreSplice.WordStoreFacts addr (amoWordBase addr))
    (h_sail : js.sail = s)
    (h_dword : js.vregs JoltISA.amoWordSwapDwordVReg = dword)
    (h_shift :
      js.vregs JoltISA.amoWordSwapShiftVReg =
        shift_bits_left newValue
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_mask :
      js.vregs JoltISA.amoWordSwapMaskVReg =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSwapDwordVReg =
        amoWordSplicedDword addr newValue dword ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.XOR (.vreg JoltISA.amoWordSwapShiftVReg)
            (.vreg JoltISA.amoWordSwapDwordVReg)
            (.vreg JoltISA.amoWordSwapShiftVReg)) <|
           .instr (.AND (.vreg JoltISA.amoWordSwapShiftVReg)
            (.vreg JoltISA.amoWordSwapShiftVReg)
            (.vreg JoltISA.amoWordSwapMaskVReg)) <|
           .instr (.XOR (.vreg JoltISA.amoWordSwapDwordVReg)
            (.vreg JoltISA.amoWordSwapDwordVReg)
            (.vreg JoltISA.amoWordSwapShiftVReg)) tail)).run js =
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
      JoltISA.amoWordSwapShiftVReg JoltISA.amoWordSwapDwordVReg
      JoltISA.amoWordSwapShiftVReg js dword shiftedNew h_dword h_shift
      (by unfold WritableVReg; decide)
  have hxor_sail : js_xor.sail = s := by
    rw [hxor_sail_raw, h_sail]
  have hxor_shift : js_xor.vregs JoltISA.amoWordSwapShiftVReg =
      dword ^^^ shiftedNew := by
    exact hxor_shift_raw
  have hxor_mask : js_xor.vregs JoltISA.amoWordSwapMaskVReg = shiftedMask := by
    rw [hxor_preserves JoltISA.amoWordSwapMaskVReg (by decide)]
    exact h_mask
  have hxor_dword : js_xor.vregs JoltISA.amoWordSwapDwordVReg = dword := by
    rw [hxor_preserves JoltISA.amoWordSwapDwordVReg (by decide)]
    exact h_dword
  have hxor_old : js_xor.vregs JoltISA.amoWordSwapOldVReg = old := by
    rw [hxor_preserves JoltISA.amoWordSwapOldVReg (by decide)]
    exact h_old
  obtain ⟨js_and, hand_sail_raw, hand_shift_raw, hand_preserves,
      hand_run⟩ :=
    amo_word_exists_state_after_and_run_vreg_vreg_vreg
      JoltISA.amoWordSwapShiftVReg JoltISA.amoWordSwapShiftVReg
      JoltISA.amoWordSwapMaskVReg js_xor (dword ^^^ shiftedNew) shiftedMask
      hxor_shift hxor_mask (by unfold WritableVReg; decide)
  have hand_sail : js_and.sail = s := by
    rw [hand_sail_raw, hxor_sail]
  have hand_shift : js_and.vregs JoltISA.amoWordSwapShiftVReg =
      (dword ^^^ shiftedNew) &&& shiftedMask := by
    exact hand_shift_raw
  have hand_dword : js_and.vregs JoltISA.amoWordSwapDwordVReg = dword := by
    rw [hand_preserves JoltISA.amoWordSwapDwordVReg (by decide)]
    exact hxor_dword
  have hand_old : js_and.vregs JoltISA.amoWordSwapOldVReg = old := by
    rw [hand_preserves JoltISA.amoWordSwapOldVReg (by decide)]
    exact hxor_old
  obtain ⟨js_splice, hsplice_sail_raw, hsplice_dword_raw,
      hsplice_preserves, hxor2_run⟩ :=
    JoltISA.exists_state_after_xor_run_vreg_vreg_vreg
      JoltISA.amoWordSwapDwordVReg JoltISA.amoWordSwapDwordVReg
      JoltISA.amoWordSwapShiftVReg js_and dword
      ((dword ^^^ shiftedNew) &&& shiftedMask) hand_dword hand_shift
      (by unfold WritableVReg; decide)
  have hspliced_value := amo_word_splice_shifted_eq addr newValue dword hsetup
  refine ⟨js_splice, ?_, ?_, ?_, ?_⟩
  · rw [hsplice_sail_raw, hand_sail]
  · rw [hsplice_dword_raw]
    exact hspliced_value
  · rw [hsplice_preserves JoltISA.amoWordSwapOldVReg (by decide)]
    exact hand_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js_xor hxor_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_xor js_and hand_run]
    rw [JoltISA.execProgram_instr_run_retire _ _ js_and js_splice hxor2_run]

/-- Selected-register version of `amo_word_swap_splice_block_run`. -/
theorem amo_word_swap_splice_block_run_for
    (rd : regidx) (js : SailJoltState) (s : SailState)
    (addr newValue dword old : BitVec 64)
    (hsetup : StoreSplice.WordStoreFacts addr (amoWordBase addr))
    (h_sail : js.sail = s)
    (h_dword : js.vregs (JoltISA.amoWordSwapDwordVRegFor rd) = dword)
    (h_shift :
      js.vregs (JoltISA.amoWordSwapShiftVRegFor rd) =
        shift_bits_left newValue
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_mask :
      js.vregs (JoltISA.amoWordSwapMaskVRegFor rd) =
        shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
          (Sail.BitVec.extractLsb
            (shift_bits_left addr (3 : BitVec 6)) 5 0))
    (h_old : js.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs (JoltISA.amoWordSwapDwordVRegFor rd) =
        amoWordSplicedDword addr newValue dword ∧
      js'.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.XOR (.vreg (JoltISA.amoWordSwapShiftVRegFor rd))
            (.vreg (JoltISA.amoWordSwapDwordVRegFor rd))
            (.vreg (JoltISA.amoWordSwapShiftVRegFor rd))) <|
           .instr (.AND (.vreg (JoltISA.amoWordSwapShiftVRegFor rd))
            (.vreg (JoltISA.amoWordSwapShiftVRegFor rd))
            (.vreg (JoltISA.amoWordSwapMaskVRegFor rd))) <|
           .instr (.XOR (.vreg (JoltISA.amoWordSwapDwordVRegFor rd))
            (.vreg (JoltISA.amoWordSwapDwordVRegFor rd))
            (.vreg (JoltISA.amoWordSwapShiftVRegFor rd))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let maskReg := JoltISA.amoWordSwapMaskVRegFor rd
  let shiftReg := JoltISA.amoWordSwapShiftVRegFor rd
  let dwordReg := JoltISA.amoWordSwapDwordVRegFor rd
  let oldReg := JoltISA.amoWordSwapOldVRegFor rd
  let shiftedNew :=
    shift_bits_left newValue
      (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
  let shiftedMask :=
    shift_bits_left (0x00000000FFFFFFFF : BitVec 64)
      (Sail.BitVec.extractLsb (shift_bits_left addr (3 : BitVec 6)) 5 0)
  have hshift_w : WritableVReg shiftReg := by
    unfold shiftReg JoltISA.amoWordSwapShiftVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hdword_w : WritableVReg dwordReg := by
    unfold dwordReg JoltISA.amoWordSwapDwordVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hmask_ne_shift : maskReg ≠ shiftReg := by
    unfold maskReg shiftReg JoltISA.amoWordSwapMaskVRegFor
      JoltISA.amoWordSwapShiftVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hdword_ne_shift : dwordReg ≠ shiftReg := by
    unfold dwordReg shiftReg JoltISA.amoWordSwapDwordVRegFor
      JoltISA.amoWordSwapShiftVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_shift : oldReg ≠ shiftReg := by
    unfold oldReg shiftReg JoltISA.amoWordSwapOldVRegFor
      JoltISA.amoWordSwapShiftVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_dword : oldReg ≠ dwordReg := by
    unfold oldReg dwordReg JoltISA.amoWordSwapOldVRegFor
      JoltISA.amoWordSwapDwordVRegFor JoltISA.amoVRegFor
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

/-- The postlude recomputes the enclosing dword base before storing it. -/
theorem amo_word_swap_store_base_prefix_run
    (rs1 : regidx) (js : SailJoltState) (s : SailState)
    (addr dwordNew old : BitVec 64)
    (h_sail : js.sail = s)
    (hrs1 : rX_bits rs1 s = .ok addr s)
    (h_dword : js.vregs JoltISA.amoWordSwapDwordVReg = dwordNew)
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs JoltISA.amoWordSwapMaskVReg = amoWordBase addr ∧
      js'.vregs JoltISA.amoWordSwapDwordVReg = dwordNew ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (JoltISA.Encoded.ANDI (.vreg JoltISA.amoWordSwapMaskVReg)
            (.xreg rs1) (-8 : BitVec 12)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  obtain ⟨js', _hrs1, h_sail_raw, h_base_raw, h_preserves, hrun⟩ :=
    JoltISA.exists_state_after_andi_run_vreg_xreg_of_sail_eq
      JoltISA.amoWordSwapMaskVReg rs1 (-8 : BitVec 12)
      js s addr h_sail hrs1 (by unfold WritableVReg; decide)
  refine ⟨js', ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_sail_raw, h_sail]
  · rw [h_base_raw]
    exact amo_word_base_mask addr
  · rw [h_preserves JoltISA.amoWordSwapDwordVReg (by decide)]
    exact h_dword
  · rw [h_preserves JoltISA.amoWordSwapOldVReg (by decide)]
    exact h_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hrun]

/-- Selected-register version of `amo_word_swap_store_base_prefix_run`. -/
theorem amo_word_swap_store_base_prefix_run_for
    (rd rs1 : regidx) (js : SailJoltState) (s : SailState)
    (addr dwordNew old : BitVec 64)
    (h_sail : js.sail = s)
    (hrs1 : rX_bits rs1 s = .ok addr s)
    (h_dword : js.vregs (JoltISA.amoWordSwapDwordVRegFor rd) = dwordNew)
    (h_old : js.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old) :
    ∃ js',
      js'.sail = s ∧
      js'.vregs (JoltISA.amoWordSwapMaskVRegFor rd) = amoWordBase addr ∧
      js'.vregs (JoltISA.amoWordSwapDwordVRegFor rd) = dwordNew ∧
      js'.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (JoltISA.Encoded.ANDI (.vreg (JoltISA.amoWordSwapMaskVRegFor rd))
            (.xreg rs1) (-8 : BitVec 12)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let maskReg := JoltISA.amoWordSwapMaskVRegFor rd
  let dwordReg := JoltISA.amoWordSwapDwordVRegFor rd
  let oldReg := JoltISA.amoWordSwapOldVRegFor rd
  have hmask_w : WritableVReg maskReg := by
    unfold maskReg JoltISA.amoWordSwapMaskVRegFor JoltISA.amoVRegFor
      WritableVReg
    split <;> decide
  have hdword_ne_mask : dwordReg ≠ maskReg := by
    unfold dwordReg maskReg JoltISA.amoWordSwapDwordVRegFor
      JoltISA.amoWordSwapMaskVRegFor JoltISA.amoVRegFor
    split <;> decide
  have hold_ne_mask : oldReg ≠ maskReg := by
    unfold oldReg maskReg JoltISA.amoWordSwapOldVRegFor
      JoltISA.amoWordSwapMaskVRegFor JoltISA.amoVRegFor
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

/-- The dword store instruction writes the spliced dword and preserves the
virtual-register file for the final writeback. -/
theorem amo_word_swap_sd_spliced_dword_run
    (js : SailJoltState) (s : SailState) (addr dwordNew old : BitVec 64)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 s)
    (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 s)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_sail : js.sail = s)
    (h_base : js.vregs JoltISA.amoWordSwapMaskVReg = amoWordBase addr)
    (h_dword : js.vregs JoltISA.amoWordSwapDwordVReg = dwordNew)
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old)
    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
    ∃ js',
      js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (JoltISA.Encoded.SD (.vreg JoltISA.amoWordSwapMaskVReg)
            (.vreg JoltISA.amoWordSwapDwordVReg) (0 : BitVec 12)) tail)).run js =
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
      vmem_write_addr (Virtaddr (js.vregs JoltISA.amoWordSwapMaskVReg +
          sign_extend (m := 64) (0 : BitVec 12))) 8
        (js.vregs JoltISA.amoWordSwapDwordVReg)
        (Store Data) false false false js.sail =
      .ok (Ok true) (state_after_dword_store s (amoWordBase addr) dwordNew) := by
    rw [h_sail, h_base, h_dword, amo_word_zero_offset_addr (amoWordBase addr)]
    exact hwrite_dword
  let js' : SailJoltState :=
    { js with sail := state_after_dword_store s (amoWordBase addr) dwordNew }
  have hsd_align :
      (js.vregs JoltISA.amoWordSwapMaskVReg +
          sign_extend (m := 64) (0 : BitVec 12)) &&& (7 : BitVec 64) = 0 := by
    rw [h_base, amo_word_zero_offset_addr (amoWordBase addr)]
    exact amo_word_base_aligned addr
  have hsd :
      (JoltISA.execInstr
        (JoltISA.Encoded.SD (.vreg JoltISA.amoWordSwapMaskVReg)
          (.vreg JoltISA.amoWordSwapDwordVReg) (0 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS js' :=
    JoltISA.execInstr_sd_vreg_run_of_write
      JoltISA.amoWordSwapMaskVReg JoltISA.amoWordSwapDwordVReg (0 : BitVec 12)
      js (state_after_dword_store s (amoWordBase addr) dwordNew)
      hsd_align hwrite_current
      (by rw [h_base, amo_word_zero_offset_addr]; exact hwrite_mmio.ram)
      (by rw [h_sail]; exact hpriv) (by rw [h_sail]; exact hmprv)
      (by rw [h_sail, h_base, amo_word_zero_offset_addr]; exact hstore_pmp)
      (by rw [h_sail, h_base, amo_word_zero_offset_addr]; exact hwrite_mmio)
      (by rw [h_base, amo_word_zero_offset_addr]; exact hjolt)
  refine ⟨js', rfl, ?_, ?_⟩
  · exact h_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hsd]

/-- Selected-register version of `amo_word_swap_sd_spliced_dword_run`. -/
theorem amo_word_swap_sd_spliced_dword_run_for
    (rd : regidx)
    (js : SailJoltState) (s : SailState) (addr dwordNew old : BitVec 64)
    (hpriv : Assumptions.CurPrivilegeMachine s)
    (hmprv : Assumptions.MstatusMprvZero s)
    (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 s)
    (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 s)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_sail : js.sail = s)
    (h_base : js.vregs (JoltISA.amoWordSwapMaskVRegFor rd) = amoWordBase addr)
    (h_dword : js.vregs (JoltISA.amoWordSwapDwordVRegFor rd) = dwordNew)
    (h_old : js.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old)
    (hjolt : Assumptions.JoltRamStoreOk (amoWordBase addr) js) :
    ∃ js',
      js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
      js'.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (JoltISA.Encoded.SD (.vreg (JoltISA.amoWordSwapMaskVRegFor rd))
            (.vreg (JoltISA.amoWordSwapDwordVRegFor rd))
            (0 : BitVec 12)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  let maskReg := JoltISA.amoWordSwapMaskVRegFor rd
  let dwordReg := JoltISA.amoWordSwapDwordVRegFor rd
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
    { js with sail := state_after_dword_store s (amoWordBase addr) dwordNew }
  have hsd_align :
      (js.vregs maskReg + sign_extend (m := 64) (0 : BitVec 12)) &&&
          (7 : BitVec 64) =
        0 := by
    rw [h_base, amo_word_zero_offset_addr (amoWordBase addr)]
    exact amo_word_base_aligned addr
  have hsd :
      (JoltISA.execInstr
        (JoltISA.Encoded.SD (.vreg maskReg) (.vreg dwordReg) (0 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS js' :=
    JoltISA.execInstr_sd_vreg_run_of_write
      maskReg dwordReg (0 : BitVec 12)
      js (state_after_dword_store s (amoWordBase addr) dwordNew)
      hsd_align hwrite_current
      (by rw [h_base, amo_word_zero_offset_addr]; exact hwrite_mmio.ram)
      (by rw [h_sail]; exact hpriv) (by rw [h_sail]; exact hmprv)
      (by rw [h_sail, h_base, amo_word_zero_offset_addr]; exact hstore_pmp)
      (by rw [h_sail, h_base, amo_word_zero_offset_addr]; exact hwrite_mmio)
      (by rw [h_base, amo_word_zero_offset_addr]; exact hjolt)
  refine ⟨js', rfl, ?_, ?_⟩
  · exact h_old
  · intro tail
    rw [JoltISA.execProgram_instr_run_retire _ _ js js' hsd]

/-- The final postlude instruction writes the sign-extended old word to `rd`. -/
theorem amo_word_swap_writeback_old_run
    (rd : regidx) (js : SailJoltState) (s : SailState)
    (addr : BitVec 64) (result oldWord : BitVec 32) (old : BitVec 64)
    (h_sail : js.sail = state_after_word_store s addr result)
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old)
    (h_old_word :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) oldWord) :
    ∃ js',
      js'.sail = amoWordFinalSailState rd s addr result oldWord ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualSignExtendWord (JoltISA.amoDstFor rd)
            (.vreg JoltISA.amoWordSwapOldVReg)) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  exact
    amo_word_writeback_old_run_from JoltISA.amoWordSwapOldVReg
      rd js s addr result oldWord old h_sail h_old h_old_word

/-- Selected-register version of `amo_word_swap_writeback_old_run`. -/
theorem amo_word_swap_writeback_old_run_for
    (rd : regidx) (js : SailJoltState) (s : SailState)
    (addr : BitVec 64) (result oldWord : BitVec 32) (old : BitVec 64)
    (h_sail : js.sail = state_after_word_store s addr result)
    (h_old : js.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old)
    (h_old_word :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) oldWord) :
    ∃ js',
      js'.sail = amoWordFinalSailState rd s addr result oldWord ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.VirtualSignExtendWord (JoltISA.amoDstFor rd)
            (.vreg (JoltISA.amoWordSwapOldVRegFor rd))) tail)).run js =
          (JoltISA.execProgram tail).run js' := by
  exact
    amo_word_writeback_old_run_from (JoltISA.amoWordSwapOldVRegFor rd)
      rd js s addr result oldWord old h_sail h_old h_old_word

/-- The aligned `AMOSWAP.W` postlude stores `rs2[31:0]` into the selected word
lane and writes the sign-extended old word into `rd`. -/
theorem amo_word_swap_post64_amoswap_aligned_run
    (rs2 rs1 rd : regidx) (js js_pre : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (addr rs2Val : BitVec 64) (oldWord : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
    (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail)
    (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hpre_sail : js_pre.sail = js.sail)
    (hpre_dword :
      js_pre.vregs JoltISA.amoWordSwapDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf)
    (hpre_shift :
      js_pre.vregs JoltISA.amoWordSwapShiftVReg =
        shift_bits_left addr (3 : BitVec 6))
    (hpre_old :
      js_pre.vregs JoltISA.amoWordSwapOldVReg =
        amoWordShiftedOld addr
          (loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf))
    (hold :
      (Sail.BitVec.extractLsb
        (amoWordShiftedOld addr
          (loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf))
        31 0 : BitVec 32) = oldWord)
    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
    (hpre_layout : js_pre.jolt_device.memory_layout = js.jolt_device.memory_layout) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoPost64ProgramWithScratch rs1 rd (.xreg rs2)
          JoltISA.amoWordSwapDwordVReg JoltISA.amoWordSwapShiftVReg
          JoltISA.amoWordSwapMaskVReg JoltISA.amoWordSwapOldVReg
          JoltISA.amoWordSwapInlineTmpVReg)).run js_pre =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoWordFinalSailState rd js.sail addr
          (Sail.BitVec.extractLsb rs2Val 31 0) oldWord := by
  let shift64 : BitVec 64 := shift_bits_left addr (3 : BitVec 6)
  let shift6 : BitVec 6 := Sail.BitVec.extractLsb shift64 5 0
  let dword : BitVec 64 :=
    loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf
  let old : BitVec 64 := amoWordShiftedOld addr dword
  let mask32 := (0x00000000FFFFFFFF : BitVec 64)
  let shiftedMask : BitVec 64 := shift_bits_left mask32 shift6
  let dwordNew : BitVec 64 := amoWordSplicedDword addr rs2Val dword
  let wordResult : BitVec 32 := Sail.BitVec.extractLsb rs2Val 31 0
  have hsetup := amo_word_store_facts addr h_no_ovf h_align
  obtain ⟨js_mask32, hmask_sail, hmask_mask, hmask_shift, hmask_dword,
      hmask_old, hmask_tail⟩ :=
    amo_word_swap_mask32_prefix_run js_pre js.sail shift64 dword old
      hpre_sail hpre_shift
      (by simpa [dword] using hpre_dword)
      (by simpa [old, dword] using hpre_old)
  obtain ⟨js_shifted_mask, hshift_mask_sail, hshift_mask_mask,
      hshift_mask_shift, hshift_mask_dword, hshift_mask_old,
      hshift_mask_tail⟩ :=
    amo_word_swap_shift_mask_prefix_run js_mask32 js.sail shift64 dword old
      hmask_sail hmask_mask hmask_shift hmask_dword hmask_old
  obtain ⟨js_shifted_new, hshift_new_sail, hshift_new_shift,
      hshift_new_mask, hshift_new_dword, hshift_new_old,
      hshift_new_tail⟩ :=
    amo_word_swap_shift_new_prefix_run rs2 js_shifted_mask js.sail rs2Val
      shift64 shiftedMask dword old hshift_mask_sail hrs2 hshift_mask_mask
      hshift_mask_shift hshift_mask_dword hshift_mask_old
  obtain ⟨js_splice, hsplice_sail, hsplice_dword, hsplice_old,
      hsplice_tail⟩ :=
    amo_word_swap_splice_block_run js_shifted_new js.sail addr rs2Val dword old
      hsetup hshift_new_sail hshift_new_dword hshift_new_shift
      hshift_new_mask hshift_new_old
  obtain ⟨js_store_base, hstore_base_sail, hstore_base, hstore_base_dword,
      hstore_base_old, hstore_base_tail⟩ :=
    amo_word_swap_store_base_prefix_run rs1 js_splice js.sail addr dwordNew old
      hsplice_sail hrs1 hsplice_dword hsplice_old
  have hstore_base_layout :
      js_store_base.jolt_device.memory_layout = js.jolt_device.memory_layout :=
    (JoltIOSetupFrame.layout_of_tail_run hstore_base_tail).trans <|
    (JoltIOSetupFrame.layout_of_tail_run hsplice_tail).trans <|
    (JoltIOSetupFrame.layout_of_tail_run hshift_new_tail).trans <|
    (JoltIOSetupFrame.layout_of_tail_run hshift_mask_tail).trans <|
    (JoltIOSetupFrame.layout_of_tail_run hmask_tail).trans hpre_layout
  obtain ⟨js_store, hstore_sail, hstore_old, hstore_tail⟩ :=
    amo_word_swap_sd_spliced_dword_run js_store_base js.sail addr dwordNew old
      hpriv hmprv hstore_pmp hwrite_mmio h_no_ovf hstore_base_sail
      hstore_base hstore_base_dword hstore_base_old
      ⟨by rw [hstore_base_layout]; exact hjolt_store.below_heap_end,
       by rw [hstore_base_layout]; exact hjolt_store.outside_canary⟩
  have hword_store :
      state_after_dword_store js.sail (amoWordBase addr) dwordNew =
        state_after_word_store js.sail addr wordResult := by
    change
      state_after_dword_store js.sail (amoWordBase addr)
        (amoWordSplicedDword addr rs2Val
          (loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf)) =
        state_after_word_store js.sail addr
          (Sail.BitVec.extractLsb rs2Val 31 0)
    exact
      amo_word_spliced_dword_store_eq_word_store
        js.sail addr rs2Val hsetup hbytes_base
  have hstore_sail_word :
      js_store.sail = state_after_word_store js.sail addr wordResult := by
    rw [hstore_sail, hword_store]
  have hold_writeback :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) oldWord := by
    exact
      amo_word_shifted_old_sign_extend_eq_loaded_word
        addr dword oldWord (by simpa [old, dword] using hold)
  obtain ⟨jsf, hwriteback_sail, hwriteback_tail⟩ :=
    amo_word_swap_writeback_old_run rd js_store js.sail addr wordResult oldWord old
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

/-- Selected-register version of `amo_word_swap_post64_amoswap_aligned_run`. -/
theorem amo_word_swap_post64_amoswap_aligned_run_for
    (rs2 rs1 rd : regidx) (js js_pre : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (addr rs2Val : BitVec 64) (oldWord : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
    (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail)
    (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
    (h_no_ovf : (amoWordBase addr).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hpre_sail : js_pre.sail = js.sail)
    (hpre_dword :
      js_pre.vregs (JoltISA.amoWordSwapDwordVRegFor rd) =
        loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf)
    (hpre_shift :
      js_pre.vregs (JoltISA.amoWordSwapShiftVRegFor rd) =
        shift_bits_left addr (3 : BitVec 6))
    (hpre_old :
      js_pre.vregs (JoltISA.amoWordSwapOldVRegFor rd) =
        amoWordShiftedOld addr
          (loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf))
    (hold :
      (Sail.BitVec.extractLsb
        (amoWordShiftedOld addr
          (loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf))
        31 0 : BitVec 32) = oldWord)
    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
    (hpre_layout : js_pre.jolt_device.memory_layout = js.jolt_device.memory_layout) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram
        (JoltISA.amoPost64ProgramWithScratch rs1 rd (.xreg rs2)
          (JoltISA.amoWordSwapDwordVRegFor rd)
          (JoltISA.amoWordSwapShiftVRegFor rd)
          (JoltISA.amoWordSwapMaskVRegFor rd)
          (JoltISA.amoWordSwapOldVRegFor rd)
          (JoltISA.amoWordSwapInlineTmpVRegFor rd))).run js_pre =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoWordFinalSailState rd js.sail addr
          (Sail.BitVec.extractLsb rs2Val 31 0) oldWord := by
  let shift64 : BitVec 64 := shift_bits_left addr (3 : BitVec 6)
  let shift6 : BitVec 6 := Sail.BitVec.extractLsb shift64 5 0
  let dword : BitVec 64 :=
    loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf
  let old : BitVec 64 := amoWordShiftedOld addr dword
  let mask32 := (0x00000000FFFFFFFF : BitVec 64)
  let shiftedMask : BitVec 64 := shift_bits_left mask32 shift6
  let dwordNew : BitVec 64 := amoWordSplicedDword addr rs2Val dword
  let wordResult : BitVec 32 := Sail.BitVec.extractLsb rs2Val 31 0
  have hsetup := amo_word_store_facts addr h_no_ovf h_align
  obtain ⟨js_mask32, hmask_sail, hmask_mask, hmask_shift, hmask_dword,
      hmask_old, hmask_tail⟩ :=
    amo_word_swap_mask32_prefix_run_for rd js_pre js.sail shift64 dword old
      hpre_sail hpre_shift
      (by simpa [dword] using hpre_dword)
      (by simpa [old, dword] using hpre_old)
  obtain ⟨js_shifted_mask, hshift_mask_sail, hshift_mask_mask,
      hshift_mask_shift, hshift_mask_dword, hshift_mask_old,
      hshift_mask_tail⟩ :=
    amo_word_swap_shift_mask_prefix_run_for rd js_mask32 js.sail shift64
      dword old hmask_sail hmask_mask hmask_shift hmask_dword hmask_old
  obtain ⟨js_shifted_new, hshift_new_sail, hshift_new_shift,
      hshift_new_mask, hshift_new_dword, hshift_new_old,
      hshift_new_tail⟩ :=
    amo_word_swap_shift_new_prefix_run_for rd rs2 js_shifted_mask js.sail
      rs2Val shift64 shiftedMask dword old hshift_mask_sail hrs2
      hshift_mask_mask hshift_mask_shift hshift_mask_dword hshift_mask_old
  obtain ⟨js_splice, hsplice_sail, hsplice_dword, hsplice_old,
      hsplice_tail⟩ :=
    amo_word_swap_splice_block_run_for rd js_shifted_new js.sail addr rs2Val
      dword old hsetup hshift_new_sail hshift_new_dword hshift_new_shift
      hshift_new_mask hshift_new_old
  obtain ⟨js_store_base, hstore_base_sail, hstore_base, hstore_base_dword,
      hstore_base_old, hstore_base_tail⟩ :=
    amo_word_swap_store_base_prefix_run_for rd rs1 js_splice js.sail addr
      dwordNew old hsplice_sail hrs1 hsplice_dword hsplice_old
  have hstore_base_layout :
      js_store_base.jolt_device.memory_layout = js.jolt_device.memory_layout :=
    (JoltIOSetupFrame.layout_of_tail_run hstore_base_tail).trans <|
    (JoltIOSetupFrame.layout_of_tail_run hsplice_tail).trans <|
    (JoltIOSetupFrame.layout_of_tail_run hshift_new_tail).trans <|
    (JoltIOSetupFrame.layout_of_tail_run hshift_mask_tail).trans <|
    (JoltIOSetupFrame.layout_of_tail_run hmask_tail).trans hpre_layout
  obtain ⟨js_store, hstore_sail, hstore_old, hstore_tail⟩ :=
    amo_word_swap_sd_spliced_dword_run_for rd js_store_base js.sail addr
      dwordNew old hpriv hmprv hstore_pmp hwrite_mmio h_no_ovf
      hstore_base_sail hstore_base hstore_base_dword hstore_base_old
      ⟨by rw [hstore_base_layout]; exact hjolt_store.below_heap_end,
       by rw [hstore_base_layout]; exact hjolt_store.outside_canary⟩
  have hword_store :
      state_after_dword_store js.sail (amoWordBase addr) dwordNew =
        state_after_word_store js.sail addr wordResult := by
    change
      state_after_dword_store js.sail (amoWordBase addr)
        (amoWordSplicedDword addr rs2Val
          (loaded_dword_at js.sail (amoWordBase addr) hbytes_base h_no_ovf)) =
        state_after_word_store js.sail addr
          (Sail.BitVec.extractLsb rs2Val 31 0)
    exact
      amo_word_spliced_dword_store_eq_word_store
        js.sail addr rs2Val hsetup hbytes_base
  have hstore_sail_word :
      js_store.sail = state_after_word_store js.sail addr wordResult := by
    rw [hstore_sail, hword_store]
  have hold_writeback :
      sign_extend (m := 64)
        ((Sail.BitVec.extractLsb old 31 0) : BitVec 32) =
      sign_extend (m := 64) oldWord := by
    exact
      amo_word_shifted_old_sign_extend_eq_loaded_word
        addr dword oldWord (by simpa [old, dword] using hold)
  obtain ⟨jsf, hwriteback_sail, hwriteback_tail⟩ :=
    amo_word_swap_writeback_old_run_for rd js_store js.sail addr wordResult
      oldWord old hstore_sail_word hstore_old hold_writeback
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

/-- The generated swap is an opened lane followed directly by its merge.
For example, the replacement comes from rs2 without a middle scratch result. -/
private theorem amoswapwProgramAuto_eq_window (rs2 rs1 rd : regidx) :
    JoltISA.amoswapwProgramAuto rd rs1 rs2 =
      amoWordWindowProgram (.done RETIRE_SUCCESS) (.xreg rs2) rs1 rd := by
  cases hrd : JoltISA.isX0 rd <;>
    simp only [JoltISA.amoswapwProgramAuto, amoWordWindowProgram,
      JoltISA.amoPre64Program, JoltISA.amoPre64ProgramWithScratch,
      JoltISA.amoWordMergeProgram,
      JoltISA.laneWindowOpen, JoltISA.laneWindowExtract, JoltISA.laneWindowMerge,
      JoltISA.amoWordOldVRegFor, JoltISA.amoWordDwordVRegFor, JoltISA.amoWordLaneVRegFor,
      JoltISA.amoVRegFor, JoltISA.amoDstFor, JoltISA.sideEffectingRdZeroDst,
      hrd, Bool.false_eq_true, if_false, if_true] <;> rfl

/-- An aligned `AMOSWAP.W` stores the low word of `rs2` and returns the old
word sign-extended in `rd`; for example, address 12 updates the upper lane. -/
theorem amoswapwProgram_concrete_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hpriv : Assumptions.CurPrivilegeMachine js.sail)
    (hmprv : Assumptions.MstatusMprvZero js.sail)
    (addr rs2Val : BitVec 64) (oldWord : BitVec 32)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8)
    (hload_pmp : Assumptions.LoadPmpOk (amoWordBase addr) 8 js.sail)
    (hread_mmio : Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail)
    (hstore_pmp : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail)
    (hwrite_mmio : Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail)
    (h_align : addr &&& (3 : BitVec 64) = 0)
    (hjolt_load : Assumptions.JoltRamLoadOk (amoWordBase addr) js)
    (hjolt_store : Assumptions.JoltRamStoreOk (amoWordBase addr) js)
    (hold :
      (Sail.BitVec.extractLsb
        (amoWordShiftedOld addr
          (loaded_dword_at js.sail (amoWordBase addr) hbytes_base
            ((amo_word_base_no_ovf addr) :
              (amoWordBase addr).toNat + 7 < 2 ^ 64)))
        31 0 : BitVec 32) = oldWord) :
    ∃ jsf : SailJoltState,
      (JoltISA.execProgram (JoltISA.amoswapwProgramAuto rd rs1 rs2)).run js =
        .ok RETIRE_SUCCESS jsf ∧
      jsf.sail =
        amoWordFinalSailState rd js.sail addr
          (Sail.BitVec.extractLsb rs2Val 31 0) oldWord := by
  have hword : word_of_dword
      (loaded_dword_at js.sail (amoWordBase addr) hbytes_base (amo_word_base_no_ovf addr))
      (addr &&& (7 : BitVec 64)).toNat = oldWord := by
    rw [← hold]
    apply amo_word_sign_extend_64_injective
    symm
    simpa only [amoWordShiftedOld] using srl_sign_extend_word_extracts_word
      (loaded_dword_at js.sail (amoWordBase addr) hbytes_base (amo_word_base_no_ovf addr))
      addr h_align
  obtain ⟨jsf, hrun, hfinal⟩ := amo_word_window_program_aligned_run
    (.done RETIRE_SUCCESS) (.xreg rs2) rs1 rd js addr rs2Val hrs1 hbytes_base
    hread_mmio hwrite_mmio h_align hjolt_load hjolt_store
    (by intro pre hsail hdword hlane hold
        refine ⟨pre, rfl, rfl, hold, hdword, hlane, ?_⟩
        exact JoltISA.readSrc_xreg_run_of_read rs2 _ rs2Val (by
          change rX_bits rs2 pre.sail = .ok rs2Val pre.sail
          rw [hsail]; exact hrs2))
  refine ⟨jsf, ?_, ?_⟩
  · rw [amoswapwProgramAuto_eq_window]
    exact hrun
  · simpa only [hword] using hfinal

/-- Main public theorem for `AMOSWAP.W`.

The theorem takes one primitive-only atomic bundle. Exact memory facts are
derived internally from that bundle. -/
private theorem amoswapwProgramAuto_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js) :
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.amoswapwProgramAuto rd rs1 rs2)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 4 rd).run js.sail := by
  apply amo_word_program_eq_sail amoop.AMOSWAP _ rs2 rs1 rd js h (by decide)
    (amoswapwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd)
  · intro halign
    exact amoswapwProgram_concrete_aligned rs2 rs1 rd js h.cur_privilege h.mstatus_mprv
      h.rs1_val h.rs2_val (amoWordBundleOld amoop.AMOSWAP rs2 rs1 rd js h)
      h.rs1_read h.rs2_read (Assumptions.DwordPresent.memBytesPresentAt h.dword_present)
      (by simpa using h.load_pmp.subaccess (offset := 0) (accessWidth := 8) (by decide) (by omega))
      (by simpa using h.not_readable_mmio.subaccess (offset := 0) (accessWidth := 8) (by decide) (by omega))
      (by simpa using h.store_pmp.subaccess (offset := 0) (accessWidth := 8) (by decide) (by omega))
      (by simpa using h.not_writable_mmio.subaccess (offset := 0) (accessWidth := 8) (by decide) (by omega))
      halign h.jolt_ram_load h.jolt_ram_store
      (by apply amo_word_sign_extend_64_injective
          simpa only [amoWordShiftedOld, amoWordBundleOld] using
            srl_sign_extend_word_extracts_word
              (loaded_dword_at js.sail (amoWordBase h.rs1_val)
                (Assumptions.DwordPresent.memBytesPresentAt h.dword_present)
                (amo_word_base_no_ovf h.rs1_val)) h.rs1_val halign)
  · intro halign
    rw [amoswapwProgramAuto_eq_window]
    exact amo_word_pre64_with_scratch_misaligned_run rs1 _ _ _ _ js h.rs1_val h.rs1_read halign

/-- Main public theorem for `AMOSWAP.W`. -/
def amoswapwProgramEqSailStatement
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (_h : AmoWordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js) : Prop :=
  System.systemProjectResult
      ((JoltISA.execProgram
        (JoltISA.amoswapwProgramAuto rd rs1 rs2)).run js) =
    (execute_AMO amoop.AMOSWAP false false rs2 rs1 4 rd).run js.sail

theorem amoswapwProgram_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js) :
    amoswapwProgramEqSailStatement rs2 rs1 rd js h := by
  unfold amoswapwProgramEqSailStatement
  exact amoswapwProgramAuto_eq_sail rs2 rs1 rd js h

end AtomicFamily

end
