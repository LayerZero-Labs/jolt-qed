import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.Word
import JoltBytecode.JoltISA.ExpansionsAutomated

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
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


/-- Rust-shaped `AMOSWAP.W` prelude with the allocator order
`v_mask`, `v_dword`, `v_shift`, `v_rd`. -/
theorem amo_word_swap_pre64_aligned_run
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
        (JoltISA.amoPre64ProgramWithScratch rs1 JoltISA.amoWordSwapOldVReg
          JoltISA.amoWordSwapDwordVReg JoltISA.amoWordSwapShiftVReg
          JoltISA.amoWordSwapInlineTmpVReg tail)).run js =
        (JoltISA.execProgram tail).run js_pre ∧
      js_pre.sail = js.sail ∧
      js_pre.vregs JoltISA.amoWordSwapDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf ∧
      js_pre.vregs JoltISA.amoWordSwapShiftVReg =
        shift_bits_left addr (3 : BitVec 6) ∧
      js_pre.vregs JoltISA.amoWordSwapOldVReg =
        amoWordShiftedOld addr
          (loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf) := by
  have hassert :=
    amo_word_virtual_assert_aligned_run rs1 js addr hrs1 h_align
  obtain ⟨js_base, _hrs1_base, hbase_sail, hbase_shift_raw,
      _hbase_preserves, hbase_run⟩ :=
    JoltISA.exists_state_after_andi_run_vreg_xreg_of_sail_eq
      JoltISA.amoWordSwapShiftVReg rs1 (-8 : BitVec 12)
      js js.sail addr rfl hrs1 (by unfold WritableVReg; decide)
  have hbase_shift :
      js_base.vregs JoltISA.amoWordSwapShiftVReg = amoWordBase addr := by
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
        (.LD .amo (.vreg JoltISA.amoWordSwapDwordVReg)
          (.vreg JoltISA.amoWordSwapShiftVReg) (0 : BitVec 12))).run js_base =
        .ok RETIRE_SUCCESS
          { sail := js_base.sail
            vregs := fun r =>
              if r = JoltISA.amoWordSwapDwordVReg then
                loaded_dword_at js_base.sail (amoWordBase addr)
                  hbytes_base h_no_ovf
              else js_base.vregs r } := by
    exact
      vreg_LD_run_of_aligned_dword_phys
        JoltISA.amoWordSwapDwordVReg JoltISA.amoWordSwapShiftVReg js_base
        (amoWordBase addr) hbase_shift
        hpriv_base hmprv_base
        (amo_word_base_aligned_access addr h_no_ovf)
        hbytes_base hload_pmp_base hread_mmio_base
        (by unfold WritableVReg; decide)
  let js_load : SailJoltState :=
    { sail := js_base.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSwapDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
            hbytes_base h_no_ovf
        else js_base.vregs r }
  have hld_named :
      (JoltISA.execInstr
        (.LD .amo (.vreg JoltISA.amoWordSwapDwordVReg)
          (.vreg JoltISA.amoWordSwapShiftVReg) (0 : BitVec 12))).run js_base =
        .ok RETIRE_SUCCESS js_load := by
    exact hld
  have hload_sail : js_load.sail = js.sail := by
    exact hbase_sail
  have hload_dword :
      js_load.vregs JoltISA.amoWordSwapDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf := by
    change
      (if JoltISA.amoWordSwapDwordVReg = JoltISA.amoWordSwapDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
            hbytes_base h_no_ovf
        else js_base.vregs JoltISA.amoWordSwapDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf
    rw [if_pos rfl]
    unfold loaded_dword_at loaded_byte_at loaded_byte_at_nat
    simp [hbase_sail]
  have hload_shift :
      js_load.vregs JoltISA.amoWordSwapShiftVReg = amoWordBase addr := by
    change
      (if JoltISA.amoWordSwapShiftVReg = JoltISA.amoWordSwapDwordVReg then
          loaded_dword_at js_base.sail (amoWordBase addr)
            hbytes_base h_no_ovf
        else js_base.vregs JoltISA.amoWordSwapShiftVReg) =
        amoWordBase addr
    rw [if_neg (by decide)]
    exact hbase_shift
  have hrs1_load :
      rX_bits rs1 js_load.sail = .ok addr js_load.sail := by
    rw [hload_sail]
    exact hrs1
  have hmuli :
      (JoltISA.execInstr
        (.VirtualMULI (.vreg JoltISA.amoWordSwapShiftVReg)
          (.xreg rs1) (8 : BitVec 64))).run js_load =
      .ok RETIRE_SUCCESS
        { sail := js_load.sail
          vregs := fun r =>
            if r = JoltISA.amoWordSwapShiftVReg then
              jolt_virtual_muli_value addr (8 : BitVec 64)
            else js_load.vregs r } :=
    amo_word_virtual_muli_run_vreg_xreg
      JoltISA.amoWordSwapShiftVReg rs1 (8 : BitVec 64) js_load addr hrs1_load
      (by unfold WritableVReg; decide)
  let js_shift : SailJoltState :=
    { sail := js_load.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSwapShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs r }
  have hmuli_named :
      (JoltISA.execInstr
        (.VirtualMULI (.vreg JoltISA.amoWordSwapShiftVReg)
          (.xreg rs1) (8 : BitVec 64))).run js_load =
      .ok RETIRE_SUCCESS js_shift := by
    exact hmuli
  have hshift_sail : js_shift.sail = js.sail := by
    exact hload_sail
  have hshift_dword :
      js_shift.vregs JoltISA.amoWordSwapDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf := by
    change
      (if JoltISA.amoWordSwapDwordVReg = JoltISA.amoWordSwapShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs JoltISA.amoWordSwapDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf
    rw [if_neg (by decide)]
    exact hload_dword
  have hshift_shift :
      js_shift.vregs JoltISA.amoWordSwapShiftVReg =
        shift_bits_left addr (3 : BitVec 6) := by
    change
      (if JoltISA.amoWordSwapShiftVReg = JoltISA.amoWordSwapShiftVReg then
          jolt_virtual_muli_value addr (8 : BitVec 64)
        else js_load.vregs JoltISA.amoWordSwapShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_pos rfl]
    exact JoltISA.virtual_muli_eight_eq_shift_left_three addr
  have hbitmask :
      (JoltISA.execInstr
        (.VirtualShiftRightBitmask (.vreg JoltISA.amoWordSwapInlineTmpVReg)
          (.vreg JoltISA.amoWordSwapShiftVReg))).run js_shift =
      .ok RETIRE_SUCCESS
        { sail := js_shift.sail
          vregs := fun r =>
            if r = JoltISA.amoWordSwapInlineTmpVReg then
              jolt_virtual_shift_right_bitmask_value
                (js_shift.vregs JoltISA.amoWordSwapShiftVReg)
            else js_shift.vregs r } :=
    JoltISA.virtual_shift_right_bitmask_run_vreg_vreg
      JoltISA.amoWordSwapInlineTmpVReg JoltISA.amoWordSwapShiftVReg js_shift
      (by unfold WritableVReg; decide)
  let js_bitmask : SailJoltState :=
    { sail := js_shift.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSwapInlineTmpVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSwapShiftVReg)
        else js_shift.vregs r }
  have hbitmask_named :
      (JoltISA.execInstr
        (.VirtualShiftRightBitmask (.vreg JoltISA.amoWordSwapInlineTmpVReg)
          (.vreg JoltISA.amoWordSwapShiftVReg))).run js_shift =
      .ok RETIRE_SUCCESS js_bitmask := by
    exact hbitmask
  have hbitmask_sail : js_bitmask.sail = js.sail := by
    exact hshift_sail
  have hbitmask_dword :
      js_bitmask.vregs JoltISA.amoWordSwapDwordVReg =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf := by
    change
      (if JoltISA.amoWordSwapDwordVReg = JoltISA.amoWordSwapInlineTmpVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSwapShiftVReg)
        else js_shift.vregs JoltISA.amoWordSwapDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf
    rw [if_neg (by decide)]
    exact hshift_dword
  have hbitmask_shift :
      js_bitmask.vregs JoltISA.amoWordSwapShiftVReg =
        shift_bits_left addr (3 : BitVec 6) := by
    change
      (if JoltISA.amoWordSwapShiftVReg = JoltISA.amoWordSwapInlineTmpVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSwapShiftVReg)
        else js_shift.vregs JoltISA.amoWordSwapShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_neg (by decide)]
    exact hshift_shift
  have hbitmask_tmp :
      js_bitmask.vregs JoltISA.amoWordSwapInlineTmpVReg =
        jolt_virtual_shift_right_bitmask_value
          (shift_bits_left addr (3 : BitVec 6)) := by
    change
      (if JoltISA.amoWordSwapInlineTmpVReg = JoltISA.amoWordSwapInlineTmpVReg then
          jolt_virtual_shift_right_bitmask_value
            (js_shift.vregs JoltISA.amoWordSwapShiftVReg)
        else js_shift.vregs JoltISA.amoWordSwapInlineTmpVReg) =
        jolt_virtual_shift_right_bitmask_value
          (shift_bits_left addr (3 : BitVec 6))
    rw [if_pos rfl, hshift_shift]
  have hsrl :
      (JoltISA.execInstr
        (.VirtualSRL (.vreg JoltISA.amoWordSwapOldVReg)
          (.vreg JoltISA.amoWordSwapDwordVReg)
          (.vreg JoltISA.amoWordSwapInlineTmpVReg))).run js_bitmask =
      .ok RETIRE_SUCCESS
        { sail := js_bitmask.sail
          vregs := fun r =>
            if r = JoltISA.amoWordSwapOldVReg then
              jolt_virtual_srl_value
                (js_bitmask.vregs JoltISA.amoWordSwapDwordVReg)
                (js_bitmask.vregs JoltISA.amoWordSwapInlineTmpVReg)
            else js_bitmask.vregs r } :=
    JoltISA.virtual_srl_run_vreg_vreg_vreg
      JoltISA.amoWordSwapOldVReg JoltISA.amoWordSwapDwordVReg
      JoltISA.amoWordSwapInlineTmpVReg js_bitmask
      (by unfold WritableVReg; decide)
  let js_pre : SailJoltState :=
    { sail := js_bitmask.sail
      vregs := fun r =>
        if r = JoltISA.amoWordSwapOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSwapDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSwapInlineTmpVReg)
        else js_bitmask.vregs r }
  have hsrl_named :
      (JoltISA.execInstr
        (.VirtualSRL (.vreg JoltISA.amoWordSwapOldVReg)
          (.vreg JoltISA.amoWordSwapDwordVReg)
          (.vreg JoltISA.amoWordSwapInlineTmpVReg))).run js_bitmask =
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
      (if JoltISA.amoWordSwapDwordVReg = JoltISA.amoWordSwapOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSwapDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSwapInlineTmpVReg)
        else js_bitmask.vregs JoltISA.amoWordSwapDwordVReg) =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf
    rw [if_neg (by decide)]
    exact hbitmask_dword
  · change
      (if JoltISA.amoWordSwapShiftVReg = JoltISA.amoWordSwapOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSwapDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSwapInlineTmpVReg)
        else js_bitmask.vregs JoltISA.amoWordSwapShiftVReg) =
        shift_bits_left addr (3 : BitVec 6)
    rw [if_neg (by decide)]
    exact hbitmask_shift
  · change
      (if JoltISA.amoWordSwapOldVReg = JoltISA.amoWordSwapOldVReg then
          jolt_virtual_srl_value
            (js_bitmask.vregs JoltISA.amoWordSwapDwordVReg)
            (js_bitmask.vregs JoltISA.amoWordSwapInlineTmpVReg)
        else js_bitmask.vregs JoltISA.amoWordSwapOldVReg) =
        amoWordShiftedOld addr
          (loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf)
    rw [if_pos rfl, hbitmask_dword, hbitmask_tmp]
    exact
      JoltISA.virtual_srl_shift_right_bitmask_value_eq
        (loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf)
        (shift_bits_left addr (3 : BitVec 6))

/-- Selected-register version of `amo_word_swap_pre64_aligned_run`, matching
Rust's `rd`-dependent allocator order for `AMOSWAP.W`. -/
theorem amo_word_swap_pre64_aligned_run_for
    (rd : regidx) (tail : JoltISA.Program)
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
        (JoltISA.amoPre64ProgramWithScratch rs1
          (JoltISA.amoWordSwapOldVRegFor rd)
          (JoltISA.amoWordSwapDwordVRegFor rd)
          (JoltISA.amoWordSwapShiftVRegFor rd)
          (JoltISA.amoWordSwapInlineTmpVRegFor rd) tail)).run js =
        (JoltISA.execProgram tail).run js_pre ∧
      js_pre.sail = js.sail ∧
      js_pre.vregs (JoltISA.amoWordSwapDwordVRegFor rd) =
        loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf ∧
      js_pre.vregs (JoltISA.amoWordSwapShiftVRegFor rd) =
        shift_bits_left addr (3 : BitVec 6) ∧
      js_pre.vregs (JoltISA.amoWordSwapOldVRegFor rd) =
        amoWordShiftedOld addr
          (loaded_dword_at js.sail (amoWordBase addr) hbytes h_no_ovf) := by
  exact
    amo_word_pre64_aligned_run_with rs1
      (JoltISA.amoWordSwapOldVRegFor rd)
      (JoltISA.amoWordSwapDwordVRegFor rd)
      (JoltISA.amoWordSwapShiftVRegFor rd)
      (JoltISA.amoWordSwapInlineTmpVRegFor rd)
      tail js hpriv hmprv addr hrs1 hbytes hload_pmp hread_mmio h_no_ovf
      h_align
      (by
        unfold JoltISA.amoWordSwapShiftVRegFor JoltISA.amoVRegFor WritableVReg
        split <;> decide)
      (by
        unfold JoltISA.amoWordSwapDwordVRegFor JoltISA.amoVRegFor WritableVReg
        split <;> decide)
      (by
        unfold JoltISA.amoWordSwapInlineTmpVRegFor JoltISA.amoVRegFor
          WritableVReg
        split <;> decide)
      (by
        unfold JoltISA.amoWordSwapOldVRegFor JoltISA.amoVRegFor WritableVReg
        split <;> decide)
      (by
        unfold JoltISA.amoWordSwapShiftVRegFor JoltISA.amoWordSwapDwordVRegFor
          JoltISA.amoVRegFor
        split <;> decide)
      (by
        unfold JoltISA.amoWordSwapDwordVRegFor
          JoltISA.amoWordSwapInlineTmpVRegFor JoltISA.amoVRegFor
        split <;> decide)
      (by
        unfold JoltISA.amoWordSwapShiftVRegFor
          JoltISA.amoWordSwapInlineTmpVRegFor JoltISA.amoVRegFor
        split <;> decide)
      (by
        unfold JoltISA.amoWordSwapDwordVRegFor JoltISA.amoWordSwapOldVRegFor
          JoltISA.amoVRegFor
        split <;> decide)
      (by
        unfold JoltISA.amoWordSwapShiftVRegFor JoltISA.amoWordSwapOldVRegFor
          JoltISA.amoVRegFor
        split <;> decide)

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
          (.instr (.ORI (.vreg JoltISA.amoWordSwapMaskVReg)
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
          (.instr (.ORI (.vreg (JoltISA.amoWordSwapMaskVRegFor rd))
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
            (.vreg JoltISA.amoWordSwapShiftVReg)) <|
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
            (.vreg (JoltISA.amoWordSwapShiftVRegFor rd))) <|
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
            (.vreg JoltISA.amoWordSwapShiftVReg)) <|
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
            (.vreg (JoltISA.amoWordSwapShiftVRegFor rd))) <|
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
          (.instr (.ANDI (.vreg JoltISA.amoWordSwapMaskVReg)
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
          (.instr (.ANDI (.vreg (JoltISA.amoWordSwapMaskVRegFor rd))
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
    (h_old : js.vregs JoltISA.amoWordSwapOldVReg = old) :
    ∃ js',
      js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
      js'.vregs JoltISA.amoWordSwapOldVReg = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.SD (.vreg JoltISA.amoWordSwapMaskVReg)
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
    { sail := state_after_dword_store s (amoWordBase addr) dwordNew
      vregs := js.vregs }
  have hsd_align :
      (js.vregs JoltISA.amoWordSwapMaskVReg +
          sign_extend (m := 64) (0 : BitVec 12)) &&& (7 : BitVec 64) = 0 := by
    rw [h_base, amo_word_zero_offset_addr (amoWordBase addr)]
    exact amo_word_base_aligned addr
  have hsd :
      (JoltISA.execInstr
        (.SD (.vreg JoltISA.amoWordSwapMaskVReg)
          (.vreg JoltISA.amoWordSwapDwordVReg) (0 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS js' :=
    JoltISA.execInstr_sd_vreg_run_of_write
      JoltISA.amoWordSwapMaskVReg JoltISA.amoWordSwapDwordVReg (0 : BitVec 12)
      js (state_after_dword_store s (amoWordBase addr) dwordNew)
      hsd_align hwrite_current
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
    (h_old : js.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old) :
    ∃ js',
      js'.sail = state_after_dword_store s (amoWordBase addr) dwordNew ∧
      js'.vregs (JoltISA.amoWordSwapOldVRegFor rd) = old ∧
      ∀ tail,
        (JoltISA.execProgram
          (.instr (.SD (.vreg (JoltISA.amoWordSwapMaskVRegFor rd))
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
        31 0 : BitVec 32) = oldWord) :
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
  obtain ⟨js_store, hstore_sail, hstore_old, hstore_tail⟩ :=
    amo_word_swap_sd_spliced_dword_run js_store_base js.sail addr dwordNew old
      hpriv hmprv hstore_pmp hwrite_mmio h_no_ovf hstore_base_sail
      hstore_base hstore_base_dword hstore_base_old
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
        31 0 : BitVec 32) = oldWord) :
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
  obtain ⟨js_store, hstore_sail, hstore_old, hstore_tail⟩ :=
    amo_word_swap_sd_spliced_dword_run_for rd js_store_base js.sail addr
      dwordNew old hpriv hmprv hstore_pmp hwrite_mmio h_no_ovf
      hstore_base_sail hstore_base hstore_base_dword hstore_base_old
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

/-- Jolt-side aligned concrete execution for `AMOSWAP.W`. -/
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
  have h_no_ovf := amo_word_base_no_ovf addr
  let post :=
    JoltISA.amoPost64ProgramWithScratch rs1 rd (.xreg rs2)
      (JoltISA.amoWordSwapDwordVRegFor rd)
      (JoltISA.amoWordSwapShiftVRegFor rd)
      (JoltISA.amoWordSwapMaskVRegFor rd)
      (JoltISA.amoWordSwapOldVRegFor rd)
      (JoltISA.amoWordSwapInlineTmpVRegFor rd)
  obtain ⟨js_pre, hpre_run, hpre_sail, hpre_dword, hpre_shift, hpre_old⟩ :=
    amo_word_swap_pre64_aligned_run_for rd post rs1 js hpriv hmprv addr hrs1
      hbytes_base hload_pmp hread_mmio h_no_ovf h_align
  obtain ⟨jsf, hpost_run, hpost_sail⟩ :=
    amo_word_swap_post64_amoswap_aligned_run_for rs2 rs1 rd js js_pre
      hpriv hmprv addr rs2Val oldWord hrs1 hrs2 hbytes_base hstore_pmp
      hwrite_mmio h_no_ovf h_align hpre_sail hpre_dword hpre_shift
      hpre_old (by simpa [h_no_ovf] using hold)
  refine ⟨jsf, ?_, hpost_sail⟩
  have hslli3 :
      JoltISA.slliMultiplier (3 : BitVec 6) = (8 : BitVec 64) := by
    rfl
  cases hrd : JoltISA.isX0 rd
  all_goals
    simp only [JoltISA.amoswapwProgramAuto, hrd,
      Bool.false_eq_true, if_false, if_true,
      post, JoltISA.amoPre64ProgramWithScratch,
      JoltISA.amoPost64ProgramWithScratch,
      JoltISA.amoWordSwapMaskVRegFor,
      JoltISA.amoWordSwapDwordVRegFor,
      JoltISA.amoWordSwapShiftVRegFor,
      JoltISA.amoWordSwapOldVRegFor,
      JoltISA.amoWordSwapInlineTmpVRegFor,
      JoltISA.amoVRegFor, JoltISA.amoDstFor,
      JoltISA.sideEffectingRdZeroDst, JoltISA.rdZeroRewriteVReg,
      JoltISA.inlineTmp, JoltISA.inlineRegisterBase,
      JoltISA.riscvRegisterBase, JoltISA.riscvRegisterCount,
      JoltISA.numReservedVirtualRegisters, hslli3] at hpre_run hpost_run ⊢
    rw [hpre_run]
    exact hpost_run

/-- Main public theorem for `AMOSWAP.W`.

The theorem takes one primitive-only atomic bundle. Exact memory facts are
derived internally from that bundle. -/
private theorem amoswapwProgramAuto_eq_sail
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions amoop.AMOSWAP rs2 rs1 rd js) :
    System.systemProjectResult
      ((JoltISA.execProgram (JoltISA.amoswapwProgramAuto rd rs1 rs2)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 4 rd).run js.sail := by
  let addr := h.rs1_val
  let rs2Val := h.rs2_val
  by_cases h_align : addr &&& (3 : BitVec 64) = 0
  · let base := amoWordBase addr
    let offset := (addr &&& (7 : BitVec 64)).toNat
    have hbase_no_ovf := amo_word_base_no_ovf addr
    have hbytes_base : MemBytesPresentAt js.sail (amoWordBase addr) 8 := by
      simpa [addr] using Assumptions.DwordPresent.memBytesPresentAt h.dword_present
    have hload_pmp_base : Assumptions.LoadPmpOk (amoWordBase addr) 8 js.sail := by
      simpa [addr] using h.load_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
    have hstore_pmp_base : Assumptions.StorePmpOk (amoWordBase addr) 8 js.sail := by
      simpa [addr] using h.store_pmp.subaccess (offset := 0) (accessWidth := 8) (by omega)
    have hread_mmio_base :
        Assumptions.NotReadableMmio (amoWordBase addr) 8 js.sail := by
      simpa [addr] using
        h.not_readable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega)
    have hwrite_mmio_base :
        Assumptions.NotWritableMmio (amoWordBase addr) 8 js.sail := by
      simpa [addr] using
        h.not_writable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega)
    have hoff : offset + 4 ≤ 8 := by
      have hcases := write_word_offset_cases addr h_align
      rcases hcases with h0 | h4
      · simp [offset, h0]
      · simp [offset, h4]
    have haddr : base + BitVec.ofNat 64 offset = addr := by
      simpa [base, offset, amoWordBase] using addr_split_aligned_offset addr
    have hbytes_word : MemBytesPresentAt js.sail addr 4 := by
      have hsub : MemBytesPresentAt js.sail (base + BitVec.ofNat 64 offset) 4 :=
        memBytesPresentAt_subaccess (s := js.sail) (base := base) (baseWidth := 8)
          (offset := offset) (accessWidth := 4)
          (by simpa [base] using hbytes_base) hoff (by
            have hb : base.toNat + 7 < 2 ^ 64 := by
              simpa [base] using hbase_no_ovf
            omega)
      simpa [haddr] using hsub
    have hatomic_pmp_word :
        Assumptions.AtomicPmpOk amoop.AMOSWAP addr 4 js.sail := by
      have hsub :
          Assumptions.AtomicPmpOk amoop.AMOSWAP
            (base + BitVec.ofNat 64 offset) 4 js.sail :=
        h.atomic_pmp.subaccess (offset := offset) (accessWidth := 4) hoff
      simpa [addr, base, haddr] using hsub
    have hread_mmio_word : Assumptions.NotReadableMmio addr 4 js.sail := by
      have hsub :
          Assumptions.NotReadableMmio (base + BitVec.ofNat 64 offset) 4 js.sail :=
        h.not_readable_mmio.subaccess (offset := offset) (accessWidth := 4) hoff
      simpa [addr, base, haddr] using hsub
    have hwrite_mmio_word : Assumptions.NotWritableMmio addr 4 js.sail := by
      have hsub :
          Assumptions.NotWritableMmio (base + BitVec.ofNat 64 offset) 4 js.sail :=
        h.not_writable_mmio.subaccess (offset := offset) (accessWidth := 4) hoff
      simpa [addr, base, haddr] using hsub
    have h_word_no_ovf : addr.toNat + 3 < 2 ^ 64 :=
      amo_word_aligned_no_ovf addr hbase_no_ovf h_align
    let dword : BitVec 64 :=
      loaded_dword_at js.sail (amoWordBase addr) hbytes_base hbase_no_ovf
    let oldWord : BitVec 32 := loaded_word_at js.sail addr hbytes_word h_word_no_ovf
    have hold :
        (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
          BitVec 32) = oldWord := by
      have hword_of_dword :
          (Sail.BitVec.extractLsb (amoWordShiftedOld addr dword) 31 0 :
            BitVec 32) =
          word_of_dword dword (addr &&& (7 : BitVec 64)).toNat := by
        apply amo_word_sign_extend_64_injective
        simpa [amoWordShiftedOld] using
          srl_sign_extend_word_extracts_word dword addr h_align
      have hloaded :
          oldWord = word_of_dword dword (addr &&& (7 : BitVec 64)).toNat := by
        unfold oldWord dword
        simpa [amoWordBase] using
          loaded_word_in_dword js.sail addr h_align
            hbytes_base hbase_no_ovf hbytes_word h_word_no_ovf
      rw [hword_of_dword, ← hloaded]
    rcases
        amoswapwProgram_concrete_aligned
          rs2 rs1 rd js h.cur_privilege h.mstatus_mprv addr rs2Val oldWord
          h.rs1_read h.rs2_read hbytes_base hload_pmp_base hread_mmio_base
          hstore_pmp_base hwrite_mmio_base h_align
          (by simpa [dword] using hold) with
      ⟨jsf, hjolt, hjolt_sail⟩
    have hsail :=
      execute_AMO_word_non_cas_aligned
        amoop.AMOSWAP rs2 rs1 rd js h.cur_privilege h.mstatus_mprv
        addr rs2Val (Sail.BitVec.extractLsb rs2Val 31 0)
        h.rs1_read h.rs2_read h.rdReadable.exists_value
        hbytes_word hatomic_pmp_word hread_mmio_word hwrite_mmio_word
        h_align (by decide) (by
          rw [amo_word_trunc_4x8_eq_extract])
    have hprojected : Projection.ProjectedVRegsPreserved js jsf :=
      Projection.execProgram_preserves_projected_vregs_of_no_protected_writes
        (amoswapwProgram_doesNotWriteProtectedVRegs rs2 rs1 rd) hjolt
    have hprojectFinal : System.systemProject jsf = jsf.sail := by
      exact Projection.systemProject_eq_sail_of_memory_update_then_write
        js jsf _ rd _ hjolt_sail rfl hprojected h.linkedCSRs
    rw [hjolt]
    rw [hsail]
    simp only [System.systemProjectResult]
    rw [hprojectFinal, hjolt_sail]
  · have hjolt :
        (JoltISA.execProgram (JoltISA.amoswapwProgramAuto rd rs1 rs2)).run js =
          .ok (ExecutionResult.Memory_Exception
            (Virtaddr addr, ExceptionType.E_SAMO_Addr_Align ())) js := by
      unfold JoltISA.amoswapwProgramAuto
      cases hrd : JoltISA.isX0 rd <;>
        simp only [Bool.false_eq_true, if_false, if_true] <;>
        exact amo_word_assert_prefix_misaligned_run
          rs1 _ js addr h.rs1_read h_align
    have hsail :=
      execute_AMO_word_misaligned
        amoop.AMOSWAP rs2 rs1 rd js addr rs2Val
        h.rs1_read h.rs2_read h_align
    rw [hjolt]
    rw [hsail]
    simp only [System.systemProjectResult]
    congr 1
    exact Projection.systemProject_eq_sail_of_compatible js h.linkedCSRs

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
