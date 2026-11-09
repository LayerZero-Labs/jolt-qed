import JoltBytecode.InstructionEquivalence.Instructions.AtomicFamily.WordProgram

open LeanRV64D

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

noncomputable section
namespace AtomicFamily

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

/-- Order the comparison operands for min or max: `reverse = true` compares
old against new, so a true flag selects the new value for a maximum. -/
def amoWordSelectFlag (less : BitVec 64 → BitVec 64 → Bool) (reverse : Bool)
    (new old : BitVec 64) : Bool :=
  if reverse then less old new else less new old

/-- The arithmetic selection tail used by Jolt's `expand_amo_minmax_w` in
`crates/jolt-program/src/expand/memory/shared.rs`.
For example, a flag of one makes SUB/MUL/ADD select the architectural source. -/
def amoWordSelectLaneTail (new old take : JoltISA.VReg) (rs2 : regidx) : JoltISA.Program :=
  .instr (.SUB (.vreg new) (.xreg rs2) (.vreg old)) <|
  .instr (.MUL (.vreg new) (.vreg new) (.vreg take)) <|
  .instr (.ADD (.vreg new) (.vreg new) (.vreg old)) <|
  .done RETIRE_SUCCESS

/-- Execute the shared arithmetic tail for arbitrary registers.
For example, setting `flag` to zero preserves the old word as the result. -/
theorem amo_word_select_lane_tail_run
    (new old take : JoltISA.VReg) (rs2 : regidx) (js : SailJoltState)
    (newValue oldValue flag : BitVec 64)
    (hrs2 : rX_bits rs2 js.sail = .ok newValue js.sail)
    (hold : js.vregs old = oldValue) (hflag : js.vregs take = flag)
    (hnew : WritableVReg new) (hon : old ≠ new) (htn : take ≠ new) :
    JoltISA.Program.Run (amoWordSelectLaneTail new old take rs2) js
      (stateAfterVRegWrite
        (stateAfterVRegWrite (stateAfterVRegWrite js new (newValue - oldValue))
          new ((newValue - oldValue) * flag))
        new ((newValue - oldValue) * flag + oldValue)) := by
  let sub := stateAfterVRegWrite js new (newValue - oldValue)
  let mul := stateAfterVRegWrite sub new ((newValue - oldValue) * flag)
  have hsub := JoltISA.sub_run_vreg_xreg_vreg new rs2 old js newValue hrs2 hnew
  have hmul := JoltISA.mul_run_vreg_vreg_vreg new new take sub hnew
  have hadd := JoltISA.add_run_vreg_vreg_vreg new new old mul hnew
  simp only [hold] at hsub
  simp only [sub, stateAfterVRegWrite, ite_true, if_neg htn, hflag] at hmul
  simp only [mul, sub, stateAfterVRegWrite, ite_true, if_neg hon, hold] at hadd
  change (JoltISA.execProgram (.instr _ (.instr _ (.instr _ (.done RETIRE_SUCCESS))))).run js = _
  rw [JoltISA.execProgram_instr_run_retire _ _ _ _ hsub,
    JoltISA.execProgram_instr_run_retire _ _ _ _ hmul,
    JoltISA.execProgram_instr_run_retire _ _ _ _ hadd]
  rfl

/-- Extend the new word, compare it with the already extended old word, then
select through the shared arithmetic tail; for example, reverse SLTU gives unsigned max. -/
def amoWordSelectLaneMiddle (cmp : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (reverse : Bool) (rs2 rd : regidx) : JoltISA.Program :=
  let old := JoltISA.amoWordOldVRegFor rd
  let new := JoltISA.amoWordNewVRegFor rd
  let take := JoltISA.amoWordTakeVRegFor rd
  .instr (.VirtualSignExtendWord (.vreg new) (.xreg rs2)) <|
  .instr (cmp (.vreg take) (if reverse then .vreg old else .vreg new)
    (if reverse then .vreg new else .vreg old)) <|
  amoWordSelectLaneTail new old take rs2

/-- The select middle preserves the opened lane and computes either the new
source or the signed old word; for example, SLT with reversed operands gives max.
The comparison row is supplied once for either SLT or SLTU. -/
theorem amo_word_select_lane_middle_run
    (cmp : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (less : BitVec 64 → BitVec 64 → Bool)
    (hcmp : ∀ dst lhs rhs js, WritableVReg dst →
      (JoltISA.execInstr (cmp (.vreg dst) (.vreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS (stateAfterVRegWrite js dst
          (zero_extend (m := 64) (bool_to_bit (less (js.vregs lhs) (js.vregs rhs))))))
    (reverse : Bool) (rs2 rd : regidx) (js : SailJoltState)
    (newValue dwordValue laneValue : BitVec 64) (oldWord : BitVec 32)
    (hrs2 : rX_bits rs2 js.sail = .ok newValue js.sail)
    (hold : js.vregs (JoltISA.amoWordOldVRegFor rd) = sign_extend (m := 64) oldWord)
    (hdword : js.vregs (JoltISA.amoWordDwordVRegFor rd) = dwordValue)
    (hlane : js.vregs (JoltISA.amoWordLaneVRegFor rd) = laneValue) :
    ∃ after, AmoWordWindowStep rd (amoWordSelectLaneMiddle cmp reverse rs2 rd)
      (.vreg (JoltISA.amoWordNewVRegFor rd)) oldWord dwordValue laneValue
      (if amoWordSelectFlag less reverse
          (sign_extend (m := 64) (Sail.BitVec.extractLsb newValue 31 0 : BitVec 32))
          (sign_extend (m := 64) oldWord)
        then newValue else sign_extend (m := 64) oldWord) js after := by
  let old := JoltISA.amoWordOldVRegFor rd
  let new := JoltISA.amoWordNewVRegFor rd
  let take := JoltISA.amoWordTakeVRegFor rd
  let oldValue := sign_extend (m := 64) oldWord
  let extended := sign_extend (m := 64) (Sail.BitVec.extractLsb newValue 31 0 : BitVec 32)
  let selected := amoWordSelectFlag less reverse extended oldValue
  let flag := zero_extend (m := 64) (bool_to_bit selected)
  let ext := stateAfterVRegWrite js new extended
  let compared := stateAfterVRegWrite ext take flag
  have hon : old ≠ new := amo_word_register_ne rd 2 3 (by decide)
  have hnt : new ≠ take := amo_word_register_ne rd 3 4 (by decide)
  have hot : old ≠ take := amo_word_register_ne rd 2 4 (by decide)
  have hex := JoltISA.virtual_sign_extend_word_run_vreg_xreg new rs2 js newValue hrs2
    (amo_word_register_writable rd 3)
  have hcompare : (JoltISA.execInstr (cmp (.vreg take)
      (if reverse then .vreg old else .vreg new)
      (if reverse then .vreg new else .vreg old))).run ext = .ok RETIRE_SUCCESS compared := by
    have hrow := hcmp take (if reverse then old else new) (if reverse then new else old) ext
      (amo_word_register_writable rd 4)
    cases reverse <;>
      simpa [compared, ext, flag, selected, amoWordSelectFlag, stateAfterVRegWrite,
        hon, hold, old, oldValue, extended] using hrow
  have hprefix : JoltISA.Program.Run
      (.instr (.VirtualSignExtendWord (.vreg new) (.xreg rs2))
        (.instr (cmp (.vreg take) (if reverse then .vreg old else .vreg new)
          (if reverse then .vreg new else .vreg old)) (.done RETIRE_SUCCESS))) js compared := by
    change (JoltISA.execProgram _).run js = _
    rw [JoltISA.execProgram_instr_run_retire _ _ _ _ hex]
    change (JoltISA.execProgram (.instr _ (.done RETIRE_SUCCESS))).run ext = _
    rw [JoltISA.execProgram_instr_run_retire _ _ _ _ hcompare]
    rfl
  have htail := amo_word_select_lane_tail_run new old take rs2 compared newValue oldValue flag
    hrs2 (by simp [compared, ext, stateAfterVRegWrite, hot, hon, old, hold, oldValue])
    (by simp [compared, stateAfterVRegWrite]) (amo_word_register_writable rd 3) hon (Ne.symm hnt)
  refine ⟨_, hprefix.append htail, rfl, ?_, ?_, ?_, ?_⟩
  all_goals
    simp [compared, ext, stateAfterVRegWrite, new, take,
      show JoltISA.amoWordOldVRegFor rd ≠ JoltISA.amoWordNewVRegFor rd from hon,
      show JoltISA.amoWordOldVRegFor rd ≠ JoltISA.amoWordTakeVRegFor rd from hot,
      show JoltISA.amoWordDwordVRegFor rd ≠ JoltISA.amoWordNewVRegFor rd from
        amo_word_register_ne rd 0 3 (by decide),
      show JoltISA.amoWordDwordVRegFor rd ≠ JoltISA.amoWordTakeVRegFor rd from
        amo_word_register_ne rd 0 4 (by decide),
      show JoltISA.amoWordLaneVRegFor rd ≠ JoltISA.amoWordNewVRegFor rd from
        amo_word_register_ne rd 1 3 (by decide),
      show JoltISA.amoWordLaneVRegFor rd ≠ JoltISA.amoWordTakeVRegFor rd from
        amo_word_register_ne rd 1 4 (by decide),
      show JoltISA.amoWordNewVRegFor rd ≠ JoltISA.amoWordDwordVRegFor rd from
        amo_word_register_ne rd 3 0 (by decide),
      hold, hdword, hlane, flag, amo_word_select_value_of_bool, selected, oldValue,
      extended, JoltISA.readSrc, readVReg, EStateM.run, bind, EStateM.bind,
      get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]

/-- Shared equivalence proof for all four word selects.
The comparison row and its 32-bit selection identity determine the instance;
for example, reverse SLTU selects the unsigned maximum. -/
theorem amo_word_select_eq_sail
    (op : amoop) (cmp : JoltISA.Dst → JoltISA.Src → JoltISA.Src → JoltISA.Instr)
    (less : BitVec 64 → BitVec 64 → Bool) (reverse : Bool)
    (hcmp : ∀ dst lhs rhs js, WritableVReg dst →
      (JoltISA.execInstr (cmp (.vreg dst) (.vreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS (stateAfterVRegWrite js dst
          (zero_extend (m := 64) (bool_to_bit (less (js.vregs lhs) (js.vregs rhs))))))
    (hselect : ∀ (new : BitVec 64) (old : BitVec 32),
      (if amoWordSelectFlag less reverse
          (sign_extend (m := 64) (Sail.BitVec.extractLsb new 31 0 : BitVec 32))
          (sign_extend (m := 64) old)
        then (Sail.BitVec.extractLsb new 31 0 : BitVec 32) else old) =
      amoWordSailResult op (Sail.BitVec.extractLsb new 31 0) old)
    (hnot_cas : (op == amoop.AMOCAS) = false)
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (h : AmoWordProgramEqSailAssumptions op rs2 rs1 rd js)
    (hprotected : JoltISA.ProgramWritesNoProtectedVReg
      (amoWordWindowProgram (amoWordSelectLaneMiddle cmp reverse rs2 rd)
        (.vreg (JoltISA.amoWordNewVRegFor rd)) rs1 rd)) :
    System.systemProjectResult
      ((JoltISA.execProgram (amoWordWindowProgram (amoWordSelectLaneMiddle cmp reverse rs2 rd)
        (.vreg (JoltISA.amoWordNewVRegFor rd)) rs1 rd)).run js) =
      (execute_AMO op false false rs2 rs1 4 rd).run js.sail := by
  apply amo_word_program_eq_sail op _ rs2 rs1 rd js h hnot_cas hprotected
  · intro halign
    let old := amoWordBundleOld op rs2 rs1 rd js h
    let selected := amoWordSelectFlag less reverse
      (sign_extend (m := 64) (Sail.BitVec.extractLsb h.rs2_val 31 0 : BitVec 32))
      (sign_extend (m := 64) old)
    obtain ⟨jsf, hrun, hfinal⟩ := amo_word_window_program_aligned_run
      (amoWordSelectLaneMiddle cmp reverse rs2 rd) (.vreg (JoltISA.amoWordNewVRegFor rd))
      rs1 rd js h.rs1_val (if selected then h.rs2_val else sign_extend (m := 64) old)
      h.rs1_read (Assumptions.DwordPresent.memBytesPresentAt h.dword_present)
      (by simpa using h.not_readable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega))
      (by simpa using h.not_writable_mmio.subaccess (offset := 0) (accessWidth := 8) (by omega))
      halign h.jolt_ram_load h.jolt_ram_store
      (by intro pre hsail hdword hlane hold
          exact amo_word_select_lane_middle_run cmp less hcmp reverse rs2 rd pre h.rs2_val
            _ _ _ (by rw [hsail]; exact h.rs2_read) hold hdword hlane)
    refine ⟨jsf, hrun, ?_⟩
    have hlow : (Sail.BitVec.extractLsb (sign_extend (m := 64) old) 31 0 : BitVec 32) = old :=
      sign_extend_64_setWidth_32 old
    rw [amo_word_extract_select_result, hlow] at hfinal
    simpa only [selected, hselect] using! hfinal
  · intro halign
    exact amo_word_pre64_with_scratch_misaligned_run rs1 _ _ _ _ js h.rs1_val h.rs1_read halign

end AtomicFamily
end
