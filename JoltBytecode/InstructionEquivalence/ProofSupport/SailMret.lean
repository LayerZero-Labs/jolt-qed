import JoltBytecode.InstructionEquivalence.Instructions.System.Common
import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.HartConfig

/-!
# Sail's MRET on Jolt's machine-mode hart

Closed forms for generated Sail's `execute_MRET` when the hart is in M-mode and
`mstatus.MPP` encodes M-mode, as it always does on Jolt's M-only hart.
Each lemma takes only the register facts its proof reads.
Based on Quang Dao's `Step/SailTrap.lean` in PR #73, which took a whole-step
invariant instead.
-/

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

noncomputable section
namespace Step

/-- The Sail state after writing register `r`.
For example, `setReg s Register.nextPC 16` makes the next PC 16. -/
def setReg (s : SailState) (r : Register) (v : RegisterType r) : SailState :=
  { s with regs := s.regs.insert r v }

/-- Sail's register write is `setReg`; for example, writing `mstatus`. -/
theorem writeReg_run (s : SailState) (r : Register) (v : RegisterType r) :
    (LeanRV64D.writeReg r v : SailM Unit) s = .ok () (setReg s r v) := rfl

/-- Writing one register leaves every other register unchanged.
For example, writing `mstatus` keeps `mepc`. -/
theorem setReg_get?_ne (s : SailState) {r r' : Register} (v : RegisterType r) (h : r ≠ r') :
    (setReg s r v).regs.get? r' = s.regs.get? r' :=
  System.extDHashMap_get?_insert_of_ne s.regs v h

/-- Writing an already-present value preserves the entire state.
For example, writing `Machine` to `cur_privilege` in an M-mode state is inert. -/
theorem setReg_eq_self (s : SailState) (r : Register) (v : RegisterType r)
    (h : s.regs.get? r = some v) : setReg s r v = s := by
  unfold setReg
  rw [System.extDHashMap_insert_eq_self_of_get? s.regs r v h]

private theorem setReg_overwrite (s : SailState) (r : Register)
    (v w : RegisterType r) : setReg (setReg s r v) r w = setReg s r w := by
  unfold setReg
  rw [System.extDHashMap_insert_insert_same]

private theorem readReg_setReg_self (s : SailState) (r : Register)
    (v : RegisterType r) :
    (LeanRV64D.readReg r : SailM (RegisterType r)) (setReg s r v) =
      .ok v (setReg s r v) := by
  apply readReg_eq_of_get?
  exact Std.ExtDHashMap.get?_insert_self

private theorem bind_run_ok {α β : Type} {f : SailM α} {g : α → SailM β}
    {s t : SailState} {a : α} (h : f s = .ok a t) : (f >>= g) s = g a t := by
  simp only [bind, EStateM.bind, h]

/-- MRET copies MPIE to MIE and sets MPIE and MPP to their M-only hart values,
preserving other bits; for example, `mretMstatus 0x1880 = 0x1888`. -/
def mretMstatus (m : BitVec 64) : BitVec 64 :=
  (m &&& ~~~(0x1888#64)) ||| ((m &&& 0x80#64) >>> 4) ||| 0x80#64 ||| 0x1800#64

private theorem update_getLsbD {w len : Nat} (x : BitVec w) (start i : Nat)
    (y : BitVec len) (hi : i < w) :
    (Sail.BitVec.updateSubrange' x start len y).getLsbD i =
      if start ≤ i ∧ i < start + len then y.getLsbD (i - start) else x.getLsbD i := by
  by_cases hs : i < start
  · simp [Sail.BitVec.updateSubrange', hi, hs, show ¬ start ≤ i from by omega]
  · have hsi : start ≤ i := by omega
    by_cases hl : i - start < len
    · simp [Sail.BitVec.updateSubrange', hi, hs, hl, hsi,
        show i < start + len from by omega]
    · simp [Sail.BitVec.updateSubrange', hi, hs, hl, hsi,
        show ¬ i < start + len from by omega,
        BitVec.getLsbD_of_ge y (i - start) (by omega : len ≤ i - start)]

private def mask (start len : Nat) : BitVec 64 := (BitVec.allOnes len).setWidth 64 <<< start

private theorem mask_getLsbD (start len i : Nat) (hi : i < 64) :
    (mask start len).getLsbD i = decide (start ≤ i ∧ i < start + len) := by
  simp only [mask, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  omega

private theorem mret_mstatus_bits (m : BitVec 64) :
    Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange
        (Sail.BitVec.updateSubrange m 3 3 (_get_Mstatus_MPIE m)) 7 7 (1#1))
      12 11 (3#2) = mretMstatus m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hspecial : i = 3 ∨ i = 7 ∨ i = 11 ∨ i = 12
  · rcases hspecial with h | h | h | h <;> subst i <;>
      simp [mretMstatus, Sail.BitVec.updateSubrange,
        Sail.BitVec.updateSubrange', _get_Mstatus_MPIE, Sail.BitVec.extractLsb]
  · have h3 : ¬(3 ≤ i ∧ i < 4) := by omega
    have h7 : ¬(7 ≤ i ∧ i < 8) := by omega
    have hpp : ¬(11 ≤ i ∧ i < 13) := by omega
    have h80 : (0x80#64) = mask 7 1 := rfl
    have h1800 : (0x1800#64) = mask 11 2 := rfl
    have h1888 : (0x1888#64) = mask 3 1 ||| mask 7 1 ||| mask 11 2 := rfl
    have hm80 : (0x80#64).getLsbD (4 + i) = false := by
      by_cases hp : 4 + i < 64
      · rw [h80, mask_getLsbD _ _ _ hp]
        simp only [show ¬(7 ≤ 4 + i ∧ 4 + i < 7 + 1) from by omega, decide_false]
      · exact BitVec.getLsbD_of_ge _ _ (by omega)
    have hright : ((m &&& 0x80#64) >>> 4).getLsbD i = false := by
      simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, hm80, Bool.and_false]
    have hmpie : (0x80#64).getLsbD i = false := by
      rw [h80, mask_getLsbD _ _ _ hi]
      simp [h7]
    have hmpp : (0x1800#64).getLsbD i = false := by
      rw [h1800, mask_getLsbD _ _ _ hi]
      simp [hpp]
    have hmask : (0x1888#64).getLsbD i = false := by
      rw [h1888]
      simp only [BitVec.getLsbD_or, mask_getLsbD _ _ _ hi]
      simp [h3, h7, hpp]
    simp only [mretMstatus, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, hmask, hmpp, hright, hmpie, hi, decide_true,
      Bool.not_false, Bool.and_true, Bool.or_false,
      Sail.BitVec.updateSubrange, update_getLsbD, h3, h7, hpp, ↓reduceIte]

private theorem saved_mpp_bits (m : BitVec 64)
    (hmpp : m &&& 0x1800#64 = 0x1800#64) :
    _get_Mstatus_MPP
      (Sail.BitVec.updateSubrange
        (Sail.BitVec.updateSubrange m 3 3 (_get_Mstatus_MPIE m)) 7 7 (1#1)) = 3#2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hw : 11 + i < 64 := by omega
  have hmask : (0x1800#64) = mask 11 2 := rfl
  have hmaskbit : (mask 11 2).getLsbD (11 + i) = true := by
    rw [mask_getLsbD _ _ _ hw]
    simp [show 11 ≤ 11 + i ∧ 11 + i < 11 + 2 from by omega]
  have hmBit : m.getLsbD (11 + i) = true := by
    have h := congrArg (fun x : BitVec 64 => x.getLsbD (11 + i)) hmpp
    simpa only [hmask, BitVec.getLsbD_and, hmaskbit, Bool.and_true] using h
  simp only [_get_Mstatus_MPP, Sail.BitVec.extractLsb, BitVec.getLsbD_extractLsb,
    show 12 - 11 + 1 = 2 from rfl, hi, decide_true, Bool.true_and,
    Sail.BitVec.updateSubrange]
  rw [update_getLsbD _ _ _ _ hw]
  simp only [show ¬(7 ≤ 11 + i ∧ 11 + i < 7 + (7 - 7 + 1)) from by omega, ↓reduceIte]
  rw [update_getLsbD _ _ _ _ hw]
  simp only [show ¬(3 ≤ 11 + i ∧ 11 + i < 3 + (3 - 3 + 1)) from by omega, ↓reduceIte]
  change m.getLsbD (11 + i) = (BitVec.allOnes 2).getLsbD i
  simp only [hmBit, BitVec.getLsbD_allOnes, hi, decide_true]

/-- Sail's `align_pc` reads only `misa`, so its result carries over to any
state with the same `misa`.
For example, an `mepc` that `align_pc` keeps before an `mstatus` write is
still kept after it. -/
theorem align_pc_of_misa {s t : SailState} {misa : BitVec 64}
    (hs : s.regs.get? Register.misa = some misa) (ht : t.regs.get? Register.misa = some misa)
    {e r : BitVec 64} (h : align_pc e s = .ok r s) : align_pc e t = .ok r t := by
  have hsupports : hartSupports extension.Ext_Zca = true := by simp [hartSupports]
  have hC : hartSupports extension.Ext_C = true := by
    simp [hartSupports, LeanRV64D.Functions.not, LeanRV64D.Functions.xlen]
  unfold align_pc currentlyEnabled at h ⊢
  unfold currentlyEnabled at h ⊢
  simp only [hsupports, hC, LeanRV64D.Functions.not, andM, toBool, bind,
    EStateM.bind, pure, EStateM.pure, readReg_eq_of_get? Register.misa s misa hs,
    readReg_eq_of_get? Register.misa t misa ht] at h ⊢
  split at h <;> split <;> simp_all <;> (simp only [EStateM.pure] at h ⊢; cases h; rfl)

/-- A successful `align_pc` reads `misa`, so `misa` is present.
For example, the bundle's mepc alignment fact implies that `misa` exists. -/
theorem misa_present_of_align_pc {s : SailState} {e r : BitVec 64}
    (h : align_pc e s = .ok r s) : ∃ m, s.regs.get? Register.misa = some m := by
  cases hm : s.regs.get? Register.misa with
  | some m => exact ⟨m, rfl⟩
  | none =>
    exfalso
    have hsupports : hartSupports extension.Ext_Zca = true := by simp [hartSupports]
    have hC : hartSupports extension.Ext_C = true := by
      simp [hartSupports, LeanRV64D.Functions.not, LeanRV64D.Functions.xlen]
    unfold align_pc currentlyEnabled at h
    unfold currentlyEnabled at h
    simp [hsupports, hC, LeanRV64D.Functions.not, andM, toBool, bind, EStateM.bind, pure,
      EStateM.pure, LeanRV64D.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg, hm, get,
      getThe, MonadStateOf.get, EStateM.get, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw] at h

/-- `align_pc`'s result carries over between states with the same `misa` lookup.
For example, the bundle's alignment fact on Jolt's Sail state holds on its projection. -/
theorem align_pc_transfer {s t : SailState}
    (hmisa : t.regs.get? Register.misa = s.regs.get? Register.misa)
    {e r : BitVec 64} (h : align_pc e s = .ok r s) : align_pc e t = .ok r t := by
  obtain ⟨m, hm⟩ := misa_present_of_align_pc h
  exact align_pc_of_misa hm (hmisa.trans hm) h

private theorem mret_handler_run (s : SailState) (m e misa pc : BitVec 64)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some m)
    (he : s.regs.get? Register.mepc = some e)
    (hmisa : s.regs.get? Register.misa = some misa)
    (halign : align_pc e s = .ok e s)
    (hmpp : m &&& 0x1800#64 = 0x1800#64) :
    exception_handler Privilege.Machine (.CTL_MRET ()) pc s =
      .ok e (setReg s Register.mstatus (mretMstatus m)) := by
  have hsame (v : BitVec 64) :
      setReg (setReg s Register.mstatus v) Register.cur_privilege Privilege.Machine =
        setReg s Register.mstatus v := by
    apply setReg_eq_self
    simpa [setReg_get?_ne] using hpriv
  have hpriv' (v : BitVec 64) :
      readReg Register.cur_privilege (setReg s Register.mstatus v) =
        .ok Privilege.Machine (setReg s Register.mstatus v) := by
    apply readReg_eq_of_get?
    simpa [setReg_get?_ne] using hpriv
  have hdecode (st : SailState) : privLevel_bits_forwards (3#2, 0#1) st =
      .ok Privilege.Machine st := by
    simp [privLevel_bits_forwards, pure, EStateM.pure]
  unfold exception_handler
  simp only [get_config_print_exception, HartConfig.hartSupports_Zicfilp,
    Bool.false_eq_true, ↓reduceIte]
  rw [bind_run_ok (readReg_eq_of_get? Register.cur_privilege s _ hpriv),
    bind_run_ok (readReg_eq_of_get? Register.mstatus s m hm),
    bind_run_ok (readReg_eq_of_get? Register.mstatus s m hm),
    bind_run_ok (writeReg_run ..), bind_run_ok (readReg_setReg_self ..),
    bind_run_ok (writeReg_run ..), bind_run_ok (readReg_setReg_self ..)]
  rw [saved_mpp_bits m hmpp]
  simp only [setReg_overwrite]
  rw [bind_run_ok (hdecode _)]
  rw [bind_run_ok (writeReg_run ..), hsame,
    bind_run_ok (readReg_setReg_self ..),
    bind_run_ok (HartConfig.currentlyEnabled_U_run _)]
  simp only [Bool.false_eq_true, ↓reduceIte, pure_bind,
    privLevel_to_bits, privLevel_bits_backwards]
  rw [bind_run_ok (writeReg_run ..)]
  simp only [setReg_overwrite, mret_mstatus_bits]
  rw [bind_run_ok (hpriv' _)]
  simp only [show bne Privilege.Machine Privilege.Machine = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  change (readReg Register.mstatus >>= _) (setReg s Register.mstatus (mretMstatus m)) = _
  rw [bind_run_ok (readReg_setReg_self ..),
    bind_run_ok (System.long_csr_write_callback_mstatus_run ..)]
  unfold prepare_xret_target get_xepc
  dsimp only
  have he' : readReg Register.mepc (setReg s Register.mstatus (mretMstatus m)) =
      .ok e (setReg s Register.mstatus (mretMstatus m)) := by
    apply readReg_eq_of_get?
    simpa [setReg_get?_ne] using he
  rw [bind_run_ok he']
  exact align_pc_of_misa hmisa (by simpa [setReg_get?_ne] using hmisa) halign

/-- MRET restores MIE from MPIE, sets MPIE and the saved privilege to M-only values,
and jumps to the saved PC while remaining in M-mode.
For example, `mstatus = 0x1880` and `mepc = 16` yield `mstatus = 0x1888`
and `nextPC = 16`; `hmpp` requires the saved privilege to encode M-mode. -/
theorem execute_MRET_machine (s : SailState) (m e misa pc : BitVec 64)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hpc : s.regs.get? Register.PC = some pc)
    (hm : s.regs.get? Register.mstatus = some m)
    (he : s.regs.get? Register.mepc = some e)
    (hmisa : s.regs.get? Register.misa = some misa)
    (halign : align_pc e s = .ok e s)
    (hmpp : m &&& 0x1800#64 = 0x1800#64) :
    execute_MRET () s =
      .ok RETIRE_SUCCESS (setReg (setReg s Register.mstatus (mretMstatus m)) Register.nextPC e) := by
  have hhandler := mret_handler_run s m e misa pc hpriv hm he hmisa halign hmpp
  unfold execute_MRET
  rw [bind_run_ok (readReg_eq_of_get? Register.cur_privilege s _ hpriv)]
  change (readReg Register.cur_privilege >>= _) s = _
  rw [bind_run_ok (readReg_eq_of_get? Register.cur_privilege s _ hpriv),
    bind_run_ok (readReg_eq_of_get? Register.PC s pc hpc), bind_run_ok hhandler]
  have hnext (st : SailState) : set_next_pc e st = .ok () (setReg st Register.nextPC e) := by
    simp only [set_next_pc, bind, EStateM.bind, writeReg_run, pure, EStateM.pure]
  rw [bind_run_ok (hnext _)]
  rfl

end Step
