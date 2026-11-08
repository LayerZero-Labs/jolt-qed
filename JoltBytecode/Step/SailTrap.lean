import JoltBytecode.Step.TryStep

/-!
# Sail ECALL trap entry and MRET on Jolt's M-mode hart

These closed forms include the generated trap-handler writes and the
non-retiring step tail.
MRET requires the saved privilege bits `mstatus.MPP` to encode M-mode.
-/

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

noncomputable section
namespace Step

/-- Trap entry copies MIE to MPIE, clears MIE, and sets MPP to M-mode,
preserving other bits; for example, `trapMstatus 8 = 0x1880`. -/
def trapMstatus (m : BitVec 64) : BitVec 64 :=
  (m &&& ~~~(0x1888#64)) ||| ((m &&& 0x8#64) <<< 4) ||| 0x1800#64

/-- MRET copies MPIE to MIE and sets MPIE and MPP to their M-only hart values,
preserving other bits; for example, `mretMstatus 0x1880 = 0x1888`. -/
def mretMstatus (m : BitVec 64) : BitVec 64 :=
  (m &&& ~~~(0x1888#64)) ||| ((m &&& 0x80#64) >>> 4) ||| 0x80#64 ||| 0x1800#64

/-- ECALL in M-mode raises the machine environment-call exception,
with no extra information; its numeric exception code is 11. -/
def ecallException : sync_exception :=
  { trap := .E_M_EnvCall (), excinfo := none, ext := none }

/-- ECALL trap-entry writes at address `pc`, starting with `mstatus = m`.
For example, `mepc` becomes `pc`, `mcause` becomes 11 and `mtval` becomes zero. -/
def ecallState (s : SailState) (m pc : BitVec 64) : SailState :=
  setReg (setReg (setReg (setReg s Register.mcause 11#64) Register.mstatus (trapMstatus m))
    Register.mtval 0#64) Register.mepc pc

/-- Finish a handled trap without retiring an instruction.
A waiting hart returns `true`; an active hart advances PC and returns `false`,
leaving `minstret` unchanged. -/
def trapFinish : SailM Bool := do
  match (← readReg Register.hart_state) with
  | .HART_WAITING _ => pure true
  | .HART_ACTIVE () => do
      tick_pc ()
      pure false

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

/-- ECALL on an active M-mode hart produces the machine environment-call trap
at the current PC, without changing the state; for example, PC 16 yields a trap
whose saved address is 16. -/
theorem execute_ECALL_machine (s : SailState) (hinv : StepInvariant s)
    (pc : BitVec 64) (hpc : s.regs.get? Register.PC = some pc) :
    execute (.ECALL ()) s = .ok (.Trap (Privilege.Machine, .CTL_TRAP ecallException, pc)) s := by
  change execute_ECALL () s = _
  unfold execute_ECALL
  simp only [bind, EStateM.bind,
    readReg_eq_of_get? Register.cur_privilege s _ hinv.machine,
    readReg_eq_of_get? Register.PC s _ hpc, pure, EStateM.pure]
  rfl

/-- The trap case of `stepFinish` handles the exception and then runs the
non-retiring tail; for example, an ECALL does not increment `minstret`. -/
theorem stepFinish_trap (p : Privilege) (ctl : ctl_result) (pc : BitVec 64) (bits : BitVec 32) :
    stepFinish (.Step_Execute (.Trap (p, ctl, pc), bits)) =
      (do set_next_pc (← exception_handler p ctl pc); trapFinish) := by
  funext s
  simp [stepFinish, trapFinish, get_config_rvfi, andM, toBool,
    bind, EStateM.bind, pure]
  rfl

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
        show ¬ i < start + len from by omega, BitVec.getLsbD_of_ge y (i - start) (by omega : len ≤ i - start)]

private def mask (start len : Nat) : BitVec 64 := (BitVec.allOnes len).setWidth 64 <<< start

private theorem mask_getLsbD (start len i : Nat) (hi : i < 64) :
    (mask start len).getLsbD i = decide (start ≤ i ∧ i < start + len) := by
  simp only [mask, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  omega

private theorem mstatus_stack_bits (returning : Bool) (m : BitVec 64) :
    (if returning then
      Sail.BitVec.updateSubrange
        (Sail.BitVec.updateSubrange
          (Sail.BitVec.updateSubrange m 3 3 (_get_Mstatus_MPIE m)) 7 7 (1#1))
        12 11 (3#2)
    else
      Sail.BitVec.updateSubrange
        (Sail.BitVec.updateSubrange
          (Sail.BitVec.updateSubrange m 7 7 (_get_Mstatus_MIE m)) 3 3 (0#1))
        12 11 (3#2)) =
      (if returning then mretMstatus m else trapMstatus m) := by
  cases returning <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  all_goals
    by_cases hspecial : i = 3 ∨ i = 7 ∨ i = 11 ∨ i = 12
    · rcases hspecial with h | h | h | h <;> subst i <;>
        simp [trapMstatus, mretMstatus, Sail.BitVec.updateSubrange,
          Sail.BitVec.updateSubrange', _get_Mstatus_MIE, _get_Mstatus_MPIE,
          Sail.BitVec.extractLsb]
    · have h3 : ¬(3 ≤ i ∧ i < 4) := by omega
      have h7 : ¬(7 ≤ i ∧ i < 8) := by omega
      have hpp : ¬(11 ≤ i ∧ i < 13) := by omega
      have h8 : (8#64) = mask 3 1 := rfl
      have h80 : (0x80#64) = mask 7 1 := rfl
      have h1800 : (0x1800#64) = mask 11 2 := rfl
      have h1888 : (0x1888#64) = mask 3 1 ||| mask 7 1 ||| mask 11 2 := rfl
      have hm8 : (8#64).getLsbD (i - 4) = false := by
        rw [h8, mask_getLsbD _ _ _ (by omega)]
        simp [show ¬(3 ≤ i - 4 ∧ i - 4 < 3 + 1) from by omega]
      have hm80 : (0x80#64).getLsbD (4 + i) = false := by
        by_cases hp : 4 + i < 64
        · rw [h80, mask_getLsbD _ _ _ hp]
          simp only [show ¬(7 ≤ 4 + i ∧ 4 + i < 7 + 1) from by omega, decide_false]
        · exact BitVec.getLsbD_of_ge _ _ (by omega)
      have hleft : ((m &&& 8#64) <<< 4).getLsbD i = false := by
        simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, hm8, Bool.and_false]
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
      simp only [trapMstatus, mretMstatus, BitVec.getLsbD_or, BitVec.getLsbD_and,
        BitVec.getLsbD_not, hmask, hmpp, hleft, hright, hmpie, hi, decide_true,
        Bool.not_false, Bool.and_true, Bool.or_false,
        Sail.BitVec.updateSubrange, update_getLsbD, h3, h7, hpp, ↓reduceIte]

private theorem trap_mstatus_bits (m : BitVec 64) :
    Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange
        (Sail.BitVec.updateSubrange m 7 7 (_get_Mstatus_MIE m)) 3 3 (0#1))
      12 11 (3#2) = trapMstatus m := mstatus_stack_bits false m

private theorem mret_mstatus_bits (m : BitVec 64) :
    Sail.BitVec.updateSubrange
      (Sail.BitVec.updateSubrange
        (Sail.BitVec.updateSubrange m 3 3 (_get_Mstatus_MPIE m)) 7 7 (1#1))
      12 11 (3#2) = mretMstatus m := mstatus_stack_bits true m

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

private theorem aligned_pc_bits (e : BitVec 64) (he0 : e.getLsbD 0 = false) :
    Sail.BitVec.update e 0 (0#1) = e := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [Sail.BitVec.update, update_getLsbD _ _ _ _ hi]
  by_cases hz : i = 0
  · subst i
    change false = e.getLsbD 0
    exact he0.symm
  · simp [show ¬ i < 1 from by omega]

private theorem align_pc_machine (s : SailState) (misa e : BitVec 64)
    (hmisa : s.regs.get? Register.misa = some misa) (hc : _get_Misa_C misa = 1#1)
    (he0 : e.getLsbD 0 = false) : align_pc e s = .ok e s := by
  have hZca : currentlyEnabled extension.Ext_Zca s = .ok true s := by
    have hsupports : hartSupports extension.Ext_Zca = true := by simp [hartSupports]
    unfold currentlyEnabled
    unfold currentlyEnabled
    simp [hsupports, hartSupports_C, LeanRV64D.Functions.not,
      andM, toBool, bind, EStateM.bind, pure, EStateM.pure,
      readReg_eq_of_get? Register.misa s misa hmisa, hc]
  unfold align_pc
  simp [hZca, bind, EStateM.bind, pure, EStateM.pure, aligned_pc_bits e he0]

private theorem ecall_mcause_bits (c : BitVec 64) :
    Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange c 63 63 (0#1))
      62 0 (11#63) = 11#64 := by
  unfold Sail.BitVec.updateSubrange Sail.BitVec.updateSubrange'
  bv_normalize

private theorem tvec_mode_bits (t : BitVec 64) (ht1 : t.getLsbD 1 = false) :
    _get_Mtvec_Mode t = if t.getLsbD 0 then 1#2 else 0#2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  split <;>
    rcases (show i = 0 ∨ i = 1 from by omega) with h | h <;>
      subst i <;> simp_all [_get_Mtvec_Mode, Sail.BitVec.extractLsb]

private theorem tvec_base_bits (t : BitVec 64) :
    _get_Mtvec_Base t +++ (0#2) = t &&& ~~~(3#64) := by
  change (t.extractLsb' 2 62 +++ (0#2)) = t &&& ~~~(3#64)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hmask : (3#64) = mask 0 2 := rfl
  rw [hmask]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, mask_getLsbD _ _ _ hi,
    hi, decide_true, Bool.true_and, BitVec.getLsbD_append]
  by_cases hl : i < 2
  · simp [hl]
  · have hidx : 2 + (i - 2) = i := by omega
    have hlen : i - 2 < 62 := by omega
    simp [hl, hidx, hlen]

private theorem tvec_ecall_bits (t : BitVec 64) (ht1 : t.getLsbD 1 = false) :
    tvec_addr t (11#64) = some (t &&& ~~~(3#64)) := by
  unfold tvec_addr
  rw [tvec_mode_bits t ht1, tvec_base_bits t]
  cases t.getLsbD 0 <;> rfl

private theorem setReg_get?_self (s : SailState) (r : Register) (v : RegisterType r) :
    (setReg s r v).regs.get? r = some v := Std.ExtDHashMap.get?_insert_self

private theorem track_trap_machine_run (s : SailState) (m c v e : BitVec 64)
    (hm : s.regs.get? Register.mstatus = some m)
    (hc : s.regs.get? Register.mcause = some c)
    (hv : s.regs.get? Register.mtval = some v)
    (he : s.regs.get? Register.mepc = some e) :
    track_trap Privilege.Machine s = .ok () s := by
  simp only [track_trap, bind, EStateM.bind,
    readReg_eq_of_get? Register.mstatus s m hm, readReg_eq_of_get? Register.mcause s c hc,
    readReg_eq_of_get? Register.mtval s v hv, readReg_eq_of_get? Register.mepc s e he,
    System.long_csr_write_callback_mstatus_run, System.csr_name_write_callback_mcause_run,
    System.csr_name_write_callback_mtval_run, System.csr_name_write_callback_mepc_run]

private theorem bind_run_ok {α β : Type} {f : SailM α} {g : α → SailM β}
    {s s' : SailState} {a : α} (h : f s = .ok a s') :
    (f >>= g) s = g a s' := by
  simp only [bind, EStateM.bind, h]

private theorem ecall_tail_run (s : SailState) (m t pc : BitVec 64)
    (ht : s.regs.get? Register.mtvec = some t) (ht1 : t.getLsbD 1 = false) :
    (do track_trap Privilege.Machine
        prepare_trap_vector Privilege.Machine (← readReg Register.mcause)) (ecallState s m pc) =
      .ok (t &&& ~~~(3#64)) (ecallState s m pc) := by
  have htrack : track_trap Privilege.Machine (ecallState s m pc) =
      .ok () (ecallState s m pc) := by
    apply track_trap_machine_run _ (trapMstatus m) (11#64) (0#64) pc <;>
      simp [ecallState, setReg_get?_ne, setReg_get?_self]
  rw [bind_run_ok htrack]
  have hcause : readReg Register.mcause (ecallState s m pc) =
      .ok (11#64) (ecallState s m pc) := by
    apply readReg_eq_of_get?
    simp [ecallState, setReg_get?_ne, setReg_get?_self]
  rw [bind_run_ok hcause]
  unfold prepare_trap_vector
  have htvec : readReg Register.mtvec (ecallState s m pc) =
      .ok t (ecallState s m pc) := by
    apply readReg_eq_of_get?
    simpa [ecallState, setReg_get?_ne] using ht
  rw [bind_run_ok htvec, tvec_ecall_bits t ht1]
  rfl

/-- Handling an M-mode ECALL saves its address and machine exception code,
updates `mstatus`, and returns the trap-vector base without changing privilege.
For example, both `mtvec = 0x100` and vectored `mtvec = 0x101` return `0x100`. -/
theorem exception_handler_ecall (s : SailState) (hinv : StepInvariant s)
    (m t pc : BitVec 64)
    (hm : s.regs.get? Register.mstatus = some m)
    (ht : s.regs.get? Register.mtvec = some t) (ht1 : t.getLsbD 1 = false) :
    exception_handler Privilege.Machine (.CTL_TRAP ecallException) pc s =
      .ok (t &&& ~~~(3#64)) (ecallState s m pc) := by
  obtain ⟨d, hd⟩ := (hinv.present Register.medeleg).exists_value
  obtain ⟨c, hc⟩ := (hinv.present Register.mcause).exists_value
  unfold exception_handler exception_delegatee ecallException
  simp only [bind, EStateM.bind, readReg_eq_of_get? Register.medeleg s d hd,
    HartConfig.currentlyEnabled_S_run, Bool.false_and, pure, EStateM.pure,
    show zopz0zI_u (privLevel_to_bits Privilege.Machine)
      (privLevel_to_bits Privilege.Machine) = false from rfl,
    Bool.false_eq_true, ↓reduceIte]
  change trap_handler Privilege.Machine (.Exception (.E_M_EnvCall ())) pc none none s = _
  unfold trap_handler
  simp only [get_config_print_exception, get_config_print_interrupt,
    HartConfig.hartSupports_Zicfilp, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    trapCause_is_interrupt, trapCause_bits_forwards, exceptionType_bits_forwards,
    bool_to_bit, bool_bit_forwards, tval, zeros, zero_extend, Sail.BitVec.zeroExtend]
  rw [bind_run_ok (readReg_eq_of_get? Register.mcause s c hc),
    bind_run_ok (writeReg_run ..), bind_run_ok (readReg_setReg_self ..),
    bind_run_ok (writeReg_run ..)]
  simp only [setReg_overwrite]
  change (readReg Register.mstatus >>= _) (setReg s Register.mcause
    (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange c 63 63 (0#1))
      62 0 (11#63))) = _
  rw [ecall_mcause_bits]
  have hms : readReg Register.mstatus (setReg s Register.mcause (11#64)) =
      .ok m (setReg s Register.mcause (11#64)) := by
    apply readReg_eq_of_get?
    simpa [setReg_get?_ne] using hm
  rw [bind_run_ok hms, bind_run_ok hms, bind_run_ok (writeReg_run ..),
    bind_run_ok (readReg_setReg_self ..), bind_run_ok (writeReg_run ..),
    bind_run_ok (readReg_setReg_self ..)]
  have hpriv (v : BitVec 64) :
      readReg Register.cur_privilege (setReg (setReg s Register.mcause (11#64)) Register.mstatus v) =
        .ok Privilege.Machine (setReg (setReg s Register.mcause (11#64)) Register.mstatus v) := by
    apply readReg_eq_of_get?
    simp [setReg_get?_ne, hinv.machine]
  simp only [setReg_overwrite]
  rw [bind_run_ok (hpriv _), bind_run_ok (writeReg_run ..)]
  simp only [setReg_overwrite, privLevel_to_bits, privLevel_bits_backwards, trap_mstatus_bits]
  rw [bind_run_ok (writeReg_run ..), bind_run_ok (writeReg_run ..)]
  change (writeReg Register.cur_privilege Privilege.Machine >>= _) (ecallState s m pc) = _
  have hsame : setReg (ecallState s m pc) Register.cur_privilege Privilege.Machine =
      ecallState s m pc := by
    apply setReg_eq_self
    simp [ecallState, setReg_get?_ne, hinv.machine]
  rw [bind_run_ok (writeReg_run ..), hsame]
  exact ecall_tail_run s m t pc ht ht1

private theorem mret_handler_run (s : SailState) (m e misa pc : BitVec 64)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hm : s.regs.get? Register.mstatus = some m)
    (he : s.regs.get? Register.mepc = some e)
    (hmisa : s.regs.get? Register.misa = some misa) (hc : _get_Misa_C misa = 1#1)
    (he0 : e.getLsbD 0 = false) (hmpp : m &&& 0x1800#64 = 0x1800#64) :
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
  apply align_pc_machine _ misa e _ hc he0
  simpa [setReg_get?_ne] using hmisa

/-- MRET restores MIE from MPIE, sets MPIE and saved privilege to M-only values,
and jumps to the aligned saved PC while remaining in M-mode.
For example, `mstatus = 0x1880` and `mepc = 16` yield `mstatus = 0x1888`
and `nextPC = 16`; `hmpp` requires the saved privilege to encode M-mode. -/
theorem execute_MRET_machine (s : SailState) (hinv : StepInvariant s)
    (m e : BitVec 64)
    (hm : s.regs.get? Register.mstatus = some m)
    (he : s.regs.get? Register.mepc = some e) (he0 : e.getLsbD 0 = false)
    (hmpp : m &&& 0x1800#64 = 0x1800#64) :
    execute (.MRET ()) s =
      .ok RETIRE_SUCCESS (setReg (setReg s Register.mstatus (mretMstatus m)) Register.nextPC e) := by
  obtain ⟨pc, hpc⟩ := (hinv.present Register.PC).exists_value
  obtain ⟨misa, hmisa, hc⟩ := hinv.misa_c
  have hhandler := mret_handler_run s m e misa pc hinv.machine hm he hmisa hc he0 hmpp
  change execute_MRET () s = _
  unfold execute_MRET
  rw [bind_run_ok (readReg_eq_of_get? Register.cur_privilege s _ hinv.machine)]
  change (readReg Register.cur_privilege >>= _) s = _
  rw [bind_run_ok (readReg_eq_of_get? Register.cur_privilege s _ hinv.machine),
    bind_run_ok (readReg_eq_of_get? Register.PC s pc hpc), bind_run_ok hhandler]
  have hnext (st : SailState) : set_next_pc e st = .ok () (setReg st Register.nextPC e) := by
    simp only [set_next_pc, bind, EStateM.bind, writeReg_run, pure, EStateM.pure]
  rw [bind_run_ok (hnext _)]
  rfl

end Step
