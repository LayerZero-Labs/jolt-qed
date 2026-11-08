import JoltBytecode.Step.TryStep
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

/-!
# Sail execution of Jolt's machine-mode CSRs

The six addresses follow Jolt's tracer at `5def437f`,
`tracer/src/utils/virtual_registers.rs`
(`VirtualRegisterAllocator::csr_to_virtual_register`, `is_supported_csr`).
The generated Sail paths are `execute_CSRReg` and `execute_CSRImm` in
`LeanRV64D/InstsEnd.lean`, and `doCSR` in `LeanRV64D/ZicsrInsts.lean`.
Legalization follows `legalize_mstatus`, `legalize_tvec`, and `legalize_xepc`
in `LeanRV64D/SysRegs.lean` on the configured RV64IMAC machine-only hart.
MIE (bit 3) enables machine interrupts, MPIE (bit 7) records the previous
interrupt-enable bit, and MPP (bits 12:11) records the previous privilege
level, fixed here to machine mode (3).
-/

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

open scoped Classical

noncomputable section

namespace Step

/-- The six CSRs Jolt implements, for example `0x340` is `mscratch`. -/
def IsJoltCsr (csr : BitVec 12) : Prop :=
  csr = 0x300 ∨ csr = 0x305 ∨ csr = 0x340 ∨ csr = 0x341 ∨ csr = 0x342 ∨ csr = 0x343

/-- The value Sail holds for one of Jolt's CSRs, for example `mscratch` at `0x340`.
An absent register or an unsupported address gives `none`. -/
def csrRead (csr : BitVec 12) (s : SailState) : Option (BitVec 64) :=
  if csr = 0x300 then s.regs.get? Register.mstatus
  else if csr = 0x305 then s.regs.get? Register.mtvec
  else if csr = 0x340 then s.regs.get? Register.mscratch
  else if csr = 0x341 then s.regs.get? Register.mepc
  else if csr = 0x342 then s.regs.get? Register.mcause
  else if csr = 0x343 then s.regs.get? Register.mtval
  else none

/-- Store `v` into the register behind one of Jolt's CSRs.
For example, address `0x340` updates only `mscratch`; other addresses do nothing. -/
def csrSet (csr : BitVec 12) (v : BitVec 64) (s : SailState) : SailState :=
  if csr = 0x300 then setReg s Register.mstatus v
  else if csr = 0x305 then setReg s Register.mtvec v
  else if csr = 0x340 then setReg s Register.mscratch v
  else if csr = 0x341 then setReg s Register.mepc v
  else if csr = 0x342 then setReg s Register.mcause v
  else if csr = 0x343 then setReg s Register.mtval v
  else s

/-- The value Sail stores when `new` is written over `old`: mstatus keeps only
MIE and MPIE and has MPP fixed at M; a reserved mtvec mode keeps the old mode;
mepc clears bit 0; the others are stored raw.
For example, writing zero to `mstatus` stores `0x1800`. -/
def csrLegal (csr : BitVec 12) (old new : BitVec 64) : BitVec 64 :=
  if csr = 0x300 then (new &&& 0x88#64) ||| 0x1800#64
  else if csr = 0x305 then
    (if new.getLsbD 1 then (new &&& ~~~(3#64)) ||| (old &&& 3#64) else new)
  else if csr = 0x341 then new &&& ~~~(1#64)
  else new

/-- The new value before legalization: replace, set bits, or clear bits.
For example, `CSRRS` with source 8 sets MIE in `mstatus`. -/
def csrApply (op : csrop) (old src : BitVec 64) : BitVec 64 :=
  match op with
  | .CSRRW => src
  | .CSRRS => old ||| src
  | .CSRRC => old &&& ~~~src

/-- Legal stored values for the three restricted CSRs.
Only MIE, MPIE and MPP can be set in `mstatus`, with MPP fixed at M;
`mtvec` has mode 0 or 1, and `mepc` is even.
For example, values `0x1800`, 0 and 0 satisfy the three restrictions. -/
structure CsrLegal (s : SailState) : Prop where
  mstatus : ∃ m : BitVec 64, s.regs.get? Register.mstatus = some m ∧
    m &&& ~~~(0x1888#64) = 0 ∧ m &&& 0x1800#64 = 0x1800#64
  mtvec : ∃ t : BitVec 64, s.regs.get? Register.mtvec = some t ∧ t.getLsbD 1 = false
  mepc : ∃ e : BitVec 64, s.regs.get? Register.mepc = some e ∧ e.getLsbD 0 = false

private theorem mstatus_mask_legal (v : BitVec 64) :
    ((v &&& 0x88#64) ||| 0x1800#64) &&& ~~~(0x1888#64) = 0 ∧
    ((v &&& 0x88#64) ||| 0x1800#64) &&& 0x1800#64 = 0x1800#64 := by
  simp only [BitVec.and_or_distrib_right, BitVec.and_assoc]
  simp

/-- Legalizing and storing a CSR preserves the legal-value restrictions.
For example, writing 3 to `mepc` stores 2 and leaves the other restrictions intact. -/
theorem csrLegal_legal (csr : BitVec 12) (old new : BitVec 64) (s : SailState)
    (hleg : CsrLegal s) (hold : csrRead csr s = some old) :
    CsrLegal (csrSet csr (csrLegal csr old new) s) := by
  obtain ⟨⟨m, hm, hm0, hmM⟩, ⟨t, ht, ht1⟩, ⟨e, he, he0⟩⟩ := hleg
  unfold csrSet csrLegal
  split
  · exact ⟨⟨_, by simp [setReg], mstatus_mask_legal new⟩,
      ⟨t, by simpa [setReg, Std.ExtDHashMap.get?_insert] using ht, ht1⟩,
      ⟨e, by simpa [setReg, Std.ExtDHashMap.get?_insert] using he, he0⟩⟩
  · split
    · have hread : s.regs.get? Register.mtvec = some old := by
        simpa [csrRead, *] using hold
      have ho : old = t := Option.some.inj (hread.symm.trans ht)
      refine ⟨⟨m, by simpa [setReg, Std.ExtDHashMap.get?_insert] using hm, hm0, hmM⟩,
        ⟨(if new.getLsbD 1 then (new &&& ~~~(3#64)) ||| (old &&& 3#64) else new),
          by simp [setReg, Std.ExtDHashMap.get?_insert_self], ?_⟩, ⟨e, by simpa [setReg, Std.ExtDHashMap.get?_insert] using he, he0⟩⟩
      split <;> simp_all
    · split
      · exact ⟨⟨m, by simpa [setReg, Std.ExtDHashMap.get?_insert] using hm, hm0, hmM⟩,
          ⟨t, by simpa [setReg, Std.ExtDHashMap.get?_insert] using ht, ht1⟩,
          ⟨e, by simpa [setReg, Std.ExtDHashMap.get?_insert] using he, he0⟩⟩
      · split
        · exact ⟨⟨m, by simpa [setReg, Std.ExtDHashMap.get?_insert] using hm, hm0, hmM⟩,
            ⟨t, by simpa [setReg, Std.ExtDHashMap.get?_insert] using ht, ht1⟩,
            ⟨new &&& ~~~(1#64), by simp [setReg, Std.ExtDHashMap.get?_insert_self], by simp⟩⟩
        · split
          · exact ⟨⟨m, by simpa [setReg, Std.ExtDHashMap.get?_insert] using hm, hm0, hmM⟩,
              ⟨t, by simpa [setReg, Std.ExtDHashMap.get?_insert] using ht, ht1⟩,
              ⟨e, by simpa [setReg, Std.ExtDHashMap.get?_insert] using he, he0⟩⟩
          · split
            · exact ⟨⟨m, by simpa [setReg, Std.ExtDHashMap.get?_insert] using hm, hm0, hmM⟩,
                ⟨t, by simpa [setReg, Std.ExtDHashMap.get?_insert] using ht, ht1⟩,
                ⟨e, by simpa [setReg, Std.ExtDHashMap.get?_insert] using he, he0⟩⟩
            · exact ⟨⟨m, hm, hm0, hmM⟩, ⟨t, ht, ht1⟩, ⟨e, he, he0⟩⟩

private theorem clear_bit_zero (v : BitVec 64) :
    Sail.BitVec.update v 0 0#1 = v &&& ~~~(1#64) := by
  simp [Sail.BitVec.update, Sail.BitVec.updateSubrange', BitVec.and_comm]

private theorem clear_bit_zero_eq (v : BitVec 64) (h : v.getLsbD 0 = false) :
    v &&& ~~~(1#64) = v := by
  ext i
  by_cases hi : i = 0
  · subst i
    simpa [← BitVec.getLsbD_eq_getElem] using h.symm
  · simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_one]
    simp [*]

private theorem check_CSR_jolt (csr : BitVec 12) (hcsr : IsJoltCsr csr)
    (access : CSRAccessType) (s : SailState) :
    check_CSR csr Privilege.Machine access s = .ok true s := by
  rcases hcsr with rfl | rfl | rfl | rfl | rfl | rfl <;> cases access <;>
    unfold check_CSR check_CSR_priv check_CSR_access is_CSR_accessible
      stateen_allows_CSR_access privLevel_to_CSR_privbits csrPriv csrAccess
      zopz0zKzJ_u <;>
    simp [bind, EStateM.bind, pure, EStateM.pure, andM, toBool] <;> rfl

private theorem csr_callbacks (csr : BitVec 12) (hcsr : IsJoltCsr csr)
    (value : BitVec 64) (s : SailState) :
    csr_id_read_callback csr value s = .ok () s ∧
    csr_id_write_callback csr value s = .ok () s := by
  rcases hcsr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

private theorem read_CSR_jolt (csr : BitVec 12) (hcsr : IsJoltCsr csr)
    (s : SailState) (hinv : StepInvariant s) (hleg : CsrLegal s)
    (old : BitVec 64) (hold : csrRead csr s = some old) :
    read_CSR csr s = .ok old s := by
  rcases hcsr with rfl | rfl | rfl | rfl | rfl | rfl
  · change (do
        let v ← LeanRV64D.readReg Register.mstatus
        pure (Sail.BitVec.extractLsb v 63 0)) s = .ok old s
    have hread := readReg_eq_of_get? Register.mstatus s old (by simpa [csrRead] using hold)
    simp only [bind, EStateM.bind, hread, pure, EStateM.pure]
    congr 1
    ext i
    simp [Sail.BitVec.extractLsb, ← BitVec.getLsbD_eq_getElem]
    omega
  · exact readReg_eq_of_get? Register.mtvec s old (by simpa [csrRead] using hold)
  · exact readReg_eq_of_get? Register.mscratch s old (by simpa [csrRead] using hold)
  · change (get_xepc Privilege.Machine) s = .ok old s
    have hread := readReg_eq_of_get? Register.mepc s old (by simpa [csrRead] using hold)
    obtain ⟨e, he, he0⟩ := hleg.mepc
    have heq : e = old := Option.some.inj (he.symm.trans (by simpa [csrRead] using hold))
    subst e
    simp only [get_xepc, align_pc, bind, EStateM.bind, hread,
      currentlyEnabled_Zca_run s hinv, pure, EStateM.pure,
      clear_bit_zero, clear_bit_zero_eq old he0, ite_true]
  · exact readReg_eq_of_get? Register.mcause s old (by simpa [csrRead] using hold)
  · exact readReg_eq_of_get? Register.mtval s old (by simpa [csrRead] using hold)

private theorem isolate_bit (v : BitVec 64) (n : Nat) (hn : n < 64) :
    BitVec.setWidth 64 (Sail.BitVec.extractLsb v n n) <<< n = v &&& (1#64 <<< n) := by
  ext i
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, Sail.BitVec.extractLsb, BitVec.extractLsb,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_one]
  by_cases hi : i = n
  · subst i
    simp [hn]
  · by_cases hni : i < n
    · simp [hni]
    · simp [hni, show i - n ≠ 0 by omega]

private theorem mask_outside_zero (old mask : BitVec 64)
    (hzero : old &&& ~~~(0x1888#64) = 0)
    (hmask : mask &&& ~~~(0x1888#64) = mask) : mask &&& old = 0 := by
  calc
    mask &&& old = (mask &&& ~~~(0x1888#64)) &&& old := by rw [hmask]
    _ = mask &&& (old &&& ~~~(0x1888#64)) := by ac_rfl
    _ = 0 := by rw [hzero]; simp

private theorem and_left_comm (a b c : BitVec 64) :
    a &&& (b &&& c) = b &&& (a &&& c) := by ac_rfl

private theorem mstatus_pack (v : BitVec 64) :
    6144#64 ||| (v &&& 128#64) ||| (v &&& 8#64) = (v &&& 136#64) ||| 6144#64 := by
  rw [BitVec.or_assoc, ← BitVec.and_or_distrib_left]
  exact BitVec.or_comm _ _

private theorem two_bit_cases (v : BitVec 2) :
    v = 0#2 ∨ v = 1#2 ∨ v = 2#2 ∨ v = 3#2 := by
  have hbound := v.isLt
  have h : v.toNat = 0 ∨ v.toNat = 1 ∨ v.toNat = 2 ∨ v.toNat = 3 := by omega
  rcases h with h | h | h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))
  · exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq h)))

private theorem have_nominal_privLevel_run (p : BitVec 2) (s : SailState) :
    have_nominal_privLevel p s = .ok (p == 3#2) s := by
  rcases two_bit_cases p with rfl | rfl | rfl | rfl <;>
    simp [have_nominal_privLevel, HartConfig.currentlyEnabled_U_run,
      HartConfig.currentlyEnabled_S_run, pure, EStateM.pure]

private theorem andM_S_run (b : Bool) (s : SailState) :
    (andM (pure b) (currentlyEnabled extension.Ext_S)) s = .ok false s := by
  cases b <;>
    simp [andM, toBool, bind, EStateM.bind, pure, EStateM.pure,
      HartConfig.currentlyEnabled_S_run]

private theorem currentlyEnabled_vm_run (ext : extension)
    (hext : ext = .Ext_Sv32 ∨ ext = .Ext_Sv39 ∨ ext = .Ext_Sv48 ∨ ext = .Ext_Sv57)
    (s : SailState) : currentlyEnabled ext s = .ok false s := by
  rcases hext with rfl | rfl | rfl | rfl <;>
    unfold currentlyEnabled <;> exact andM_S_run _ s

private theorem virtual_memory_supported_run (s : SailState) :
    virtual_memory_supported () s = .ok false s := by
  have h32 := currentlyEnabled_vm_run _ (Or.inl rfl)
  have h39 := currentlyEnabled_vm_run _ (Or.inr (Or.inl rfl))
  have h48 := currentlyEnabled_vm_run _ (Or.inr (Or.inr (Or.inl rfl)))
  have h57 := currentlyEnabled_vm_run _ (Or.inr (Or.inr (Or.inr rfl)))
  simp [virtual_memory_supported, orM, toBool, bind, EStateM.bind,
    h32, h39, h48, h57]

private theorem legalize_mstatus_run (old new : BitVec 64) (s : SailState)
    (hzero : old &&& ~~~(0x1888#64) = 0) :
    legalize_mstatus old new s = .ok ((new &&& 0x88#64) ||| 0x1800#64) s := by
  unfold legalize_mstatus
  by_cases hp : _get_Mstatus_MPP (Mk_Mstatus new) = 3#2 <;>
    simp only [bind, EStateM.bind, HartConfig.currentlyEnabled_S_run,
      HartConfig.currentlyEnabled_U_run, virtual_memory_supported_run,
      have_nominal_privLevel_run, hp, beq_self_eq_true, beq_iff_eq,
      HartConfig.lowest_supported_privLevel_run, pure, EStateM.pure,
      Bool.false_eq_true, ite_false, ite_true]
  all_goals
    simp only [HartConfig.hartSupports_Zicfilp,
      show hartSupports extension.Ext_Zfinx = false from by simp [hartSupports],
      show hartSupports extension.Ext_Zve32x = false from by
        simp [hartSupports, vector_support_ge, vector_support_level, num_of_vector_support], Bool.false_eq_true,
      ite_false, plat_mstatus_legal_fs, legalize_extStatus, extStatus_to_bits,
      extStatus_bits_forwards, privLevel_to_bits, privLevel_bits_backwards]
    congr 1
    simp only [_update_Mstatus_SD, _update_Mstatus_SIE, _update_Mstatus_MIE,
      _update_Mstatus_SPIE, _update_Mstatus_MPIE, _update_Mstatus_VS,
      _update_Mstatus_SPP, _update_Mstatus_MPP, _update_Mstatus_FS,
      _update_Mstatus_XS, _update_Mstatus_MPRV, _update_Mstatus_SUM,
      _update_Mstatus_MXR, _update_Mstatus_TVM, _update_Mstatus_TW,
      _update_Mstatus_TSR, _update_Mstatus_SPELP, _update_Mstatus_MPELP,
      Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
    simp [BitVec.and_or_distrib_left, ← BitVec.and_assoc]
    -- Inherited bits before and after Sail clears the status-summary bit SD.
    simp only [mask_outside_zero old 0x7ffffdffff000055#64 hzero rfl,
      mask_outside_zero old 0xfffffdffff000055#64 hzero rfl]
    simp only [Mk_Mstatus, _get_Mstatus_MIE, _get_Mstatus_MPIE,
      isolate_bit new 3 (by decide), isolate_bit new 7 (by decide)]
    simp [and_left_comm]
    simp only [mstatus_pack]
    simp [_get_Mstatus_FS, _get_Mstatus_XS, _get_Mstatus_VS, Sail.BitVec.extractLsb,
      BitVec.extractLsb_or, BitVec.extractLsb_and, extStatus_of_bits,
      extStatus_bits_backwards, bool_to_bit, bool_bit_forwards,
      show (ExtStatus.Off == ExtStatus.Dirty) = false from rfl]

private theorem low_two_bits (v : BitVec 64) :
    BitVec.setWidth 64 (_get_Mtvec_Mode v) = v &&& 3#64 := by
  apply BitVec.eq_of_toNat_eq
  have h := Nat.and_two_pow_sub_one_eq_mod v.toNat 2
  simp only [Nat.reducePow, Nat.reduceSub] at h
  simp only [_get_Mtvec_Mode, Sail.BitVec.extractLsb, BitVec.toNat_setWidth,
    BitVec.extractLsb, BitVec.extractLsb'_toNat, BitVec.toNat_and]
  have hbound : v.toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  simp [h]
  omega

private theorem legalize_tvec_run (old new : BitVec 64) (s : SailState) :
    legalize_tvec old new s =
      .ok (if new.getLsbD 1 then (new &&& ~~~(3#64)) ||| (old &&& 3#64) else new) s := by
  have hbit : new.getLsbD 1 = (_get_Mtvec_Mode new).getLsbD 1 := by
    simp [_get_Mtvec_Mode, Sail.BitVec.extractLsb]
  have hupdate : _update_Mtvec_Mode new (_get_Mtvec_Mode old) =
      (new &&& ~~~(3#64)) ||| (old &&& 3#64) := by
    simp [_update_Mtvec_Mode, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
      low_two_bits, BitVec.and_comm]
  rcases two_bit_cases (_get_Mtvec_Mode new) with hm | hm | hm | hm <;>
    rw [hm] at hbit <;>
    simp at hbit <;>
    simp [legalize_tvec, Mk_Mtvec, hm, trapVectorMode_of_bits,
      xtvec_mode_reserved_behavior, hbit, hupdate, pure, EStateM.pure]

private theorem readReg_set_run (s : SailState) (r : Register) (v : RegisterType r) :
    (LeanRV64D.readReg r : SailM (RegisterType r)) (setReg s r v) =
      .ok v (setReg s r v) :=
  readReg_eq_of_get? r _ v (by simp [setReg, Std.ExtDHashMap.get?_insert_self])

private theorem write_read_run (s : SailState) (r : Register) (v : RegisterType r) :
    (do
      LeanRV64D.writeReg r v
      pure (Result.Ok (← LeanRV64D.readReg r) : Result (RegisterType r) Unit)) s =
      .ok (Result.Ok v) (setReg s r v) := by
  simp only [bind, EStateM.bind, writeReg_run, readReg_set_run, pure, EStateM.pure]

private theorem write_CSR_jolt (csr : BitVec 12) (hcsr : IsJoltCsr csr)
    (s : SailState) (hleg : CsrLegal s)
    (old new : BitVec 64) (hold : csrRead csr s = some old) :
    write_CSR csr new s = .ok (Result.Ok (csrLegal csr old new))
      (csrSet csr (csrLegal csr old new) s) := by
  rcases hcsr with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨m, hm, hm0, _⟩ := hleg.mstatus
    have heq : m = old := Option.some.inj (hm.symm.trans (by simpa [csrRead] using hold))
    subst m
    have hread := readReg_eq_of_get? Register.mstatus s old hm
    change (do
      LeanRV64D.writeReg Register.mstatus
        (← legalize_mstatus (← LeanRV64D.readReg Register.mstatus) new)
      pure (Result.Ok (← LeanRV64D.readReg Register.mstatus))) s =
        .ok (Result.Ok ((new &&& 0x88#64) ||| 0x1800#64))
          (setReg s Register.mstatus ((new &&& 0x88#64) ||| 0x1800#64))
    simp only [bind, EStateM.bind, hread, legalize_mstatus_run old new s hm0,
      writeReg_run, readReg_set_run, pure, EStateM.pure]
  · have hread := readReg_eq_of_get? Register.mtvec s old (by simpa [csrRead] using hold)
    change (set_mtvec new >>= fun v => pure (Result.Ok v)) s =
      .ok (Result.Ok (if new.getLsbD 1 then (new &&& ~~~(3#64)) ||| (old &&& 3#64) else new))
        (setReg s Register.mtvec
          (if new.getLsbD 1 then (new &&& ~~~(3#64)) ||| (old &&& 3#64) else new))
    simp only [set_mtvec, bind, EStateM.bind, hread, legalize_tvec_run,
      writeReg_run, readReg_set_run, pure, EStateM.pure]
  · exact write_read_run s Register.mscratch new
  · change (set_xepc Privilege.Machine new >>= fun v => pure (Result.Ok v)) s =
      .ok (Result.Ok (new &&& ~~~(1#64))) (setReg s Register.mepc (new &&& ~~~(1#64)))
    have hc : hartSupports extension.Ext_Zca = true := by simp [hartSupports]
    simp only [set_xepc, legalize_xepc, hc, ite_true, clear_bit_zero,
      bind, EStateM.bind, writeReg_run, pure, EStateM.pure]
  · exact write_read_run s Register.mcause new
  · exact write_read_run s Register.mtval new

local instance : LawfulBEq regidx where
  rfl := by
    rintro ⟨a⟩
    change (a == a) = true
    exact beq_self_eq_true a
  eq_of_beq := by
    rintro ⟨a⟩ ⟨b⟩ h
    change (a == b) = true at h
    exact congrArg regidx.Regidx (eq_of_beq h)

private theorem stateAfterWrite_zreg (s : SailState) (v : BitVec 64) :
    stateAfterWrite s zreg v = s :=
  stateAfterWrite_regidx_zero s v

private theorem doCSR_jolt (csr : BitVec 12) (hcsr : IsJoltCsr csr)
    (src : BitVec 64) (rd : regidx) (op : csrop) (source_zero : Bool)
    (s : SailState) (hinv : StepInvariant s) (hleg : CsrLegal s)
    (old : BitVec 64) (hold : csrRead csr s = some old) :
    doCSR csr src rd op (csr_access_type op (rd == zreg) source_zero) s =
      .ok RETIRE_SUCCESS
        (stateAfterWrite
          (if op = .CSRRW ∨ source_zero = false then
            csrSet csr (csrLegal csr old (csrApply op old src)) s else s) rd old) := by
  have hpriv := readReg_eq_of_get? Register.cur_privilege s _ hinv.machine
  have hcheck := check_CSR_jolt csr hcsr
  have hread := read_CSR_jolt csr hcsr s hinv hleg old hold
  have hwrite := write_CSR_jolt csr hcsr s hleg old
  have hcallbacks := csr_callbacks csr hcsr
  unfold doCSR
  cases op <;> cases source_zero <;> by_cases hrd : rd = zreg <;>
    simp [csr_access_type, hrd, Bool.beq_eq_decide_eq, bind, EStateM.bind, hpriv, hcheck,
      System.ext_check_CSR_true, hread, hwrite _ hold, csrApply,
      hcallbacks, wX_bits_stateAfterWrite, pure, EStateM.pure,
      LeanRV64D.Functions.not, stateAfterWrite_zreg,
      show (CSRAccessType.CSRRead != CSRAccessType.CSRWrite) = true from rfl,
      show (CSRAccessType.CSRRead != CSRAccessType.CSRRead) = false from rfl,
      show (CSRAccessType.CSRWrite != CSRAccessType.CSRWrite) = false from rfl,
      show (CSRAccessType.CSRWrite != CSRAccessType.CSRRead) = true from rfl,
      show (CSRAccessType.CSRReadWrite != CSRAccessType.CSRWrite) = true from rfl,
      show (CSRAccessType.CSRReadWrite != CSRAccessType.CSRRead) = true from rfl]

/-- A register-source CSR instruction reads the old CSR into `rd` and, when
required by its operation and source index, stores the legalized new value.
For example, `CSRRS` on `mscratch` with source `x1` and destination `x2`
sets the source bits and writes old `mscratch` into `x2`.
`zreg` is Sail's name for `x0`. -/
theorem execute_CSRReg_jolt (csr : BitVec 12) (hcsr : IsJoltCsr csr)
    (rs1 rd : regidx) (op : csrop) (s : SailState)
    (hinv : StepInvariant s) (hleg : CsrLegal s)
    (old src : BitVec 64) (hold : csrRead csr s = some old)
    (hsrc : rX_bits rs1 s = .ok src s) :
    execute (.CSRReg (csr, rs1, rd, op)) s =
      .ok RETIRE_SUCCESS
        (stateAfterWrite
          (if op = .CSRRW ∨ rs1 ≠ zreg then csrSet csr (csrLegal csr old (csrApply op old src)) s
           else s)
          rd old) := by
  change execute_CSRReg csr rs1 rd op s = _
  simp only [execute_CSRReg, bind, EStateM.bind, hsrc]
  simpa using doCSR_jolt csr hcsr src rd op (rs1 == zreg) s hinv hleg old hold

/-- An immediate CSR instruction uses the zero-extended five-bit source,
writes the old CSR into `rd`, and performs the required legalized CSR update.
For example, `CSRRC` on `mscratch` with immediate 1 and destination `x2`
clears bit 0 and writes the old value into `x2`. -/
theorem execute_CSRImm_jolt (csr : BitVec 12) (hcsr : IsJoltCsr csr)
    (imm : BitVec 5) (rd : regidx) (op : csrop) (s : SailState)
    (hinv : StepInvariant s) (hleg : CsrLegal s)
    (old : BitVec 64) (hold : csrRead csr s = some old) :
    execute (.CSRImm (csr, imm, rd, op)) s =
      .ok RETIRE_SUCCESS
        (stateAfterWrite
          (if op = .CSRRW ∨ imm ≠ 0 then
             csrSet csr (csrLegal csr old (csrApply op old (zero_extend (m := 64) imm))) s
           else s)
          rd old) := by
  change execute_CSRImm csr imm rd op s = _
  simpa [execute_CSRImm, zeros, BitVec.zero] using
    doCSR_jolt csr hcsr (zero_extend (m := 64) imm) rd op (imm == 0) s hinv hleg old hold

end Step
