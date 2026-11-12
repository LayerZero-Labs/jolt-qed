import JoltBytecode.Inlines.StraightLine
import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.MmuJolt

/-!
# Loads, stores and architectural-register reads in straight-line rows

This module extends `JoltBytecode.Inlines.StraightLine` with the rows that touch memory:
`LD` into a virtual register from an architectural base, and `SD` of a virtual register to an
architectural base. Each lemma says what a successful run of `row :: rest` means.

* `loadDword?` is the doubleword an `LD` reads, and `storeDword?` the state after an `SD`.
* For RAM addresses both have closed forms (`loadDword?_ram`, `storeDword?_ram`), with the
  read-after-write facts on the RAM map (`ram_doubleword_write_same`,
  `ram_doubleword_write_ne`).
* `XReads` says that reading an architectural register succeeds; it depends only on the Sail
  register map, so it survives the rows of an inline (`XReads.of_regs`).

Every lemma is proved; the module has no `sorry`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines

/-! ## Architectural-register reads -/

/-- Reading architectural register `r` in `s` succeeds with value `v` and changes nothing.
Example: `XReads s x0 0` holds for every `s`. -/
def XReads (s : SailJoltState) (r : regidx) (v : BitVec 64) : Prop :=
  rX_bits r s.sail = .ok v s.sail

/-- A successful read has the value `sourceValue`, the value the frame lemma talks about.
Example: if `x10` holds `0x80000000`, a successful read of `x10` returns `0x80000000`. -/
theorem XReads.eq_sourceValue {s : SailJoltState} {r : regidx} {v : BitVec 64}
    (h : XReads s r v) : v = sourceValue (.xreg r) s :=
  (readSrc_run (readSrc_xreg_run_of_read r s v h)).2

/-- The operand read of a row through an architectural register.
Example: if `XReads s x10 0x80010000`, then `readSrc (.xreg x10) s = .ok 0x80010000 s`. -/
theorem XReads.run {s : SailJoltState} {r : regidx} {v : BitVec 64} (h : XReads s r v) :
    readSrc (.xreg r) s = .ok v s :=
  readSrc_xreg_run_of_read r s v h

/-- A successful operand read through an architectural register is an `XReads`.
Example: `readSrc (.xreg x10) s = .ok 0x80010000 t` gives `XReads s x10 0x80010000`. -/
theorem XReads.of_readSrc {s t : SailJoltState} {r : regidx} {v : BitVec 64}
    (h : JoltISA.readSrc (.xreg r) s = .ok v t) : XReads s r v := by
  rw [(readSrc_run h).1] at h
  unfold XReads
  simp only [readSrc_xreg, liftSail] at h
  cases hr : rX_bits r s.sail with
  | error e σ => rw [hr] at h; cases h
  | ok w σ =>
    rw [hr] at h
    have hσ := rX_bits_pure r s.sail w σ hr
    subst hσ
    cases h
    rfl

private theorem readReg_ok_congr {reg : Register} {σ₁ σ₂ : SailState}
    {v : RegisterType reg} (hregs : σ₁.regs = σ₂.regs)
    (h : (LeanRV64D.readReg reg : SailM (RegisterType reg)) σ₁ = .ok v σ₁) :
    (LeanRV64D.readReg reg : SailM (RegisterType reg)) σ₂ = .ok v σ₂ := by
  unfold LeanRV64D.readReg Sail.ConcurrencyInterfaceV1.PreSail.readReg at h ⊢
  simp only [bind, EStateM.bind, get, MonadStateOf.get, getThe, EStateM.get, pure] at h ⊢
  rw [← hregs]
  revert h
  cases σ₁.regs.get? reg with
  | some w => intro h; cases h; rfl
  | none => simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Reading an architectural register depends only on the Sail register map.
Example: if `XReads s x10 0x80010000` and `t` is `s` after an `SD` to RAM, then
`XReads t x10 0x80010000`. -/
theorem XReads.of_regs {s t : SailJoltState} {r : regidx} {v : BitVec 64}
    (hregs : s.sail.regs = t.sail.regs) (h : XReads s r v) : XReads t r v := by
  unfold XReads rX_bits rX at h ⊢
  simp only [Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.toNat_natCast,
    bind, EStateM.bind] at h ⊢
  obtain ⟨i⟩ := r
  have hi : i.toNat < 32 := i.isLt
  generalize i.toNat = k at h hi ⊢
  interval_cases k <;> simp only [pure, EStateM.pure] at h ⊢
  · cases h
    rfl
  all_goals
    split at h
    · rename_i a σ hσ
      have hσ' := readReg_pure _ _ _ _ hσ
      subst hσ'
      cases h
      rw [readReg_ok_congr hregs hσ]
    · cases h

/-- Register-row updates keep architectural reads.
Example: `XReads s x10 0x80010000` gives `XReads { s with vregs := setV s.vregs vr62 7 } x10
0x80010000`. -/
theorem XReads.vregs {s : SailJoltState} {r : regidx} {v : BitVec 64}
    (f : VReg → BitVec 64) (h : XReads s r v) : XReads { s with vregs := f } r v := h

/-! ## Alignment -/

/-- The alignment test of `LD` and `SD` is divisibility by 8.
Example: `0x80000008 &&& 7 = 0`. -/
theorem and_seven_eq_zero_iff (a : BitVec 64) : a &&& 7 = 0 ↔ a.toNat % 8 = 0 := by
  constructor
  · exact Mmu.toNat_mod_eight_of_align
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have h7 : (7 : BitVec 64).toNat = 2 ^ 3 - 1 := by decide
    rw [h7, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h

/-! ## Loads -/

/-- The doubleword an `LD` reads at address `a` in state `s`, or `none` when Jolt's load
fails (misaligned, outside the readable memory, or an unreadable device byte).
Example: `loadDword? s 0x80010000 = some (ram_doubleword s.sail.mem 0x80010000)` when
`0x80010000` lies below the heap end and outside the stack canary. -/
def loadDword? (s : SailJoltState) (a : BitVec 64) : Option (BitVec 64) :=
  match Mmu.load_doubleword a s with
  | .ok (.Ok v) _ => some v
  | _ => none

/-- A doubleword load that returns changes nothing and returns a value at an aligned
address.
Example: if `Mmu.load_doubleword 0x80010000 s = .ok r t`, then `t = s` and `r = .Ok v` for
some `v`. -/
theorem load_doubleword_ok_inv {a : BitVec 64} {s t : SailJoltState}
    {r : Result (BitVec 64) ExecutionResult} (h : Mmu.load_doubleword a s = .ok r t) :
    t = s ∧ (∃ v, r = .Ok v) ∧ a.toNat % 8 = 0 := by
  simp only [Mmu.load_doubleword] at h
  repeat' split at h
  all_goals first | (cases h; exact ⟨rfl, ⟨_, rfl⟩, by omega⟩) | cases h

/-- The load behind a `loadDword?` value.
Example: if `loadDword? s 0x80010000 = some 7`, then `Mmu.load_doubleword 0x80010000 s` returns
`7` and leaves `s` unchanged. -/
theorem load_doubleword_of_loadDword? {s : SailJoltState} {a v : BitVec 64}
    (h : loadDword? s a = some v) : Mmu.load_doubleword a s = .ok (.Ok v) s := by
  unfold loadDword? at h
  split at h
  · rename_i w t ht
    cases h
    obtain ⟨rfl, -⟩ := load_doubleword_ok_inv ht
    exact ht
  · cases h

/-- `loadDword?` in closed form: an aligned RAM address reads the RAM map when it is readable,
and an address below RAM reads the device bytes.
Example: `loadDword? s 0x80000004 = none`, since the address is not a multiple of 8. -/
theorem loadDword?_eq (s : SailJoltState) (a : BitVec 64) :
    loadDword? s a =
      if a.toNat % 8 ≠ 0 then none
      else if RAM_START_ADDRESS ≤ a.toNat then
        (if Mmu.effective_address_ok s.jolt_device a.toNat false = true then
          some (Mmu.ram_doubleword s.sail.mem a.toNat) else none)
      else read_doubleword? (Mmu.load_raw? s) a.toNat := by
  unfold loadDword? Mmu.load_doubleword
  dsimp only
  by_cases h1 : a.toNat % 8 = 0
  · by_cases h2 : RAM_START_ADDRESS ≤ a.toNat
    · by_cases h3 : Mmu.effective_address_ok s.jolt_device a.toNat false = true
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]
    · simp only [h1, h2, ne_eq, not_true_eq_false, ite_false]
      cases read_doubleword? (Mmu.load_raw? s) a.toNat <;> rfl
  · simp [h1]

/-- What an `LD` reads depends only on the device and the RAM map, not on the registers.
Example: `loadDword? { s with vregs := f } 0x80010000 = loadDword? s 0x80010000`. -/
theorem loadDword?_congr {s t : SailJoltState} (hd : s.jolt_device = t.jolt_device)
    (hm : s.sail.mem = t.sail.mem) (a : BitVec 64) : loadDword? s a = loadDword? t a := by
  have hraw : Mmu.load_raw? s = Mmu.load_raw? t := by
    funext ea
    unfold Mmu.load_raw?
    simp only [hd, hm]
  rw [loadDword?_eq, loadDword?_eq, hd, hm, hraw]

/-- Register updates do not change what an `LD` reads.
Example: `loadDword? { s with vregs := setV s.vregs vr61 7 } a = loadDword? s a`. -/
@[simp] theorem loadDword?_vregs (s : SailJoltState) (f : VReg → BitVec 64) (a : BitVec 64) :
    loadDword? { s with vregs := f } a = loadDword? s a :=
  loadDword?_congr (s := { s with vregs := f }) (t := s) rfl rfl a

/-- A RAM doubleword load below the heap end reads the RAM map.
Example: `loadDword? s 0x80000000 = some (ram_doubleword s.sail.mem 0x80000000)` when the heap
ends above it. -/
theorem loadDword?_ram {s : SailJoltState} {a : BitVec 64} (halign : a.toNat % 8 = 0)
    (hram : RAM_START_ADDRESS ≤ a.toNat)
    (hok : Mmu.effective_address_ok s.jolt_device a.toNat false = true) :
    loadDword? s a = some (Mmu.ram_doubleword s.sail.mem a.toNat) := by
  unfold loadDword?
  rw [Mmu.load_doubleword_ram s a ((and_seven_eq_zero_iff a).2 halign) hram hok]

/-- An `LD` from a virtual destination at or above `vr32` through an architectural base that
reads `base`: the run continues exactly when the load succeeds, with the destination set.
Example: with `XReads s x10 0x80010000`, a run of `[LD vr48, 0(x10); rest]` from `s` is a run of
`rest` with `vr48` set to `v`, where `loadDword? s 0x80010000 = some v`. -/
theorem run_ld_iff {fc : LoadFaultClass} {d : VReg} (hd : 32 ≤ d.toNat) {r : regidx}
    {imm : BitVec 64} {s : SailJoltState} {base : BitVec 64} (hr : XReads s r base)
    (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (.LD fc (.vreg d) (.xreg r) imm :: rest)).Run s s' ↔
      ∃ v, loadDword? s (base + imm) = some v ∧
        (Program.seq rest).Run { s with vregs := setV s.vregs d v } s' := by
  have hw : WritableVReg d := by unfold WritableVReg; omega
  rw [seq_cons]
  cases hl : loadDword? s (base + imm) with
  | some v =>
    have hld := load_doubleword_of_loadDword? hl
    obtain ⟨-, -, hal⟩ := load_doubleword_ok_inv hld
    have hand : (base + imm) &&& 7 = 0 := (and_seven_eq_zero_iff _).2 hal
    have hrun : (execInstr (.LD fc (.vreg d) (.xreg r) imm)).run s =
        .ok RETIRE_SUCCESS { s with vregs := setV s.vregs d v } := by
      simp only [execInstr, EStateM.run, bind, hr.run, hand, ite_true, EStateM.bind, hld,
        writeDst_vreg]
      exact writeVReg_retire_run_of_writable _ _ s hw
    rw [run_instr_iff hrun]
    simp
  | none =>
    simp only [reduceCtorEq, false_and, exists_false, iff_false]
    intro hrun
    obtain ⟨t, ht, -⟩ := execProgram_instr_run_retire_inv _ _ _ _ hrun
    simp only [execInstr, EStateM.run, bind, EStateM.bind, hr.run] at ht
    split at ht
    · cases hm : Mmu.load_doubleword (base + imm) s with
      | error e σ => simp [EStateM.bind, hm] at ht
      | ok res σ =>
        obtain ⟨rfl, ⟨w, rfl⟩, -⟩ := load_doubleword_ok_inv hm
        unfold loadDword? at hl
        rw [hm] at hl
        cases hl
    · simp [pure, EStateM.pure, RETIRE_SUCCESS] at ht

/-- A run through an `LD` reads its base register.
Example: a run of `[LD vr48, 0(x10); rest]` from `s` gives `XReads s x10 v`, where `v` is the
value of `x10` in `s`. -/
theorem XReads.of_run_ld {fc : LoadFaultClass} {d : Dst} {r : regidx} {imm : BitVec 64}
    {rest : List Instr} {s s' : SailJoltState}
    (h : (Program.seq (.LD fc d (.xreg r) imm :: rest)).Run s s') :
    XReads s r (sourceValue (.xreg r) s) := by
  obtain ⟨t, ht, -⟩ := execProgram_instr_run_retire_inv _ _ _ _ h
  simp only [execInstr, EStateM.run, bind, EStateM.bind] at ht
  cases hr : JoltISA.readSrc (.xreg r) s with
  | error e σ => simp [hr] at ht
  | ok v σ =>
    have hx := XReads.of_readSrc hr
    rwa [← hx.eq_sourceValue]

/-! ## Stores -/

/-- The state after an `SD` of `v` at address `a` in state `s`, or `none` when Jolt's store
fails.
Example: `storeDword? s 0x80020000 7` writes `7` to the RAM map at `0x80020000` when that
address lies below the heap end and outside the stack canary. -/
def storeDword? (s : SailJoltState) (a v : BitVec 64) : Option SailJoltState :=
  match Mmu.store_doubleword a v s with
  | .ok (.Ok _) t => some t
  | _ => none

/-- A doubleword store that returns reports success at an aligned address.
Example: if `Mmu.store_doubleword 0x80020000 7 s = .ok r t`, then `r = .Ok b` for some `b`. -/
theorem store_doubleword_ok_inv {a v : BitVec 64} {s t : SailJoltState}
    {r : Result Bool ExecutionResult} (h : Mmu.store_doubleword a v s = .ok r t) :
    (∃ b, r = .Ok b) ∧ a.toNat % 8 = 0 := by
  simp only [Mmu.store_doubleword] at h
  repeat' split at h
  all_goals first | (cases h; exact ⟨⟨_, rfl⟩, by omega⟩) | cases h

/-- The store behind a `storeDword?` state.
Example: if `storeDword? s 0x80020000 7 = some t`, then `Mmu.store_doubleword 0x80020000 7 s`
succeeds and ends in `t`. -/
theorem store_doubleword_of_storeDword? {s t : SailJoltState} {a v : BitVec 64}
    (h : storeDword? s a v = some t) : ∃ b, Mmu.store_doubleword a v s = .ok (.Ok b) t := by
  unfold storeDword? at h
  split at h
  · rename_i b t' ht
    cases h
    exact ⟨b, ht⟩
  · cases h

/-- A RAM doubleword store outside the stack canary and below the heap end writes the RAM
map.
Example: `storeDword? s 0x80020000 7` is `s` with `write_ram_doubleword s.sail.mem 0x80020000 7`
as its RAM map. -/
theorem storeDword?_ram {s : SailJoltState} {a : BitVec 64} (v : BitVec 64)
    (halign : a.toNat % 8 = 0) (hram : RAM_START_ADDRESS ≤ a.toNat)
    (hok : Mmu.effective_address_ok s.jolt_device a.toNat true = true) :
    storeDword? s a v =
      some { s with
        sail := { s.sail with mem := Mmu.write_ram_doubleword s.sail.mem a.toNat v } } := by
  unfold storeDword?
  rw [Mmu.store_doubleword_ram s a v ((and_seven_eq_zero_iff a).2 halign) hram hok]

/-- A successful RAM store is the closed form, and its address was writable.
Example: `storeDword? s 0x80020000 7 = some t` gives that `0x80020000` is writable and `t` is `s`
with `write_ram_doubleword s.sail.mem 0x80020000 7` as its RAM map. -/
theorem storeDword?_ram_inv {s t : SailJoltState} {a v : BitVec 64}
    (hram : RAM_START_ADDRESS ≤ a.toNat) (h : storeDword? s a v = some t) :
    a.toNat % 8 = 0 ∧ Mmu.effective_address_ok s.jolt_device a.toNat true = true ∧
      t = { s with
        sail := { s.sail with mem := Mmu.write_ram_doubleword s.sail.mem a.toNat v } } := by
  obtain ⟨b, hb⟩ := store_doubleword_of_storeDword? h
  have hal := (store_doubleword_ok_inv hb).2
  have hnot : ¬ a.toNat % 8 ≠ 0 := by omega
  by_cases hok : Mmu.effective_address_ok s.jolt_device a.toNat true = true
  · refine ⟨hal, hok, ?_⟩
    rw [storeDword?_ram v hal hram hok] at h
    exact (Option.some.inj h).symm
  · exfalso
    simp only [Mmu.store_doubleword, hnot, hram, ite_false, ite_true, hok] at hb
    cases hb

/-- An `SD` of a virtual register through an architectural base that reads `base`: the run
continues exactly when the store succeeds.
Example: with `XReads s x12 0x80020000`, a run of `[SD x12, vr62, 0; rest]` from `s` is a run of
`rest` from `t`, where `storeDword? s 0x80020000 (s.vregs vr62) = some t`. -/
theorem run_sd_iff {x : VReg} {r : regidx} {imm : BitVec 64} {s : SailJoltState}
    {base : BitVec 64} (hr : XReads s r base) (rest : List Instr) (s' : SailJoltState) :
    (Program.seq (.SD (.xreg r) (.vreg x) imm :: rest)).Run s s' ↔
      ∃ t, storeDword? s (base + imm) (s.vregs x) = some t ∧ (Program.seq rest).Run t s' := by
  rw [seq_cons]
  cases hl : storeDword? s (base + imm) (s.vregs x) with
  | some t =>
    obtain ⟨b, hst⟩ := store_doubleword_of_storeDword? hl
    have hal := (store_doubleword_ok_inv hst).2
    have hand : (base + imm) &&& 7 = 0 := (and_seven_eq_zero_iff _).2 hal
    have hrun : (execInstr (.SD (.xreg r) (.vreg x) imm)).run s = .ok RETIRE_SUCCESS t := by
      simp only [execInstr, EStateM.run, bind, EStateM.bind, hr.run, readSrc_vreg,
        readVReg_run, hand, ite_true, hst, pure, EStateM.pure]
    rw [run_instr_iff hrun]
    simp
  | none =>
    simp only [reduceCtorEq, false_and, exists_false, iff_false]
    intro hrun
    obtain ⟨t, ht, -⟩ := execProgram_instr_run_retire_inv _ _ _ _ hrun
    simp only [execInstr, EStateM.run, bind, EStateM.bind, hr.run, readSrc_vreg,
      readVReg_run] at ht
    split at ht
    · cases hm : Mmu.store_doubleword (base + imm) (s.vregs x) s with
      | error e σ => simp [EStateM.bind, hm] at ht
      | ok res σ =>
        obtain ⟨⟨w, rfl⟩, -⟩ := store_doubleword_ok_inv hm
        unfold storeDword? at hl
        rw [hm] at hl
        cases hl
    · simp [pure, EStateM.pure, RETIRE_SUCCESS] at ht

/-- A run through an `SD` reads its base register.
Example: a run of `[SD x12, vr62, 0; rest]` from `s` gives `XReads s x12 v`, where `v` is the
value of `x12` in `s`. -/
theorem XReads.of_run_sd {r : regidx} {val : Src} {imm : BitVec 64}
    {rest : List Instr} {s s' : SailJoltState}
    (h : (Program.seq (.SD (.xreg r) val imm :: rest)).Run s s') :
    XReads s r (sourceValue (.xreg r) s) := by
  obtain ⟨t, ht, -⟩ := execProgram_instr_run_retire_inv _ _ _ _ h
  simp only [execInstr, EStateM.run, bind, EStateM.bind] at ht
  cases hr : JoltISA.readSrc (.xreg r) s with
  | error e σ => simp [hr] at ht
  | ok v σ =>
    have hx := XReads.of_readSrc hr
    rwa [← hx.eq_sourceValue]

/-! ## Reading back RAM -/

/-- A RAM doubleword reads back what was stored at the same address.
Example: `ram_doubleword (write_ram_doubleword m 0x80020000 7) 0x80020000 = 7`. -/
theorem ram_doubleword_write_same (m : Std.ExtHashMap Nat (BitVec 8)) (ea : Nat)
    (v : BitVec 64) : Mmu.ram_doubleword (Mmu.write_ram_doubleword m ea v) ea = v := by
  unfold Mmu.ram_doubleword Mmu.write_ram_doubleword Mmu.ram_byte
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.foldl_cons,
    List.foldl_nil, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
  simp
  show @Eq (BitVec (8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)) _ _
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  repeat rw [BitVec.getLsbD_append]
  simp only [BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

/-- A RAM doubleword that does not overlap a store keeps its value.
Example: storing limb `1` of a result leaves limb `0` in place. -/
theorem ram_doubleword_write_ne (m : Std.ExtHashMap Nat (BitVec 8)) (ea b : Nat)
    (v : BitVec 64) (h : ea + 8 ≤ b ∨ b + 8 ≤ ea) :
    Mmu.ram_doubleword (Mmu.write_ram_doubleword m ea v) b = Mmu.ram_doubleword m b := by
  have hbyte : ∀ c, b ≤ c → c < b + 8 → Mmu.ram_byte (Mmu.write_ram_doubleword m ea v) c =
      Mmu.ram_byte m c := by
    intro c hc1 hc2
    unfold Mmu.ram_byte Mmu.write_ram_doubleword
    rw [foldl_insert_get?_of_ne]
    intro k hk
    simp only [List.mem_range] at hk
    omega
  unfold Mmu.ram_doubleword
  rw [hbyte b (by omega) (by omega), hbyte (b + 1) (by omega) (by omega),
    hbyte (b + 2) (by omega) (by omega), hbyte (b + 3) (by omega) (by omega),
    hbyte (b + 4) (by omega) (by omega), hbyte (b + 5) (by omega) (by omega),
    hbyte (b + 6) (by omega) (by omega), hbyte (b + 7) (by omega) (by omega)]

end JoltISA.Inlines
