import JoltBytecode.Inlines.StraightLineMemory

/-!
# Advice stores: rows that write prover-chosen words to consecutive doublewords

Several inlines store runtime advice words to an output buffer, one word per pair of rows:

```text
VirtualAdvice vd, w₀;  SD vd, off(rs)
VirtualAdvice vd, w₁;  SD vd, off+8(rs)
...
```

`adviceStoreRows r d off ws` builds these rows for any number of words, and
`run_adviceStoreRows_iff` says exactly when they run: every target doubleword in RAM is aligned
and writable, and the state afterwards is `afterStores`, with the words written by
`writeDwords`. `loadDword?_of_mem_writeDwords` reads the words back.

Every lemma is proved; the module has no `sorry`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D
  LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace JoltISA.Inlines

/-! ## Definitions -/

/-- The doubleword at address `ea` is 8-aligned and `effective_address_ok` lets Jolt store to
it. The predicate does not require `ea` to be in RAM (an aligned output-window address also
satisfies it); the lemmas that use it take `RAM_START_ADDRESS ≤ ea` as a separate hypothesis.
Example: with the stack ending at `0x8000_1000` and the heap at `0x8010_0000`, the address
`0x8002_0000` is writable and `0x8002_0004` is not (misaligned). -/
def DwordWritable (dev : JoltDevice) (ea : Nat) : Prop :=
  ea % 8 = 0 ∧ Mmu.effective_address_ok dev ea true = true

/-- The RAM map after storing the words `ws` at consecutive doublewords from `ea`.
Example: `writeDwords m 0x8002_0000 [7, 9]` stores `7` at `0x8002_0000` and `9` at
`0x8002_0008`. -/
def writeDwords (m : Std.ExtHashMap Nat (BitVec 8)) (ea : Nat) :
    List (BitVec 64) → Std.ExtHashMap Nat (BitVec 8)
  | [] => m
  | w :: ws => writeDwords (Mmu.write_ram_doubleword m ea w) (ea + 8) ws

/-- The rows that store the words `ws` through virtual register `d` to consecutive doublewords
at offsets `off, off + 8, …` from architectural base register `r`.
Example: `GLVR_ADV` is `adviceStoreRows rs3 vr48 0 [w₀, …, w₅]` followed by a reset of `vr48`. -/
def adviceStoreRows (r : regidx) (d : VReg) (off : Nat) : List (BitVec 64) → List Instr
  | [] => []
  | w :: ws =>
    .VirtualAdvice (.vreg d) w 0 :: .SD (.xreg r) (.vreg d) (BitVec.ofNat 64 off) ::
      adviceStoreRows r d (off + 8) ws

/-- The state after `adviceStoreRows` from `s`, when its first store goes to RAM address `ea`.
Example: `afterStores s d ea []` is `s`. -/
def afterStores (s : SailJoltState) (d : VReg) (ea : Nat) : List (BitVec 64) → SailJoltState
  | [] => s
  | w :: ws =>
    afterStores { s with vregs := setV s.vregs d w,
                         sail := { s.sail with mem := Mmu.write_ram_doubleword s.sail.mem ea w } }
      d (ea + 8) ws

/-! ## The state after the stores -/

/-- Writing the same register twice keeps the second value.
Example: `setV (setV f vr48 7) vr48 0 = setV f vr48 0`. -/
theorem setV_setV (f : VReg → BitVec 64) (d : VReg) (a b : BitVec 64) :
    setV (setV f d a) d b = setV f d b := by
  funext r
  by_cases h : r = d <;> simp [setV, h]

/-- The stores change only the RAM map and register `d`; a later write to `d` hides the advice
values.
Example: after storing `[7]` through `vr48` and then setting `vr48 := 0`, the state is `s` with
`vr48 = 0` and `7` in RAM. -/
theorem afterStores_setV (s : SailJoltState) (d : VReg) (v : BitVec 64) (ea : Nat)
    (ws : List (BitVec 64)) :
    { afterStores s d ea ws with vregs := setV (afterStores s d ea ws).vregs d v } =
      { s with vregs := setV s.vregs d v,
               sail := { s.sail with mem := writeDwords s.sail.mem ea ws } } := by
  induction ws generalizing s ea with
  | nil => rfl
  | cons w ws ih =>
    simp only [afterStores, writeDwords]
    rw [ih]
    simp only [setV_setV]

/-! ## Running the rows -/

/-- A run of an empty row list ends where it starts.
Example: `(Program.seq []).Run s s'` holds exactly when `s' = s`. -/
theorem run_nil_iff (s s' : SailJoltState) : (Program.seq []).Run s s' ↔ s' = s := by
  simp only [Program.seq, List.foldr, Program.Run, execProgram_done, EStateM.run, pure,
    EStateM.pure]
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    rfl

/-- **The advice-store rows.** Let base register `r` read `C`, with the stores in RAM and no
address wrapping. A run of `adviceStoreRows r d off ws ++ rest` from `s` is exactly a run of
`rest` from `afterStores s d (C + off) ws`, and it exists only when every target doubleword is
aligned and writable.
Example: with `x12` reading `0x8002_0000`, a run of `adviceStoreRows x12 vr48 0 [7, 9] ++ rest`
is a run of `rest` from `s` with `7` at `0x8002_0000`, `9` at `0x8002_0008` and `vr48 = 9`. -/
theorem run_adviceStoreRows_iff {r : regidx} {d : VReg} (hd : 32 ≤ d.toNat) {C : BitVec 64}
    (hC : RAM_START_ADDRESS ≤ C.toNat) (off : Nat) (ws : List (BitVec 64)) (s : SailJoltState)
    (hr : XReads s r C) (hw : C.toNat + off + 8 * ws.length ≤ 2 ^ 64) (rest : List Instr)
    (s' : SailJoltState) :
    (Program.seq (adviceStoreRows r d off ws ++ rest)).Run s s' ↔
      (∀ k < ws.length, DwordWritable s.jolt_device (C.toNat + off + 8 * k)) ∧
        (Program.seq rest).Run (afterStores s d (C.toNat + off) ws) s' := by
  induction ws generalizing off s with
  | nil => simp [adviceStoreRows, afterStores]
  | cons w ws ih =>
    simp only [List.length_cons] at hw
    have hoff : off < 2 ^ 64 := by omega
    have haddr : (C + BitVec.ofNat 64 off).toNat = C.toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff,
        Nat.mod_eq_of_lt (by omega)]
    have hram : RAM_START_ADDRESS ≤ (C + BitVec.ofNat 64 off).toNat := by rw [haddr]; omega
    have hrow : (Instr.VirtualAdvice (.vreg d) w 0).regRow? = some (d, fun _ => w) := rfl
    rw [adviceStoreRows, List.cons_append, List.cons_append, seq_cons,
      run_instr_iff (execInstr_of_regRow hrow hd s),
      run_sd_iff (hr.vregs (setV s.vregs d w))]
    simp only [setV_same]
    have hr2 := XReads.of_regs (s := s)
      (t := ({ s with vregs := setV s.vregs d w,
                      sail := { s.sail with
                        mem := Mmu.write_ram_doubleword s.sail.mem (C.toNat + off) w } } :
        SailJoltState)) rfl hr
    have hih := ih (off + 8) _ hr2 (by omega)
    rw [show C.toNat + (off + 8) = C.toNat + off + 8 by omega] at hih
    simp only [afterStores, List.length_cons]
    constructor
    · rintro ⟨t, ht, hrun⟩
      obtain ⟨hal, hok, rfl⟩ := storeDword?_ram_inv hram ht
      rw [haddr] at hal hok hrun
      obtain ⟨hall, hrest⟩ := hih.1 hrun
      refine ⟨fun k hk => ?_, hrest⟩
      cases k with
      | zero => exact ⟨by simpa using hal, by simpa using hok⟩
      | succ k =>
        have h := hall k (by omega)
        rwa [show C.toNat + off + 8 * (k + 1) = C.toNat + off + 8 + 8 * k by omega]
    · rintro ⟨hall, hrest⟩
      have h0 := hall 0 (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at h0
      refine ⟨_, storeDword?_ram w (by rw [haddr]; exact h0.1) hram
        (by rw [haddr]; exact h0.2), ?_⟩
      rw [haddr]
      refine hih.2 ⟨fun k hk => ?_, hrest⟩
      have h := hall (k + 1) (by omega)
      rwa [show C.toNat + off + 8 * (k + 1) = C.toNat + off + 8 + 8 * k by omega] at h

/-! ## Reading the words back -/

/-- A RAM address Jolt may store to, it may also load from.
Example: if Jolt may store to `0x8002_0000`, it may also load from it. -/
theorem effective_address_ok_read_of_write {dev : JoltDevice} {ea : Nat}
    (hram : RAM_START_ADDRESS ≤ ea) (h : Mmu.effective_address_ok dev ea true = true) :
    Mmu.effective_address_ok dev ea false = true := by
  have hn : ¬ ea < RAM_START_ADDRESS := by omega
  simp only [Mmu.effective_address_ok, hn, ite_false, ite_true, Bool.false_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact h.2

/-- Stores at or above `ea` leave a doubleword that ends by `ea` unchanged.
Example: storing at `ea = 0x8000_0010` leaves the doubleword at `0x8000_0008`. -/
theorem ram_doubleword_writeDwords_of_le (m : Std.ExtHashMap Nat (BitVec 8)) (ea b : Nat)
    (ws : List (BitVec 64)) (h : b + 8 ≤ ea) :
    Mmu.ram_doubleword (writeDwords m ea ws) b = Mmu.ram_doubleword m b := by
  induction ws generalizing m ea with
  | nil => rfl
  | cons w ws ih =>
    rw [writeDwords, ih _ _ (by omega), ram_doubleword_write_ne _ _ _ _ (Or.inr h)]

/-- Doubleword `i` of the stored words reads back.
Example: after `writeDwords m 0x8002_0000 [7, 9]`, the doubleword at `0x8002_0008` (`i = 1`)
is `9`. -/
theorem ram_doubleword_writeDwords_get (m : Std.ExtHashMap Nat (BitVec 8)) (ea : Nat)
    (ws : List (BitVec 64)) (i : Nat) (hi : i < ws.length) :
    Mmu.ram_doubleword (writeDwords m ea ws) (ea + 8 * i) = ws[i] := by
  induction ws generalizing m ea i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero =>
      simp only [writeDwords, Nat.mul_zero, Nat.add_zero]
      rw [ram_doubleword_writeDwords_of_le _ _ _ _ (by omega), ram_doubleword_write_same]
      rfl
    | succ j =>
      rw [writeDwords, show ea + 8 * (j + 1) = ea + 8 + 8 * j by omega,
        ih _ _ _ (by simpa using hi)]
      rfl

/-- **Read-back.** If the RAM map of `t` holds the words `ws` stored from `C`, at addresses Jolt
may store to, then loading doubleword `i` returns word `i`.
Example: if the RAM map of `t` is `writeDwords m 0x8002_0000 [7, 9]`, then
`loadDword? t (0x8002_0000 + 8) = some 9`. -/
theorem loadDword?_of_mem_writeDwords {t : SailJoltState} {m : Std.ExtHashMap Nat (BitVec 8)}
    {C : BitVec 64} {ws : List (BitVec 64)} (hm : t.sail.mem = writeDwords m C.toNat ws)
    (hC : RAM_START_ADDRESS ≤ C.toNat) (hw : C.toNat + 8 * ws.length ≤ 2 ^ 64)
    (hok : ∀ k < ws.length, DwordWritable t.jolt_device (C.toNat + 8 * k)) {i : Nat}
    (hi : i < ws.length) :
    loadDword? t (C + BitVec.ofNat 64 (8 * i)) = ws[i]? := by
  have haddr : (C + BitVec.ofNat 64 (8 * i)).toNat = C.toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hki := hok i hi
  rw [loadDword?_ram (by rw [haddr]; exact hki.1) (by rw [haddr]; omega)
      (by rw [haddr]; exact effective_address_ok_read_of_write (by omega) hki.2),
    haddr, hm, ram_doubleword_writeDwords_get _ _ _ _ hi, List.getElem?_eq_getElem hi]

end JoltISA.Inlines
