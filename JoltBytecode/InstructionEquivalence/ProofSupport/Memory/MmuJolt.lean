import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Basic

open LeanRV64D

/-
Facts about Jolt's own memory access (`JoltISA.Mmu`, following Rust's MMU) that
need no Sail reasoning: what LD and SD do when Rust's checks pass.
-/

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

namespace JoltISA.Mmu

theorem toNat_mod_eight_of_align {addr : BitVec 64} (halign : addr &&& 7 = 0) :
    addr.toNat % 8 = 0 := by
  have h := congrArg BitVec.toNat halign
  rw [BitVec.toNat_and] at h
  have h7 : (7 : BitVec 64).toNat = 7 := by decide
  have h0 : (0 : BitVec 64).toNat = 0 := by decide
  rw [h7, h0, show (7 : Nat) = 2 ^ 3 - 1 from by norm_num,
    Nat.and_two_pow_sub_one_eq_mod] at h
  exact h

-- The Jolt RAM assumptions are exactly Rust's checks passing for a RAM address.
theorem effective_address_ok_of_load {js : SailJoltState} {addr : BitVec 64}
    (hram : RAM_START_ADDRESS ≤ addr.toNat) (h : Assumptions.JoltRamLoadOk addr js) :
    effective_address_ok js.jolt_device addr.toNat false = true := by
  have hlt : ¬ addr.toNat < RAM_START_ADDRESS := by omega
  simp [effective_address_ok, hlt, h.below_backing_end]

theorem effective_address_ok_of_store {js : SailJoltState} {addr value : BitVec 64} {width : Nat}
    (hram : RAM_START_ADDRESS ≤ addr.toNat) (h : Assumptions.JoltRamStoreOk addr js value width) :
    effective_address_ok js.jolt_device addr.toNat true = true := by
  have hlt : ¬ addr.toNat < RAM_START_ADDRESS := by omega
  simp [effective_address_ok, hlt, h.below_backing_end]

/-- The protected-store check reads only the layout, the code guard and memory.
For example, a register write between a load and a store does not change it.
Based on Quang Dao's `protected_store_ok_congr` in PR #73. -/
theorem assert_write_protected_store_congr {s t : SailJoltState} (address : Nat)
    (value : BitVec 64) (width : Nat)
    (hlayout : t.jolt_device.memory_layout = s.jolt_device.memory_layout)
    (hcode : t.code_guard = s.code_guard) (hmem : t.sail.mem = s.sail.mem) :
    assert_write_protected_store t address value width =
      assert_write_protected_store s address value width := by
  simp only [assert_write_protected_store, ram_doubleword, ram_byte, JoltDevice.is_input,
    JoltDevice.is_trusted_advice, JoltDevice.is_untrusted_advice, hlayout, hcode, hmem]
  rfl

-- With the byte present, the zero-filled direct read and Sail's lookup agree.
theorem ram_byte_eq_loaded_byte_at (s : SailState) (v : BitVec 64)
    (h : MemBytePresentAt s v.toNat) :
    ram_byte s.mem v.toNat = loaded_byte_at s v h := by
  unfold ram_byte loaded_byte_at loaded_byte_at_nat
  rw [Option.get_eq_getD (fallback := 0)]

-- With all 8 bytes present, the direct 64-bit read is Sail's loaded dword.
theorem ram_doubleword_eq_loaded_dword_at (s : SailState) (addr : BitVec 64)
    (hbytes : MemBytesPresentAt s addr 8) (h_no_ovf : addr.toNat + 7 < 2 ^ 64) :
    ram_doubleword s.mem addr.toNat = loaded_dword_at s addr hbytes h_no_ovf := by
  have hk : ∀ k : Nat, k < 8 → (addr + BitVec.ofNat 64 k).toNat = addr.toNat + k :=
    fun k hk => toNat_add_small_of_no_ovf addr k (by omega)
  unfold ram_doubleword loaded_dword_at
  simp only [← ram_byte_eq_loaded_byte_at]
  rw [show (addr + 7).toNat = addr.toNat + 7 from hk 7 (by omega),
    show (addr + 6).toNat = addr.toNat + 6 from hk 6 (by omega),
    show (addr + 5).toNat = addr.toNat + 5 from hk 5 (by omega),
    show (addr + 4).toNat = addr.toNat + 4 from hk 4 (by omega),
    show (addr + 3).toNat = addr.toNat + 3 from hk 3 (by omega),
    show (addr + 2).toNat = addr.toNat + 2 from hk 2 (by omega),
    show (addr + 1).toNat = addr.toNat + 1 from hk 1 (by omega)]

-- Jolt's 64-bit RAM read when Rust's checks pass.
theorem load_doubleword_ram (js : SailJoltState) (addr : BitVec 64)
    (halign : addr &&& 7 = 0) (hram : RAM_START_ADDRESS ≤ addr.toNat)
    (hlegal : effective_address_ok js.jolt_device addr.toNat false = true) :
    load_doubleword addr js = .ok (.Ok (ram_doubleword js.sail.mem addr.toNat)) js := by
  have hmod := toNat_mod_eight_of_align halign
  simp [load_doubleword, hmod, hram, hlegal]

-- Jolt's 64-bit RAM write when Rust's checks pass.
theorem store_doubleword_ram (js : SailJoltState) (addr value : BitVec 64)
    (halign : addr &&& 7 = 0) (hram : RAM_START_ADDRESS ≤ addr.toNat)
    (hlegal : effective_address_ok js.jolt_device addr.toNat true = true)
    (hprotected : assert_write_protected_store js addr.toNat value 8 = true) :
    store_doubleword addr value js =
      .ok (.Ok true)
        { js with sail := { js.sail with mem := write_ram_doubleword js.sail.mem addr.toNat value } } := by
  have hmod := toNat_mod_eight_of_align halign
  simp [store_doubleword, hmod, hram, hlegal, hprotected]

-- A one-byte load changes no state.
theorem load_state {address : BitVec 64} {s t : SailJoltState}
    {v : Result (BitVec 8) ExecutionResult}
    (h : load address s = .ok v t) : t = s := by
  simp only [load] at h
  split at h
  all_goals first | (cases h; rfl) | cases h

-- A load changes no state.
theorem load_doubleword_state {address : BitVec 64} {s t : SailJoltState}
    {v : Result (BitVec 64) ExecutionResult}
    (h : load_doubleword address s = .ok v t) : t = s := by
  simp only [load_doubleword] at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

-- A store changes only memory and the device, never the registers.
theorem store_raw_regs {s s' : SailJoltState} {ea : Nat} {v : BitVec 8}
    (h : store_raw? s ea v = some s') :
    s'.sail.regs = s.sail.regs ∧ s'.vregs = s.vregs := by
  simp only [store_raw?] at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨rfl, rfl⟩)
    | cases h
    | (cases hst : s.jolt_device.store? s.sail.mem ea v <;> simp [hst] at h; cases h; exact ⟨rfl, rfl⟩)

theorem store_bytes_regs (ea : Nat) (value : BitVec 64) :
    ∀ (l : List Nat) (o : Option SailJoltState) (s0 s' : SailJoltState),
      (∀ s, o = some s → s.sail.regs = s0.sail.regs ∧ s.vregs = s0.vregs) →
      l.foldl (fun current k => current.bind fun s =>
        store_raw? s (ea + k) (value.extractLsb' (8 * k) 8)) o = some s' →
      s'.sail.regs = s0.sail.regs ∧ s'.vregs = s0.vregs := by
  intro l
  induction l with
  | nil => intro o s0 s' ho h; exact ho s' h
  | cons k rest ih =>
      intro o s0 s' ho h
      simp only [List.foldl] at h
      apply ih _ s0 s' _ h
      intro s hs
      cases o with
      | none => simp at hs
      | some s1 =>
          simp only [Option.bind] at hs
          obtain ⟨hregs, hvregs⟩ := store_raw_regs hs
          obtain ⟨hregs1, hvregs1⟩ := ho s1 rfl
          exact ⟨hregs.trans hregs1, hvregs.trans hvregs1⟩

theorem store_doubleword_regs {address value : BitVec 64} {s t : SailJoltState}
    {v : Result Bool ExecutionResult}
    (h : store_doubleword address value s = .ok v t) :
    t.sail.regs = s.sail.regs ∧ t.vregs = s.vregs := by
  simp only [store_doubleword] at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨rfl, rfl⟩)
    | (rename_i heq
       cases h
       exact store_bytes_regs _ value _ (some s) s _
         (fun s' hs => by cases hs; exact ⟨rfl, rfl⟩) heq)
    | cases h

/-! ## Protected shared memory

Based on Quang Dao's protected-memory facts in `Memory/MmuJolt.lean` (PR #73), restated for
`assert_write_protected_store`, which tests each touched doubleword as Jolt's tracer does. -/

/-- Comparing one byte lane of two doublewords is comparing the bytes.
For example, at lane 3 only bits 24 to 31 of each side matter. -/
private theorem masked_byte_eq_iff (x : BitVec 64) (v : BitVec 8) (off : Nat) (hoff : off < 8) :
    (x &&& ((BitVec.allOnes 64 >>> (64 - 8)) <<< (8 * off))) =
        ((v.zeroExtend 64 >>> (8 * 0)) <<< (8 * off) &&&
          ((BitVec.allOnes 64 >>> (64 - 8)) <<< (8 * off))) ↔
      x.extractLsb' (8 * off) 8 = v := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun y => y.getLsbD (8 * off + i)) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_allOnes, BitVec.getLsbD_setWidth] at this
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    have h1 : 8 * off + i < 64 := by omega
    have h2 : ¬ 8 * off + i < 8 * off := by omega
    simp [h1, h2, show 8 * off + i - 8 * off = i by omega, show 56 + i < 64 by omega, hi] at this
    simpa [h1, hi, show i < 64 by omega] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_allOnes, BitVec.getLsbD_setWidth]
    by_cases hin : 8 * off ≤ i ∧ i < 8 * off + 8
    · have hx := congrArg (fun y => y.getLsbD (i - 8 * off)) h
      simp only [BitVec.getLsbD_extractLsb', show i - 8 * off < 8 by omega, decide_true,
        Bool.true_and, show 8 * off + (i - 8 * off) = i by omega] at hx
      simp [hi, show ¬ i < 8 * off by omega, show 64 - 8 + (i - 8 * off) < 64 by omega,
        show i - 8 * off < 8 by omega, show i - 8 * off < 64 by omega]
      simpa [hi, show i - 8 * off < 8 by omega] using hx
    · by_cases hlt : i < 8 * off
      · simp [hlt]
      · simp [hlt, hi, show ¬ (64 - 8 + (i - 8 * off) < 64) by omega]

/-- Byte `k` of the doubleword at `ea` is the byte at `ea + k`.
For example, lane 0 is the byte at `ea` itself. -/
theorem ram_doubleword_extract (mem : Std.ExtHashMap Nat (BitVec 8)) (ea k : Nat) (hk : k < 8) :
    (ram_doubleword mem ea).extractLsb' (8 * k) 8 = ram_byte mem (ea + k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb']
  simp only [hi, decide_true, Bool.true_and]
  unfold ram_doubleword
  simp only [BitVec.getLsbD_append]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  split_ifs <;> first | omega | (congr 1; omega)

/-- Whether the doubleword holding `address` is write-protected: it lies in the guarded code
interval or an input or advice region, or it overlaps the stack canary.
For example, every byte of an input word is protected.
This is the test `assert_write_protected_store` applies to each doubleword a store touches. -/
def protected_byte (state : SailJoltState) (address : Nat) : Bool :=
  let word := address / 8 * 8
  let device := state.jolt_device
  let layout := device.memory_layout
  let index := (word - layout.get_lowest_address.toNat) / 8
  (state.code_guard.any fun guard => guard.region.1 ≤ index && index < guard.region.2) ||
    device.is_input word || device.is_trusted_advice word || device.is_untrusted_advice word ||
    (layout.stack_end.toNat ≤ word + 7 && word < layout.stack_end.toNat + STACK_CANARY_SIZE)

/-- Protection depends only on the layout and the code guard.
For example, writing an output byte does not move the protected input interval. -/
theorem protected_byte_congr {s t : SailJoltState} (address : Nat)
    (hlayout : t.jolt_device.memory_layout = s.jolt_device.memory_layout)
    (hcode : t.code_guard = s.code_guard) :
    protected_byte t address = protected_byte s address := by
  simp only [protected_byte, JoltDevice.is_input, JoltDevice.is_trusted_advice,
    JoltDevice.is_untrusted_advice, hlayout, hcode]

/-- Bytes of one doubleword share its protection.
For example, the eight bytes of an aligned input word are all protected. -/
theorem protected_byte_aligned (s : SailJoltState) (ea k : Nat) (aligned : ea % 8 = 0)
    (hk : k < 8) : protected_byte s (ea + k) = protected_byte s ea := by
  unfold protected_byte
  rw [show (ea + k) / 8 * 8 = ea / 8 * 8 by omega]

/-- The layout, the code guard and every protected byte agree between two states.
Bytes use the zero-default shared-memory reading of Jolt's tracer.
For example, this relation keeps input, advice, code and canary bytes and allows output writes. -/
structure ProtectedMemory (s t : SailJoltState) : Prop where
  layout : t.jolt_device.memory_layout = s.jolt_device.memory_layout
  code : t.code_guard = s.code_guard
  bytes : ∀ address, protected_byte s address = true →
    ram_byte t.sail.mem address = ram_byte s.sail.mem address

/-- An unchanged state keeps every protected byte; for example, a load. -/
theorem ProtectedMemory.refl (s : SailJoltState) : ProtectedMemory s s :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- Protected-memory agreement composes.
For example, two accepted same-value code stores keep the original code bytes. -/
theorem ProtectedMemory.trans {s t u : SailJoltState} (hst : ProtectedMemory s t)
    (htu : ProtectedMemory t u) : ProtectedMemory s u := by
  refine ⟨htu.layout.trans hst.layout, htu.code.trans hst.code, ?_⟩
  intro address hp
  have hpt : protected_byte t address = true := by
    rw [protected_byte_congr address hst.layout hst.code]; exact hp
  exact (htu.bytes address hpt).trans (hst.bytes address hp)

private theorem insert_keeps_protected (s : SailJoltState)
    (mem : Std.ExtHashMap Nat (BitVec 8)) (address : Nat) (value : BitVec 8)
    (keeps : ∀ a, protected_byte s a = true → ram_byte mem a = ram_byte s.sail.mem a)
    (accepted : protected_byte s address = true → ram_byte s.sail.mem address = value) :
    ∀ a, protected_byte s a = true →
      ram_byte (mem.insert address value) a = ram_byte s.sail.mem a := by
  intro a hp
  by_cases heq : address = a
  · subst a
    simpa only [ram_byte, Std.ExtHashMap.get?_eq_getElem?,
      Std.ExtHashMap.getElem?_insert_self, Option.getD_some] using
      (accepted hp).symm
  · simpa [ram_byte, Std.ExtHashMap.getElem?_insert, heq] using keeps a hp

/-- A one-byte protection check accepts exactly the writes that keep a protected byte.
For example, a new output byte and the existing input byte both pass. -/
theorem assert_write_protected_store_byte_iff (s : SailJoltState) (address : Nat)
    (value : BitVec 8) :
    assert_write_protected_store s address (value.zeroExtend 64) 1 = true ↔
      (protected_byte s address = true → ram_byte s.sail.mem address = value) := by
  have hword : (address + 1 - 1) / 8 * 8 = address / 8 * 8 := by simp
  have hoff : address - address / 8 * 8 < 8 := by omega
  have hstart : max address (address / 8 * 8) = address := by omega
  have hstop : min (address + 1) (address / 8 * 8 + 8) = address + 1 := by omega
  unfold assert_write_protected_store protected_byte
  simp only [hword, ite_true, List.all_cons, List.all_nil, Bool.and_true, hstart, hstop,
    show address + 1 - address = 1 by omega, Nat.sub_self, Nat.mul_zero]
  split
  · rename_i free
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at free
    simp only [true_iff, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    intro hp
    exfalso
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := free
    simp only [h1, h2, h3, h4, Bool.false_eq_true, or_false, false_or] at hp
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at h5
    omega
  · rename_i guarded
    have key := masked_byte_eq_iff (ram_doubleword s.sail.mem (address / 8 * 8)) value
      (address - address / 8 * 8) hoff
    rw [ram_doubleword_extract _ _ _ hoff,
      show address / 8 * 8 + (address - address / 8 * 8) = address by omega] at key
    simp only [beq_iff_eq, Nat.mul_one]
    constructor
    · intro h _; exact key.mp h
    · intro h
      apply key.mpr
      apply h
      revert guarded
      cases (s.code_guard.any fun guard =>
          guard.region.1 ≤ (address / 8 * 8 - s.jolt_device.memory_layout.get_lowest_address.toNat) / 8 &&
          (address / 8 * 8 - s.jolt_device.memory_layout.get_lowest_address.toNat) / 8 < guard.region.2) <;>
        cases s.jolt_device.is_input (address / 8 * 8) <;>
        cases s.jolt_device.is_trusted_advice (address / 8 * 8) <;>
        cases s.jolt_device.is_untrusted_advice (address / 8 * 8) <;> simp

/-- An aligned doubleword check accepts exactly the writes that keep a protected word.
For example, storing an input word's existing value passes. -/
theorem assert_write_protected_store_aligned_iff (s : SailJoltState) (ea : Nat)
    (value : BitVec 64) (aligned : ea % 8 = 0) :
    assert_write_protected_store s ea value 8 = true ↔
      (protected_byte s ea = true → ram_doubleword s.sail.mem ea = value) := by
  have hfirst : ea / 8 * 8 = ea := by omega
  have hlast : (ea + 8 - 1) / 8 * 8 = ea := by omega
  unfold assert_write_protected_store protected_byte
  simp only [hfirst, hlast, ite_true, List.all_cons, List.all_nil, Bool.and_true, max_self,
    min_self, show ea + 8 - ea = 8 by omega, Nat.sub_self, Nat.mul_zero,
    BitVec.ushiftRight_zero, BitVec.shiftLeft_zero]
  split
  · rename_i free
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at free
    simp only [true_iff, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    intro hp
    exfalso
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := free
    simp only [h1, h2, h3, h4, Bool.false_eq_true, or_false, false_or] at hp
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at h5
    omega
  · rename_i guarded
    have hmask : BitVec.allOnes 64 >>> (64 - 8 * 8) = BitVec.allOnes 64 := by
      simp
    simp only [BitVec.and_allOnes, beq_iff_eq]
    constructor
    · intro h _; exact h
    · intro h
      apply h
      revert guarded
      cases (s.code_guard.any fun guard =>
          guard.region.1 ≤ (ea - s.jolt_device.memory_layout.get_lowest_address.toNat) / 8 &&
          (ea - s.jolt_device.memory_layout.get_lowest_address.toNat) / 8 < guard.region.2) <;>
        cases s.jolt_device.is_input ea <;>
        cases s.jolt_device.is_trusted_advice ea <;>
        cases s.jolt_device.is_untrusted_advice ea <;> simp

/-- A successful raw byte store keeps every protected byte.
For example, changing an input byte cannot succeed. -/
theorem store_raw_protected {s t : SailJoltState} {address : Nat} {value : BitVec 8}
    (stored : store_raw? s address value = some t) : ProtectedMemory s t := by
  have hc : assert_write_protected_store s address (value.zeroExtend 64) 1 = true := by
    cases hcheck : assert_write_protected_store s address (value.zeroExtend 64) 1 with
    | true => rfl
    | false => simp [store_raw?, hcheck] at stored
  have keeps := insert_keeps_protected s s.sail.mem address value
    (fun _ _ => rfl) ((assert_write_protected_store_byte_iff s address value).mp hc)
  simp only [store_raw?, JoltDevice.store?] at stored
  repeat' split at stored
  all_goals first
    | (cases stored; exact ProtectedMemory.refl s)
    | (cases stored; exact ⟨rfl, rfl, keeps⟩)
    | cases stored

private theorem write_doubleword_keeps_protected (s : SailJoltState) (ea : Nat)
    (value : BitVec 64) (aligned : ea % 8 = 0)
    (accepted : assert_write_protected_store s ea value 8 = true) :
    ∀ a, protected_byte s a = true →
      ram_byte (write_ram_doubleword s.sail.mem ea value) a = ram_byte s.sail.mem a := by
  have word := (assert_write_protected_store_aligned_iff s ea value aligned).mp accepted
  unfold write_ram_doubleword
  refine List.foldlRecOn (motive := fun mem => ∀ a, protected_byte s a = true →
    ram_byte mem a = ram_byte s.sail.mem a) (List.range 8) _ (fun _ _ => rfl) ?_
  intro mem keeps k hk
  have hk8 : k < 8 := List.mem_range.mp hk
  apply insert_keeps_protected s mem (ea + k) (value.extractLsb' (8 * k) 8) keeps
  intro hp
  rw [protected_byte_aligned s ea k aligned hk8] at hp
  rw [← word hp, ram_doubleword_extract _ _ _ hk8]

/-- A retiring doubleword store keeps every protected byte, the layout and the code guard.
For example, storing the existing doubleword into the canary succeeds and keeps it. -/
theorem store_doubleword_protected (address value : BitVec 64) (s t : SailJoltState)
    (result : Result Bool ExecutionResult)
    (stored : store_doubleword address value s = .ok result t) : ProtectedMemory s t := by
  simp only [store_doubleword] at stored
  split at stored
  · cases stored
  · rename_i aligned
    split at stored
    · split at stored
      · rename_i checked
        have hc := (Bool.and_eq_true_iff.mp checked).2
        cases stored
        exact ⟨rfl, rfl, write_doubleword_keeps_protected s _ value (by omega) hc⟩
      · cases stored
    · split at stored
      · rename_i hfold
        cases stored
        exact List.foldlRecOn
          (motive := fun current => ∀ t, current = some t → ProtectedMemory s t)
          (List.range 8) _ (fun t ht => by cases ht; exact ProtectedMemory.refl s)
          (fun current keeps k _ t ht => by
            cases current with
            | none => cases ht
            | some middle =>
              exact (keeps middle rfl).trans (store_raw_protected ht)) _ hfold
      · cases stored

end JoltISA.Mmu

/-- Transport a store assumption between states with the same layout, code guard and memory.
For example, a register write before the store keeps the assumption.
Based on Quang Dao's version in PR #73. -/
theorem Assumptions.JoltRamStoreOk.transfer {s t : SailJoltState}
    {addr value : BitVec 64} {width : Nat}
    (h : Assumptions.JoltRamStoreOk addr s value width)
    (hlayout : t.jolt_device.memory_layout = s.jolt_device.memory_layout)
    (hcode : t.code_guard = s.code_guard) (hmem : t.sail.mem = s.sail.mem) :
    Assumptions.JoltRamStoreOk addr t value width :=
  ⟨by simpa only [JoltISA.Mmu.ram_backing_end, hlayout] using h.below_backing_end,
   by rw [JoltISA.Mmu.assert_write_protected_store_congr _ _ _ hlayout hcode hmem]
      exact h.preserves_protected⟩
