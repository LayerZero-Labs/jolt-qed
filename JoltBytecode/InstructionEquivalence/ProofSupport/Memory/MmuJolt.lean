import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.Basic

/-
Facts about Jolt's own memory access (`JoltISA.Mmu`, following Rust's MMU) that
need no Sail reasoning: what LD and SD do when Rust's checks pass.
-/

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

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
  simp [effective_address_ok, hlt, h.below_heap_end]

theorem effective_address_ok_of_store {js : SailJoltState} {addr : BitVec 64}
    (hram : RAM_START_ADDRESS ≤ addr.toNat) (h : Assumptions.JoltRamStoreOk addr js) :
    effective_address_ok js.jolt_device addr.toNat true = true := by
  have hlt : ¬ addr.toNat < RAM_START_ADDRESS := by omega
  simp [effective_address_ok, hlt, h.below_heap_end, h.outside_canary]

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
    (hlegal : effective_address_ok js.jolt_device addr.toNat true = true) :
    store_doubleword addr value js =
      .ok (.Ok true)
        { js with sail := { js.sail with mem := write_ram_doubleword js.sail.mem addr.toNat value } } := by
  have hmod := toNat_mod_eight_of_align halign
  simp [store_doubleword, hmod, hram, hlegal]

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
    | (cases hst : s.jolt_device.store? ea v <;> simp [hst] at h; cases h; exact ⟨rfl, rfl⟩)

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

end JoltISA.Mmu
