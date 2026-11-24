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

/-- Transport a protected-store check across unchanged layout, code interval and memory.
For example, AMO register updates do not change the acceptance of its eventual store. -/
theorem protected_store_ok_congr {s t : SailJoltState} (addr : Nat)
    (value : BitVec 64) (width : Nat)
    (hlayout : t.jolt_device.memory_layout = s.jolt_device.memory_layout)
    (hcode : t.codeRegion = s.codeRegion) (hmem : t.sail.mem = s.sail.mem) :
    protected_store_ok t addr value width = protected_store_ok s addr value width := by
  simp only [protected_store_ok, protected_byte, ram_byte, JoltDevice.is_input,
    JoltDevice.is_trusted_advice, JoltDevice.is_untrusted_advice, hlayout, hcode, hmem]

/-- Protection depends only on the static MMU layout and code interval.
For example, writing an output byte does not move the protected input interval. -/
theorem protected_byte_congr {s t : SailJoltState} (address : Nat)
    (hlayout : t.jolt_device.memory_layout = s.jolt_device.memory_layout)
    (hcode : t.codeRegion = s.codeRegion) :
    protected_byte t address = protected_byte s address := by
  simp only [protected_byte, JoltDevice.is_input, JoltDevice.is_trusted_advice,
    JoltDevice.is_untrusted_advice, hlayout, hcode]

/-- Static MMU setup and every protected byte agree between states.
Bytes use the zero-default shared-memory interpretation of the tracer.
For example, this relation preserves input, advice, code and canary values while allowing output writes. -/
structure ProtectedMemory (s t : SailJoltState) : Prop where
  layout : t.jolt_device.memory_layout = s.jolt_device.memory_layout
  code : t.codeRegion = s.codeRegion
  bytes : ∀ address, protected_byte s address = true →
    ram_byte t.sail.mem address = ram_byte s.sail.mem address

/-- An unchanged state preserves all protected bytes; for example, a load. -/
theorem ProtectedMemory.refl (s : SailJoltState) : ProtectedMemory s s :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- Compose protected-memory preservation across two fragments.
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

/-- A one-byte protection check accepts exactly value-preserving protected writes.
For example, either a new output value or the existing input value passes. -/
theorem protected_store_byte_iff (s : SailJoltState) (address : Nat) (value : BitVec 8) :
    protected_store_ok s address (value.zeroExtend 64) 1 = true ↔
      (protected_byte s address = true → ram_byte s.sail.mem address = value) := by
  have hbyte : (value.zeroExtend 64).extractLsb' 0 8 = value := by
    exact (BitVec.extractLsb'_setWidth_of_le (by decide)).trans BitVec.extractLsb'_eq_self
  cases hp : protected_byte s address <;> simp [protected_store_ok, hp, hbyte]

/-- An address accepted by the MMU permits storing its existing byte.
For example, a protected canary byte can be written back unchanged.
The peripheral condition excludes dispatches that Jolt's tracer always faults on. -/
theorem store_raw_existing (s : SailJoltState) (address : Nat)
    (haddress : effective_address_ok s.jolt_device address true = true)
    (hperipheral : unsupported_store address = false) :
    store_raw? s address (ram_byte s.sail.mem address) =
      some { s with sail := { s.sail with
        mem := s.sail.mem.insert address (ram_byte s.sail.mem address) } } := by
  have hc := (protected_store_byte_iff s address (ram_byte s.sail.mem address)).mpr
    (fun _ => rfl)
  by_cases hram : RAM_START_ADDRESS ≤ address
  · simp [store_raw?, haddress, hc, hram]
  · have hbelow : address < RAM_START_ADDRESS := by omega
    have hread : s.jolt_device.readable address = true := by
      simpa only [effective_address_ok, if_pos hbelow] using haddress
    simp [store_raw?, haddress, hc, hram, hperipheral, JoltDevice.store?, hread]

/-- A successful raw byte store preserves every protected shared-memory byte.
For example, changing an input byte cannot produce a successful result. -/
theorem store_raw_protected {s t : SailJoltState} {address : Nat} {value : BitVec 8}
    (stored : store_raw? s address value = some t) : ProtectedMemory s t := by
  have hc : protected_store_ok s address (value.zeroExtend 64) 1 = true := by
    cases hcheck : protected_store_ok s address (value.zeroExtend 64) 1 with
    | true => rfl
    | false => simp [store_raw?, hcheck] at stored
  have keeps := insert_keeps_protected s s.sail.mem address value
    (fun _ _ => rfl) ((protected_store_byte_iff s address value).mp hc)
  simp only [store_raw?, JoltDevice.store?] at stored
  repeat' split at stored
  all_goals cases stored <;> exact ⟨rfl, rfl, keeps⟩

private theorem write_doubleword_keeps_protected (s : SailJoltState) (address : Nat)
    (value : BitVec 64) (accepted : protected_store_ok s address value 8 = true) :
    ∀ a, protected_byte s a = true →
      ram_byte (write_ram_doubleword s.sail.mem address value) a = ram_byte s.sail.mem a := by
  unfold write_ram_doubleword
  refine List.foldlRecOn (motive := fun mem => ∀ a, protected_byte s a = true →
    ram_byte mem a = ram_byte s.sail.mem a) (List.range 8) _ (fun _ _ => rfl) ?_
  intro mem keeps k hk
  apply insert_keeps_protected s mem (address + k) (value.extractLsb' (8 * k) 8) keeps
  intro hp
  have h := List.all_eq_true.mp accepted k hk
  simpa only [hp, Bool.not_true, Bool.false_or, beq_iff_eq] using h

/-- A retiring doubleword store preserves every protected byte and static guard.
For example, storing the original doubleword into the canary succeeds and preserves it. -/
theorem store_doubleword_protected (address value : BitVec 64) (s t : SailJoltState)
    (result : Result Bool ExecutionResult)
    (stored : store_doubleword address value s = .ok result t) : ProtectedMemory s t := by
  simp only [store_doubleword] at stored
  split at stored
  · cases stored
  · split at stored
    · split at stored
      · rename_i checked
        have hc := (Bool.and_eq_true_iff.mp checked).2
        cases stored
        exact ⟨rfl, rfl, write_doubleword_keeps_protected s _ value hc⟩
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
    (hprotected : protected_store_ok js addr.toNat value 8 = true) :
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

end JoltISA.Mmu

/-- Transport successful-store premises through changes to registers or halt metadata.
For example, a pure AMO middle fragment preserves its memory and static MMU setup. -/
theorem Assumptions.JoltRamStoreOk.transfer {s t : SailJoltState}
    {addr value : BitVec 64} {width : Nat}
    (h : Assumptions.JoltRamStoreOk addr s value width)
    (hlayout : t.jolt_device.memory_layout = s.jolt_device.memory_layout)
    (hcode : t.codeRegion = s.codeRegion) (hmem : t.sail.mem = s.sail.mem) :
    Assumptions.JoltRamStoreOk addr t value width := by
  refine ⟨?_, ?_⟩
  · simpa only [JoltISA.Mmu.ram_backing_end, hlayout] using h.below_backing_end
  · rw [JoltISA.Mmu.protected_store_ok_congr _ _ _ hlayout hcode hmem]
    exact h.preserves_protected
