import JoltConstraints.translation.metadata
import JoltConstraints.theorems.layout_facts

open LeanRV64D JoltISA
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail

set_option autoImplicit false

namespace JoltConstraints

/-- The input and advice areas start on doubleword boundaries.
For example, every layout `MemoryLayout.new` builds qualifies (`new_advice_regions`). -/
def RegionsWordAligned (layout : MemoryLayout) : Prop :=
  layout.input_start.toNat % 8 = 0 ∧ layout.trusted_advice_start.toNat % 8 = 0 ∧
    layout.untrusted_advice_start.toNat % 8 = 0

/-- Every layout `MemoryLayout.new` builds starts its input and advice areas on doubleword
boundaries; for example, the input area starts where the higher advice area ends.
Jolt at `504dd78a2`: `common/src/jolt_device.rs` (`MemoryLayout::try_new`). -/
theorem RegionsWordAligned.of_new {config : MemoryConfig} {layout : MemoryLayout}
    (built : MemoryLayout.new config = some layout) : RegionsWordAligned layout := by
  obtain ⟨_, trustedMultiple, _, untrustedMultiple, trustedEnd, untrustedEnd, _, trustedStart,
    untrustedStart, inputStart⟩ := new_advice_regions config layout built
  refine ⟨?_, trustedStart, untrustedStart⟩
  rw [inputStart]
  omega

/-- Two byte maps read the same byte at every address, with the tracer's zero default.
For example, a map with no entry at an address agrees with one holding zero there. -/
def SameBytes (mem mem' : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ address, Mmu.ram_byte mem address = Mmu.ram_byte mem' address

/-- Inserting the same byte keeps two maps reading alike.
For example, a store into either of two agreeing maps leaves them agreeing. -/
theorem SameBytes.insert {mem mem' : Std.ExtHashMap Nat (BitVec 8)} (same : SameBytes mem mem')
    (address : Nat) (value : BitVec 8) :
    SameBytes (mem.insert address value) (mem'.insert address value) := by
  intro other
  by_cases here : address = other
  · subst other; simp [Mmu.ram_byte]
  · simpa [Mmu.ram_byte, Std.ExtHashMap.getElem?_insert, here] using same other

/-- Maps that read alike pack the same doublewords.
For example, a map with no entry and one holding zero give the same word. -/
theorem SameBytes.ram_doubleword {mem mem' : Std.ExtHashMap Nat (BitVec 8)}
    (same : SameBytes mem mem') (address : Nat) :
    Mmu.ram_doubleword mem address = Mmu.ram_doubleword mem' address := by
  unfold SameBytes at same
  simp only [Mmu.ram_doubleword, same]

/-- With word-aligned areas, every input or advice byte lies in a protected doubleword.
For example, the first input byte's word is the input area's first word. -/
theorem protected_of_io (state : SailJoltState)
    (aligned : RegionsWordAligned state.jolt_device.memory_layout) (address : Nat)
    (io : (state.jolt_device.is_input address || state.jolt_device.is_trusted_advice address ||
      state.jolt_device.is_untrusted_advice address) = true) :
    Mmu.protected_byte state address = true := by
  obtain ⟨hi, ht, hu⟩ := aligned
  have word : address / 8 * 8 ≤ address := Nat.div_mul_le_self address 8
  unfold Mmu.protected_byte
  simp only [JoltDevice.is_input, JoltDevice.is_trusted_advice, JoltDevice.is_untrusted_advice,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at io ⊢
  rcases io with (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩)))
  · exact Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
  · exact Or.inl (Or.inr ⟨by omega, by omega⟩)

/-- An accepted byte store changes only shared memory, which then reads as the old map
with the byte inserted.
An input or advice store keeps its byte, as Jolt's tracer returns without writing;
for example, rewriting an input byte with its own value leaves memory as it was.
Jolt at `504dd78a2`: `tracer/src/emulator/mmu.rs` (`Mmu::store_raw`).
Adapted from Quang Dao's version in PR #73, whose store wrote the byte back. -/
theorem store_raw_shape (before after : SailJoltState) (address : Nat) (value : BitVec 8)
    (aligned : RegionsWordAligned before.jolt_device.memory_layout)
    (stored : Mmu.store_raw? before address value = some after) :
    after = { before with sail := { before.sail with mem := after.sail.mem } } ∧
      SameBytes after.sail.mem (before.sail.mem.insert address value) := by
  have checked : Mmu.assert_write_protected_store before address (value.zeroExtend 64) 1 =
      true := by
    cases h : Mmu.assert_write_protected_store before address (value.zeroExtend 64) 1 with
    | true => rfl
    | false => simp [Mmu.store_raw?, h] at stored
  have keeps := (Mmu.assert_write_protected_store_byte_iff before address value).mp checked
  unfold Mmu.store_raw? at stored
  split at stored
  · split at stored
    · cases stored
    · split at stored
      · cases stored
      · cases stored; exact ⟨rfl, fun _ => rfl⟩
  · split at stored
    · cases stored
    · split at stored
      · cases stored
      · split at stored
        · cases stored
        · split at stored
          · rename_i io
            cases stored
            refine ⟨rfl, fun other => ?_⟩
            by_cases here : address = other
            · subst other
              simp only [Mmu.ram_byte, Std.ExtHashMap.get?_eq_getElem?,
                Std.ExtHashMap.getElem?_insert_self, Option.getD_some]
              exact keeps (protected_of_io before aligned address io)
            · simp [Mmu.ram_byte, Std.ExtHashMap.getElem?_insert, here]
          · unfold JoltDevice.store? at stored
            split at stored
            · simp only [Option.map_some] at stored
              cases stored; exact ⟨rfl, fun _ => rfl⟩
            · cases stored

/-- A run of guarded byte stores reads as the plain insertions, with only memory changed.
For example, eight accepted byte stores read as the eight inserted bytes. -/
private theorem store_bytes_shape (address : Nat) (value : BitVec 64) (before : SailJoltState)
    (aligned : RegionsWordAligned before.jolt_device.memory_layout) :
    ∀ (offsets : List Nat) (start : SailJoltState) (reference : Std.ExtHashMap Nat (BitVec 8))
      (after : SailJoltState),
      start = { before with sail := { before.sail with mem := start.sail.mem } } →
      SameBytes start.sail.mem reference →
      offsets.foldl (fun current k => current.bind fun state =>
        Mmu.store_raw? state (address + k) (value.extractLsb' (8 * k) 8)) (some start) =
          some after →
      after = { before with sail := { before.sail with mem := after.sail.mem } } ∧
        SameBytes after.sail.mem (offsets.foldl
          (fun mem k => mem.insert (address + k) (value.extractLsb' (8 * k) 8)) reference) := by
  intro offsets
  induction offsets with
  | nil =>
    intro start reference after shape same stored
    cases stored
    exact ⟨shape, same⟩
  | cons offset rest ih =>
    intro start reference after shape same stored
    simp only [List.foldl_cons, Option.bind_some] at stored
    cases next : Mmu.store_raw? start (address + offset) (value.extractLsb' (8 * offset) 8) with
    | none =>
      rw [next, List.foldl_fixed' (fun _ => rfl) rest] at stored
      cases stored
    | some middle =>
      rw [next] at stored
      have startAligned : RegionsWordAligned start.jolt_device.memory_layout := by
        rw [shape]; exact aligned
      obtain ⟨middleShape, middleSame⟩ := store_raw_shape start middle _ _ startAligned next
      refine ih middle _ after ?_ ?_ stored
      · rw [middleShape, shape]
      · intro other
        rw [middleSame other]
        exact SameBytes.insert same _ _ other

/-- Every successful doubleword store changes only shared memory, which then reads as
the old map with the doubleword written, in RAM and in the I/O window alike.
For example, a gap-word store writes all eight little-endian bytes.
Jolt at `504dd78a2`: `tracer/src/emulator/mmu.rs` (`Mmu::store_doubleword_raw`).
Adapted from Quang Dao's version in PR #73. -/
theorem store_doubleword_shape (before after : SailJoltState) (address value : BitVec 64)
    (result : Result Bool ExecutionResult)
    (aligned : RegionsWordAligned before.jolt_device.memory_layout)
    (stored : Mmu.store_doubleword address value before = .ok result after) :
    after = { before with sail := { before.sail with mem := after.sail.mem } } ∧
      SameBytes after.sail.mem
        (Mmu.write_ram_doubleword before.sail.mem address.toNat value) := by
  simp only [Mmu.store_doubleword] at stored
  split at stored
  · cases stored
  · split at stored
    · split at stored
      · cases stored; exact ⟨rfl, fun _ => rfl⟩
      · cases stored
    · split at stored
      · rename_i afterBytes byteStores
        cases stored
        exact store_bytes_shape address.toNat value before aligned (List.range 8) before
          before.sail.mem _ rfl (fun _ => rfl) byteStores
      · cases stored

/-- A non-store row preserves the shared byte map, including a halt row.
For example, a panic halt updates its CPU marker but changes no memory byte.
Jolt at `ff6fc6568`: `tracer/src/emulator/cpu.rs` (`Cpu::halt`). -/
theorem nonstore_memory (instruction : Instr)
    (notStore : JoltMetadata.opcodeFlag instruction .Store = false) :
    StatePreservation.Preserves (fun s t => t.sail.mem = s.sail.mem)
      (execInstr instruction) := by
  let rules : InstructionFrame.NonStoreRules
      (fun s t => t.sail.mem = s.sail.mem) := {
    refl := fun _ => rfl
    trans := fun _ _ _ ab bc => bc.trans ab
    sail := fun _ _ same => same
    vreg := fun _ _ _ => rfl
    halt := fun _ _ => rfl
    append := fun _ _ => rfl }
  apply InstructionFrame.execInstr_rule_of_store rules instruction
  · intro base value imm same
    subst instruction
    cases notStore
  · intro base value imm fault same
    rcases same with rfl | rfl | rfl <;> cases notStore
  · intro _ _ _ _ _ _ _
    rfl


/-- A successful checked byte read returns its byte in the shared map.
For example, an untouched mapped gap byte returns the map's zero default.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`Mmu::load_raw`). -/
theorem load_raw_value (state : SailJoltState) (address : Nat) (value : BitVec 8)
    (loaded : Mmu.load_raw? state address = some value) :
    value = Mmu.ram_byte state.sail.mem address := by
  simp only [Mmu.load_raw?, JoltDevice.load?] at loaded
  repeat' split at loaded
  all_goals cases loaded
  all_goals rfl

/-- Reading eight accepted bytes packs their shared-memory values.
For example, eight reads starting at address eight form its little-endian word. -/
private theorem read_doubleword_value (mem : Std.ExtHashMap Nat (BitVec 8))
    (byte : Nat → Option (BitVec 8))
    (shape : ∀ address value, byte address = some value → value = Mmu.ram_byte mem address)
    (address : Nat) (value : BitVec 64)
    (loaded : read_doubleword? byte address = some value) :
    value = Mmu.ram_doubleword mem address := by
  unfold read_doubleword? at loaded
  split at loaded
  · rename_i b0 b1 b2 b3 b4 b5 b6 b7 h0 h1 h2 h3 h4 h5 h6 h7
    cases loaded
    simp only [Mmu.ram_doubleword, shape _ _ h0, shape _ _ h1, shape _ _ h2,
      shape _ _ h3, shape _ _ h4, shape _ _ h5, shape _ _ h6, shape _ _ h7]
  · cases loaded

/-- A successful doubleword load returns the shared map's packed word in both
RAM and I/O; for example, a load in the output region reads its stored bytes.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`Mmu::load_doubleword`). -/
theorem load_doubleword_shape (before after : SailJoltState) (address : BitVec 64)
    (result : Result (BitVec 64) ExecutionResult)
    (loaded : Mmu.load_doubleword address before = .ok result after) :
    result = .Ok (Mmu.ram_doubleword before.sail.mem address.toNat) ∧ after = before := by
  simp only [Mmu.load_doubleword] at loaded
  split at loaded
  · cases loaded
  · split at loaded
    · split at loaded
      · cases loaded
        exact ⟨rfl, rfl⟩
      · cases loaded
    · split at loaded
      · rename_i recorded reads
        cases loaded
        exact ⟨congrArg Result.Ok (read_doubleword_value before.sail.mem
          (Mmu.load_raw? before) (load_raw_value before) address.toNat recorded reads), rfl⟩
      · cases loaded

/-- A captured doubleword is exactly the shared-memory word it records.
For example, capturing an I/O gap word needs no separate device overlay.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`device_doubleword`). -/
theorem trace_doubleword_value (state : SailJoltState) (address value : BitVec 64)
    (recorded : trace_doubleword? state address = some value) :
    value = Mmu.ram_doubleword state.sail.mem address.toNat := by
  simp only [trace_doubleword?] at recorded
  split at recorded
  · apply read_doubleword_value state.sail.mem (state.jolt_device.load? state.sail.mem)
      (fun address value loaded => ?_) address.toNat value recorded
    unfold JoltDevice.load? at loaded
    split at loaded
    · exact (Option.some.inj loaded).symm
    · cases loaded
  · split at recorded
    · exact (Option.some.inj recorded).symm
    · cases recorded

/-- Extracting byte `k` of a shared doubleword returns its byte at offset `k`.
For example, byte zero is its least significant byte, regardless of map presence.
This byte-packing fact is a candidate to move to JoltBytecode. -/
theorem ram_doubleword_byte (memory : Std.ExtHashMap Nat (BitVec 8)) (address k : Nat)
    (within : k < 8) :
    (Mmu.ram_doubleword memory address).extractLsb' (8 * k) 8 =
      Mmu.ram_byte memory (address + k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Mmu.ram_doubleword, BitVec.getLsbD_extractLsb',
    show (i <b 8) = true by simpa using hi, Bool.true_and]
  repeat rw [BitVec.getLsbD_append]
  split_ifs <;> congr 2 <;> omega

/-- A checked shared-byte read succeeds when peripheral dispatch is excluded.
For example, a mapped but absent output byte returns zero. -/
private theorem load_raw_of_checks (state : SailJoltState) (address : Nat)
    (checked : Mmu.effective_address_ok state.jolt_device address false = true)
    (peripheral : Mmu.unsupported_load address = false) :
    Mmu.load_raw? state address = some (Mmu.ram_byte state.sail.mem address) := by
  by_cases inRam : RAM_START_ADDRESS ≤ address
  · simp only [Mmu.load_raw?, checked, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, inRam]
  · have readable : state.jolt_device.readable address = true := by
      simpa only [Mmu.effective_address_ok, ite_eq_left (Nat.lt_of_not_ge inRam)] using checked
    simp only [Mmu.load_raw?, checked, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, inRam, peripheral, JoltDevice.load?, readable]
    rfl

/-- Address and peripheral checks suffice for a shared doubleword load.
For example, an input word and an ordinary RAM word return their packed map bytes.
This primitive MMU fact is a candidate to move to JoltBytecode. -/
theorem load_doubleword_of_checks (state : SailJoltState) (address : BitVec 64)
    (aligned : address &&& 7 = 0)
    (checked : ∀ k < 8, Mmu.effective_address_ok state.jolt_device (address.toNat + k) false = true)
    (peripheral : ∀ k < 8, Mmu.unsupported_load (address.toNat + k) = false) :
    Mmu.load_doubleword address state =
      .ok (.Ok (Mmu.ram_doubleword state.sail.mem address.toNat)) state := by
  have raw (k : Nat) (within : k < 8) := load_raw_of_checks state (address.toNat + k)
    (checked k within) (peripheral k within)
  have zero := raw 0 (by decide)
  simp only [Nat.add_zero] at zero
  simp only [Mmu.load_doubleword, Mmu.toNat_mod_eight_of_align aligned,
    ne_self_iff_false, ↓reduceIte]
  split
  · have start := checked 0 (by decide)
    simp only [Nat.add_zero] at start
    simp only [start, ↓reduceIte]
  · simp only [read_doubleword?, zero, raw 1 (by decide), raw 2 (by decide),
      raw 3 (by decide), raw 4 (by decide), raw 5 (by decide),
      raw 6 (by decide), raw 7 (by decide)]
    rfl

/-- A byte store with successful address and protection checks succeeds.
For example, a value-preserving protected input store is admitted. -/
private theorem store_raw_of_checks (state : SailJoltState) (address : Nat) (value : BitVec 8)
    (checked : Mmu.effective_address_ok state.jolt_device address true = true)
    (peripheral : Mmu.unsupported_store address = false)
    (preservesProtected :
      Mmu.assert_write_protected_store state address (value.zeroExtend 64) 1 = true) :
    ∃ after, Mmu.store_raw? state address value = some after := by
  cases stored : Mmu.store_raw? state address value with
  | some after => exact ⟨after, rfl⟩
  | none =>
    exfalso
    by_cases inRam : RAM_START_ADDRESS ≤ address
    · simp [Mmu.store_raw?, checked, preservesProtected, inRam] at stored
    · have readable : state.jolt_device.readable address = true := by
        simpa only [Mmu.effective_address_ok, ite_eq_left (Nat.lt_of_not_ge inRam)] using checked
      simp [Mmu.store_raw?, checked, preservesProtected, inRam, peripheral, JoltDevice.store?,
        readable] at stored
      split_ifs at stored

/-- Address, peripheral and protected-value checks suffice for a doubleword store
in the shared map, including I/O; memory then reads as the written doubleword.
For example, replacing an input word by itself succeeds and preserves the device.
Adapted from Quang Dao's version in PR #73. -/
theorem store_doubleword_of_checks (state : SailJoltState) (address value : BitVec 64)
    (aligned : address &&& 7 = 0)
    (checked : ∀ k < 8, Mmu.effective_address_ok state.jolt_device (address.toNat + k) true = true)
    (peripheral : ∀ k < 8, Mmu.unsupported_store (address.toNat + k) = false)
    (preservesProtected : Mmu.assert_write_protected_store state address.toNat value 8 = true)
    (regions : RegionsWordAligned state.jolt_device.memory_layout) :
    ∃ after, Mmu.store_doubleword address value state = .ok (.Ok true) after ∧
      after = { state with sail := { state.sail with mem := after.sail.mem } } ∧
      SameBytes after.sail.mem (Mmu.write_ram_doubleword state.sail.mem address.toNat value) := by
  have wordAligned : address.toNat % 8 = 0 := Mmu.toNat_mod_eight_of_align aligned
  by_cases inRam : RAM_START_ADDRESS ≤ address.toNat
  · exact ⟨_, Mmu.store_doubleword_ram state address value aligned inRam
      (by simpa only [Nat.add_zero] using checked 0 (by decide)) preservesProtected,
      rfl, fun _ => rfl⟩
  · have word := (Mmu.assert_write_protected_store_aligned_iff state address.toNat value
      wordAligned).mp preservesProtected
    have folded : ∃ after,
        (List.range 8).foldl (fun current k => current.bind fun s =>
          Mmu.store_raw? s (address.toNat + k) (value.extractLsb' (8 * k) 8))
          (some state) = some after := by
      have step : ∀ k ∈ List.range 8, ∀ middle : SailJoltState, Mmu.ProtectedMemory state middle →
          ∃ next, Mmu.store_raw? middle (address.toNat + k) (value.extractLsb' (8 * k) 8) =
            some next ∧ Mmu.ProtectedMemory state next := by
        intro k member middle keeps
        have within : k < 8 := List.mem_range.mp member
        have currentCheck : Mmu.effective_address_ok middle.jolt_device
            (address.toNat + k) true = true := by
          simpa only [Mmu.effective_address_ok, Mmu.ram_backing_end, keeps.layout,
            JoltDevice.readable, JoltDevice.is_input, JoltDevice.is_trusted_advice,
            JoltDevice.is_untrusted_advice, JoltDevice.is_output, JoltDevice.is_io_gap]
            using! checked k within
        have currentProtected : Mmu.assert_write_protected_store middle (address.toNat + k)
            ((value.extractLsb' (8 * k) 8).zeroExtend 64) 1 = true := by
          apply (Mmu.assert_write_protected_store_byte_iff middle _ _).mpr
          intro hp
          have original : Mmu.protected_byte state (address.toNat + k) = true := by
            rwa [Mmu.protected_byte_congr _ keeps.layout keeps.code] at hp
          rw [keeps.bytes _ original, ← Mmu.ram_doubleword_extract _ _ _ within]
          rw [Mmu.protected_byte_aligned state _ k wordAligned within] at original
          rw [word original]
        obtain ⟨next, stored⟩ := store_raw_of_checks middle (address.toNat + k)
          (value.extractLsb' (8 * k) 8) currentCheck (peripheral k within) currentProtected
        exact ⟨next, stored, keeps.trans (Mmu.store_raw_protected stored)⟩
      have invariant := List.foldlRecOn (motive := fun current => ∃ after,
        current = some after ∧ Mmu.ProtectedMemory state after) (List.range 8)
        (fun current k => current.bind fun s =>
          Mmu.store_raw? s (address.toNat + k) (value.extractLsb' (8 * k) 8))
        (b := some state) ⟨state, rfl, Mmu.ProtectedMemory.refl state⟩
        (fun current prior k member => by
          obtain ⟨middle, rfl, keeps⟩ := prior
          obtain ⟨next, stored, nextKeeps⟩ := step k member middle keeps
          exact ⟨next, by simp only [Option.bind_some, stored], nextKeeps⟩)
      obtain ⟨after, bytes, _⟩ := invariant
      exact ⟨after, bytes⟩
    obtain ⟨after, bytes⟩ := folded
    have executed : Mmu.store_doubleword address value state = .ok (.Ok true) after := by
      simp only [Mmu.store_doubleword, wordAligned, ne_eq, not_true_eq_false, ↓reduceIte,
        inRam, bytes]
    exact ⟨after, executed, store_doubleword_shape state after address value _ regions executed⟩

end JoltConstraints
