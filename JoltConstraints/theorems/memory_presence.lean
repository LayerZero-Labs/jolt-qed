import JoltConstraints.theorems.execution_facts

open LeanRV64D

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions
set_option autoImplicit false

/-!
Recorded store words at `ff6fc6568` come from shared memory with zero defaults.
No flag-word geometry or induction on presence of hash-map keys is required.
For example, storing into an untouched I/O-gap word records an old word of zero.
-/

theorem initialRam_size (layout : MemoryLayout) (image : List (BitVec 64 × BitVec 8)) :
    (initialRam layout image).size = 8 * ((layout.get_total_memory_size.toNat + 7) / 8) := by
  have fold : ∀ (image : List (BitVec 64 × BitVec 8)) (ram : Array (BitVec 8)),
      (image.foldl (fun ram (address, byte) =>
        if JoltISA.RAM_START_ADDRESS ≤ address.toNat then
          ram.setIfInBounds (address.toNat - JoltISA.RAM_START_ADDRESS) byte else ram) ram).size = ram.size := by
    intro image
    induction image with
    | nil => intro ram; rfl
    | cons head tail ih =>
      intro ram
      rcases head with ⟨address, byte⟩
      rw [List.foldl_cons, ih]
      dsimp only
      split
      · exact Array.size_setIfInBounds
      · rfl
  unfold initialRam
  rw [fold]
  simp

private theorem aligned_backing_end_arithmetic (base lowest words : Nat)
    (baseAligned : base % 8 = 0) (lowestAligned : lowest % 8 = 0) :
    (base + (lowest + 8 * words - base)) % 8 = 0 := by
  omega

private theorem aligned_backing_end_option (base lowest : Nat) (domain : Option Nat)
    (baseAligned : base % 8 = 0) (lowestAligned : lowest % 8 = 0) :
    (base + (domain.map fun words => lowest + 8 * words - base).getD 0) % 8 = 0 := by
  cases domain with
  | none => simpa using baseAligned
  | some words => exact aligned_backing_end_arithmetic base lowest words baseAligned lowestAligned

private theorem backing_end_ge_heap_arithmetic (base lowest heap words : Nat)
    (below : lowest ≤ heap) (aligned : lowest % 8 = 0) (heapAligned : heap % 8 = 0)
    (rounded : (heap - lowest) / 8 ≤ words) :
    heap ≤ base + (lowest + 8 * words - base) := by omega

private theorem backing_end_ge_heap_option (base lowest heap : Nat) (domain : Option Nat)
    (lowestAligned : lowest % 8 = 0) (k : Nat) (present : domain = some k)
    (geometry : heap % 8 = 0 ∧ lowest ≤ heap ∧ (heap - lowest) / 8 ≤ k) :
    heap ≤ base + (domain.map fun words => lowest + 8 * words - base).getD 0 := by
  rw [present]
  exact backing_end_ge_heap_arithmetic base lowest heap k geometry.2.1 lowestAligned
    geometry.1 geometry.2.2

/-- A padded RAM domain is aligned when its remapping base is aligned.
For example, adding any number of eight-byte slots keeps the low three bits zero. -/
theorem ram_backing_end_aligned (device : JoltDevice)
    (aligned : device.memory_layout.get_lowest_address.toNat % 8 = 0) :
    JoltISA.Mmu.ram_backing_end device % 8 = 0 := by
  exact aligned_backing_end_option _ _ _ (by decide) aligned

private theorem backing_end_le_arithmetic (base lowest words bound : Nat)
    (baseBound : base ≤ bound) (totalBound : lowest + 8 * words ≤ bound) :
    base + (lowest + 8 * words - base) ≤ bound := by
  omega

private theorem backing_end_le_option (base lowest bound : Nat) (domain : Option Nat)
    (words : Nat) (present : domain = some words) (baseBound : base ≤ bound)
    (totalBound : lowest + 8 * words ≤ bound) :
    base + (domain.map fun k => lowest + 8 * k - base).getD 0 ≤ bound := by
  rw [present]
  exact backing_end_le_arithmetic base lowest words bound baseBound totalBound

/-- The padded RAM backing of a checked layout ends within the u64 address domain.
For example, its final aligned word can end exactly at `2^64` without wrapping
its first byte's address.
Jolt at `ff6fc6568`: `common/src/jolt_device.rs` (`MemoryLayout::try_new`). -/
theorem ram_backing_end_le_address_space (device : JoltDevice) (config : MemoryConfig)
    (built : MemoryLayout.new config = some device.memory_layout) :
    JoltISA.Mmu.ram_backing_end device ≤ 2 ^ 64 := by
  obtain ⟨words, checked⟩ := Option.isSome_iff_exists.mp (new_max_ram_k config _ built)
  have bound := (max_ram_k_spec device.memory_layout words checked).2.2.2
  exact backing_end_le_option JoltISA.RAM_START_ADDRESS _ _ _ words checked (by decide) bound

/-- The padded RAM domain reaches the configured heap end.
For example, padding can add accessible words after `heap_end`.
Only checked layouts, rather than arbitrary records of addresses, have this property. -/
theorem heap_end_le_ram_backing_end (device : JoltDevice) (config : MemoryConfig)
    (built : MemoryLayout.new config = some device.memory_layout) :
    device.memory_layout.heap_end.toNat ≤ JoltISA.Mmu.ram_backing_end device := by
  obtain ⟨k, checked⟩ := Option.isSome_iff_exists.mp (new_max_ram_k config _ built)
  exact backing_end_ge_heap_option _ _ _ _ (new_lowest_address_aligned config _ built)
    k checked (by
      obtain ⟨heapAligned, below, sizeIs, _⟩ := max_ram_k_spec _ k checked
      refine ⟨heapAligned, below, ?_⟩
      rw [sizeIs]
      exact Nat.le_nextPowerOfTwo _)

private theorem padded_size_lt_arithmetic (base total bound : Nat)
    (basePositive : 0 < base) (boundPositive : 0 < bound) (totalBound : total ≤ bound) :
    total - base < bound := by omega

private theorem padded_size_lt_option (base lowest bound : Nat) (domain : Option Nat)
    (k : Nat) (present : domain = some k) (basePositive : 0 < base)
    (boundPositive : 0 < bound) (totalBound : lowest + 8 * k ≤ bound) :
    (domain.map fun words => lowest + 8 * words - base).getD 0 < bound := by
  rw [present]
  exact padded_size_lt_arithmetic base _ bound basePositive boundPositive totalBound

private theorem rounded_size_exact (base size : Nat)
    (baseAligned : base % 8 = 0) (endAligned : (base + size) % 8 = 0) :
    8 * ((size + 7) / 8) = size := by omega

/-- The initialized RAM array has exactly the tracer's padded backing size
for a checked layout.
For example, an aligned 248-byte backing allocates exactly 248 bytes, without
wrapping the size through its u64 representation. -/
theorem initialRam_size_eq_ram_size (layout : MemoryLayout)
    (image : List (BitVec 64 × BitVec 8)) (config : MemoryConfig)
    (built : MemoryLayout.new config = some layout) :
    (initialRam layout image).size = layout.ram_size := by
  obtain ⟨words, checked⟩ := Option.isSome_iff_exists.mp (new_max_ram_k config layout built)
  have bound := (max_ram_k_spec layout words checked).2.2.2
  have sizeBound : layout.ram_size < 2 ^ 64 :=
    padded_size_lt_option JoltISA.RAM_START_ADDRESS _ _ _ words checked
      (by decide) (by decide) bound
  have aligned := ram_backing_end_aligned
    { memory_layout := layout, panic := false } (new_lowest_address_aligned config layout built)
  rw [initialRam_size, MemoryLayout.get_total_memory_size, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt sizeBound]
  exact rounded_size_exact JoltISA.RAM_START_ADDRESS layout.ram_size (by decide) aligned

/-- Device readability depends only on layout, not memory contents or panic.
For example, an output remains readable after another output byte is stored. -/
theorem device_readable_of_layout (before after : JoltDevice) (address : Nat)
    (same : after.memory_layout = before.memory_layout) :
    after.readable address = before.readable address := by
  simp only [JoltDevice.readable, JoltDevice.is_input, JoltDevice.is_output,
    JoltDevice.is_trusted_advice, JoltDevice.is_untrusted_advice,
    JoltDevice.is_io_gap, same]

/-- A successful below-RAM store passed the device's readability guard.
For example, an I/O-gap store implies its old byte has a zero-default read. -/
theorem store_raw_device_readable (before after : SailJoltState) (address : Nat)
    (value : BitVec 8) (below : address < JoltISA.RAM_START_ADDRESS)
    (stored : JoltISA.Mmu.store_raw? before address value = some after) :
    before.jolt_device.readable address = true := by
  have checked : JoltISA.Mmu.effective_address_ok before.jolt_device address true = true := by
    by_contra failed
    have rejected := Bool.eq_false_iff.mpr failed
    simp [JoltISA.Mmu.store_raw?, rejected] at stored
  simpa only [JoltISA.Mmu.effective_address_ok, ite_eq_left below] using checked

theorem store_bytes_device_readable (address : Nat) (value : BitVec 64) :
    ∀ (offsets : List Nat) (before after : SailJoltState),
      (∀ k ∈ offsets, address + k < JoltISA.RAM_START_ADDRESS) →
      offsets.foldl (fun current k => current.bind fun state =>
        JoltISA.Mmu.store_raw? state (address + k) (value.extractLsb' (8 * k) 8)) (some before) =
          some after →
      ∀ k ∈ offsets, before.jolt_device.readable (address + k) = true := by
  intro offsets
  induction offsets with
  | nil => intro before after below stored k member; cases member
  | cons head tail ih =>
    intro before after below stored k member
    simp only [List.foldl_cons, Option.bind_some] at stored
    cases headStore : JoltISA.Mmu.store_raw? before (address + head)
        (value.extractLsb' (8 * head) 8) with
    | none =>
      rw [headStore] at stored
      have fails : ∀ offsets : List Nat,
          offsets.foldl (fun current k => current.bind fun state =>
            JoltISA.Mmu.store_raw? state (address + k) (value.extractLsb' (8 * k) 8)) none = none := by
        intro offsets
        induction offsets with
        | nil => rfl
        | cons k rest ih => exact ih
      rw [fails] at stored
      cases stored
    | some middle =>
      rw [headStore] at stored
      have same := (JoltIOSetupFrame.store_raw_same _ _ _ _ headStore).1
      rcases List.mem_cons.mp member with atHead | inTail
      · subst k
        exact store_raw_device_readable _ _ _ _ (below _ List.mem_cons_self) headStore
      · rw [← device_readable_of_layout before.jolt_device middle.jolt_device _ same]
        exact ih middle after (fun k member => below k (List.mem_cons_of_mem _ member))
          stored k inTail

theorem read_doubleword_present (byte : Nat → Option (BitVec 8)) (address : Nat)
    (present : ∀ k < 8, (byte (address + k)).isSome = true) :
    (JoltISA.read_doubleword? byte address).isSome = true := by
  obtain ⟨_, h0⟩ := Option.isSome_iff_exists.mp (present 0 (by decide))
  obtain ⟨_, h1⟩ := Option.isSome_iff_exists.mp (present 1 (by decide))
  obtain ⟨_, h2⟩ := Option.isSome_iff_exists.mp (present 2 (by decide))
  obtain ⟨_, h3⟩ := Option.isSome_iff_exists.mp (present 3 (by decide))
  obtain ⟨_, h4⟩ := Option.isSome_iff_exists.mp (present 4 (by decide))
  obtain ⟨_, h5⟩ := Option.isSome_iff_exists.mp (present 5 (by decide))
  obtain ⟨_, h6⟩ := Option.isSome_iff_exists.mp (present 6 (by decide))
  obtain ⟨_, h7⟩ := Option.isSome_iff_exists.mp (present 7 (by decide))
  simp only [Nat.add_zero] at h0
  simp only [JoltISA.read_doubleword?, h0, h1, h2, h3, h4, h5, h6, h7, Option.isSome_some]

/-- A successful aligned store has the old word recorded by the tracer.
The RAM and I/O reads use shared memory and zero defaults; for example,
an untouched mapped output word has old value zero. -/
theorem store_doubleword_old_present (state after : SailJoltState) (address value : BitVec 64)
    (result : Result Bool ExecutionResult)
    (alignedBase : state.jolt_device.memory_layout.get_lowest_address.toNat % 8 = 0)
    (stored : JoltISA.Mmu.store_doubleword address value state = .ok result after) :
    (JoltISA.trace_doubleword? state address).isSome = true := by
  simp only [JoltISA.Mmu.store_doubleword] at stored
  split at stored
  · cases stored
  · rename_i aligned
    split at stored
    · rename_i inRam
      split at stored
      · rename_i valid
        have below : address.toNat < JoltISA.Mmu.ram_backing_end state.jolt_device := by
          simp only [Bool.and_eq_true, JoltISA.Mmu.effective_address_ok,
            ite_eq_right (by omega : ¬ address.toNat < JoltISA.RAM_START_ADDRESS),
            decide_eq_true_eq] at valid
          exact valid.1
        have endAligned := ram_backing_end_aligned state.jolt_device alignedBase
        simp [JoltISA.trace_doubleword?,
          show ¬ address.toNat < JoltISA.RAM_START_ADDRESS by omega,
          show address.toNat + 8 ≤ JoltISA.Mmu.ram_backing_end state.jolt_device by omega]
      · cases stored
    · rename_i notRam
      split at stored
      · rename_i finalState writes
        rw [JoltISA.trace_doubleword?, ite_eq_left (by omega)]
        apply read_doubleword_present
        intro k hk
        have readable := store_bytes_device_readable address.toNat value (List.range 8)
          state finalState (fun k member => by
            have hk := List.mem_range.mp member
            have base : JoltISA.RAM_START_ADDRESS = 2147483648 := rfl
            omega) writes k (List.mem_range.mpr hk)
        simp [JoltDevice.load?, readable]
      · cases stored

theorem HonestTrace.preState_lowest_address_aligned {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (position : Nat) (row : TraceRow trace.bytecode)
    (atPosition : trace.rows[position]? = some row) :
    row.preState.jolt_device.memory_layout.get_lowest_address.toNat % 8 = 0 := by
  induction position generalizing row with
  | zero =>
    obtain ⟨_, _, startState⟩ := trace.starts row atPosition
    rw [startState]
    change trace.initialState.jolt_device.memory_layout.get_lowest_address.toNat % 8 = 0
    exact initial_state_lowest_address_aligned _ _ _ trace.initialized
  | succ position ih =>
    obtain ⟨inRange, _⟩ := Array.getElem?_eq_some_iff.mp atPosition
    have previousAt : trace.rows[position]? = some trace.rows[position] :=
      Array.getElem?_eq_getElem (by omega)
    have previous := ih trace.rows[position] previousAt
    have same := (JoltIOSetupFrame.execInstr_rule _ _ _ _
      (trace.executes trace.rows[position] (Array.getElem_mem (by omega)))).1
    have link := trace.linked position trace.rows[position] row previousAt atPosition
    split at link
    · rw [link.2, same]; exact previous
    · obtain ⟨_, _, _, _, startState⟩ := link
      rw [startState]
      change trace.rows[position].postState.jolt_device.memory_layout.get_lowest_address.toNat % 8 = 0
      rw [same]
      exact previous

/-- A successful register-read/store sequence has an old word at its accessed
address, provided the mapped RAM domain is word-aligned.
`addressOf` maps the effective address to the accessed address; the two masks
allow an alignment check before or after reading the value source.
For example, SD uses `id`, mask 0 before the read and mask 7 after it.
Jolt's tracer: `tracer/src/instruction/sd.rs` (`SD::exec`) and
`tracer/src/instruction/floor_access.rs` (`store`) at `ff6fc6568`. -/
private theorem store_sequence_old_present (base value : JoltISA.Src) (imm : BitVec 64)
    (addressOf : BitVec 64 → BitVec 64) (beforeMask afterMask : BitVec 64)
    (fault : ExceptionType) (state after : SailJoltState)
    (aligned : state.jolt_device.memory_layout.get_lowest_address.toNat % 8 = 0)
    (runs : (do
      let baseValue ← JoltISA.readSrc base
      let ea := baseValue + imm
      if ea &&& beforeMask = 0 then
        let stored ← JoltISA.readSrc value
        if ea &&& afterMask = 0 then
          match ← JoltISA.Mmu.store_doubleword (addressOf ea) stored with
          | .Ok _ => pure RETIRE_SUCCESS
          | .Err e => pure e
        else pure (ExecutionResult.Memory_Exception (virtaddr.Virtaddr ea, fault))
      else pure (ExecutionResult.Memory_Exception (virtaddr.Virtaddr ea, fault))) state =
        .ok RETIRE_SUCCESS after) :
    (JoltISA.trace_doubleword? state
      (addressOf (JoltISA.sourceValue base state + imm))).isSome = true := by
  cases baseRead : JoltISA.readSrc base state with
  | error failure middle => simp only [bind, EStateM.bind, baseRead] at runs; cases runs
  | ok baseValue middle =>
    obtain ⟨middleSame, baseIs⟩ := readSrc_value base _ _ _ baseRead
    simp only [bind, EStateM.bind, baseRead] at runs
    rw [middleSame] at runs
    split at runs
    · cases valueRead : JoltISA.readSrc value state with
      | error failure middle => simp only [EStateM.bind, valueRead] at runs; cases runs
      | ok storedValue middle =>
        obtain ⟨storedSame, _⟩ := readSrc_value value _ _ _ valueRead
        simp only [EStateM.bind, valueRead] at runs
        split at runs
        · rw [storedSame, baseIs] at runs
          cases stored : JoltISA.Mmu.store_doubleword
              (addressOf (JoltISA.sourceValue base state + imm)) storedValue state with
          | error failure final => simp only [EStateM.bind, stored] at runs; cases runs
          | ok result final =>
            exact store_doubleword_old_present _ _ _ _ _ aligned stored
        · cases runs
    · cases runs

/-- Runtime advice leaves SD and floor stores unchanged; for example,
VirtualStoreH still stores its source register, not an advice value.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`store`) and
`tracer/src/instruction/sd.rs` (`SD::exec`) at `ff6fc6568`. -/
private theorem store_runtime_advice {instruction : JoltISA.Instr}
    (advice : instruction.RuntimeAdvice) (base value : JoltISA.Src) (imm : BitVec 64)
    (fault : ExceptionType)
    (selected : instruction = .SD base value imm ∨
      instruction = .VirtualStoreB base value imm fault ∨
      instruction = .VirtualStoreH base value imm fault ∨
      instruction = .VirtualStoreW base value imm fault) :
    instruction.withRuntimeAdvice advice = instruction := by
  rcases selected with rfl | rfl | rfl | rfl <;> rfl

/-- The old doubleword exists at the accessed address of an SD or floor-store
row in an initialized, linked honest trace.
`isStore` identifies both the store and its accessed address; floor stores
clear all three low bits, so a byte floor store at effective address 11 reads
its old word at 8.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`store`) at `ff6fc6568`. -/
theorem HonestTrace.store_word_present {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (inBounds : i < trace.rows.size) (address : BitVec 64)
    (isStore : match trace.bytecode[trace.rows[i].rowIndex].instruction with
      | .SD base _ imm => address = JoltISA.sourceValue base trace.rows[i].preState + imm
      | .VirtualStoreB base _ imm _ | .VirtualStoreH base _ imm _
      | .VirtualStoreW base _ imm _ =>
          address = (JoltISA.sourceValue base trace.rows[i].preState + imm) &&& ~~~7
      | _ => False) :
    (JoltISA.trace_doubleword? trace.rows[i].preState address).isSome = true := by
  have atPosition := Array.getElem?_eq_getElem inBounds
  have aligned := trace.preState_lowest_address_aligned i trace.rows[i] atPosition
  have runs := trace.executes trace.rows[i] (Array.getElem_mem inBounds)
  have andZero (ea : BitVec 64) : ea &&& 0 = 0 := BitVec.and_zero
  split at isStore
  · rename_i base value imm selected
    subst address
    rw [store_runtime_advice _ base value imm (ExceptionType.E_SAMO_Addr_Align ())
      (Or.inl selected), selected] at runs
    simp only [JoltISA.execInstr] at runs
    refine store_sequence_old_present base value imm id 0 7
      (ExceptionType.E_SAMO_Addr_Align ()) trace.rows[i].preState trace.rows[i].postState aligned ?_
    simpa only [andZero, ↓reduceIte, id_eq] using! runs
  · rename_i base value imm fault selected
    subst address
    rw [store_runtime_advice _ base value imm fault
      (Or.inr (Or.inl selected)), selected] at runs
    simp only [JoltISA.execInstr] at runs
    refine store_sequence_old_present base value imm (fun ea => ea &&& ~~~7) 0 0
      fault trace.rows[i].preState trace.rows[i].postState aligned ?_
    simpa only [andZero, ↓reduceIte] using! runs
  · rename_i base value imm fault selected
    subst address
    rw [store_runtime_advice _ base value imm fault
      (Or.inr (Or.inr (Or.inl selected))), selected] at runs
    simp only [JoltISA.execInstr] at runs
    refine store_sequence_old_present base value imm (fun ea => ea &&& ~~~7) 1 0
      fault trace.rows[i].preState trace.rows[i].postState aligned ?_
    simpa only [andZero, ↓reduceIte] using! runs
  · rename_i base value imm fault selected
    subst address
    rw [store_runtime_advice _ base value imm fault
      (Or.inr (Or.inr (Or.inr selected))), selected] at runs
    simp only [JoltISA.execInstr] at runs
    refine store_sequence_old_present base value imm (fun ea => ea &&& ~~~7) 3 0
      fault trace.rows[i].preState trace.rows[i].postState aligned ?_
    simpa only [andZero, ↓reduceIte] using! runs
  · exact False.elim isStore
