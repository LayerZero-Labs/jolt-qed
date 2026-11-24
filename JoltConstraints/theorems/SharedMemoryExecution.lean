import JoltBytecode.InstructionEquivalence.ProofSupport.Memory.MmuJolt
import JoltConstraints.theorems.DeviceFrame
import JoltConstraints.translation.metadata

open LeanRV64D JoltISA
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail

set_option autoImplicit false

namespace JoltConstraints

/-- An accepted byte store inserts its byte into the shared map, retaining all
other state fields.
For example, a byte stored in the I/O gap has the same effect as a RAM byte.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`Mmu::store_raw`).
This primitive execution fact is a candidate to move into JoltBytecode. -/
theorem store_raw_shape (before after : SailJoltState) (address : Nat) (value : BitVec 8)
    (stored : Mmu.store_raw? before address value = some after) :
    after = { before with sail := { before.sail with
      mem := before.sail.mem.insert address value } } := by
  unfold Mmu.store_raw? at stored
  split at stored
  · cases stored
  · split at stored
    · cases stored
    · split at stored
      · exact (Option.some.inj stored).symm
      · split at stored
        · cases stored
        · unfold JoltDevice.store? at stored
          split at stored
          · exact (Option.some.inj stored).symm
          · cases stored

/-- If each successful guarded step has a fixed effect, a successful fold has
the fold of those effects.
For example, checking eight byte stores does not change the resulting insertions. -/
private theorem guarded_fold_shape {α σ : Type} (steps : List α)
    (checked : σ → α → Option σ) (effect : σ → α → σ)
    (shape : ∀ before step after, checked before step = some after →
      after = effect before step) (before after : σ)
    (stored : steps.foldl (fun current step => current.bind fun state =>
      checked state step) (some before) = some after) :
    after = steps.foldl effect before := by
  induction steps generalizing before with
  | nil => exact (Option.some.inj stored).symm
  | cons step rest ih =>
    cases next : checked before step with
    | none =>
      simp only [List.foldl_cons, Option.bind_some, next] at stored
      rw [List.foldl_fixed' (fun _ => rfl) rest] at stored
      cases stored
    | some middle =>
      have middleIs := shape before step middle next
      have tail : rest.foldl (fun current step => current.bind fun state =>
          checked state step) (some middle) = some after := by
        simpa only [List.foldl_cons, Option.bind_some, next] using stored
      rw [List.foldl_cons, ← middleIs]
      exact ih middle tail

/-- Pure byte insertions update only the memory field.
For example, folding offsets 0 through 7 leaves the tape and halt kind unchanged. -/
private theorem byte_inserts_shape (offsets : List Nat) (address : Nat) (value : BitVec 64)
    (before : SailJoltState) :
    offsets.foldl (fun (state : SailJoltState) k => { state with sail := { state.sail with
      mem := state.sail.mem.insert (address + k) (value.extractLsb' (8 * k) 8) } }) before =
    { before with sail := { before.sail with mem := (offsets.foldl
      (fun mem k => mem.insert (address + k) (value.extractLsb' (8 * k) 8)) before.sail.mem) } } := by
  induction offsets generalizing before with
  | nil => rfl
  | cons offset rest ih =>
    simp only [List.foldl_cons]
    rw [ih]

/-- Every successful doubleword store has the same shared-map effect in RAM and
the I/O window, with no device-array update.
For example, a gap-word store writes all eight little-endian bytes and retains
the panic claim and code interval.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`Mmu::store_doubleword_raw`).
This primitive execution fact is a candidate to move into JoltBytecode. -/
theorem store_doubleword_shape (before after : SailJoltState) (address value : BitVec 64)
    (result : Result Bool ExecutionResult)
    (stored : Mmu.store_doubleword address value before = .ok result after) :
    after = { before with sail := { before.sail with
      mem := Mmu.write_ram_doubleword before.sail.mem address.toNat value } } := by
  simp only [Mmu.store_doubleword] at stored
  split at stored
  · cases stored
  · split at stored
    · split at stored
      · exact (EStateM.Result.ok.inj stored).2.symm
      · cases stored
    · split at stored
      · rename_i afterBytes byteStores
        cases stored
        have shape := guarded_fold_shape (List.range 8)
          (fun state k => Mmu.store_raw? state (address.toNat + k)
            (value.extractLsb' (8 * k) 8))
          (fun (state : SailJoltState) k => { state with sail := { state.sail with mem :=
            (state.sail.mem.insert (address.toNat + k) (value.extractLsb' (8 * k) 8)) } })
          (fun state k next stored => store_raw_shape state next _ _ stored)
          before after byteStores
        exact shape.trans (byte_inserts_shape (List.range 8) address.toNat value before)
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
  all_goals cases loaded <;> rfl

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
      simpa only [Mmu.effective_address_ok, if_pos (Nat.lt_of_not_ge inRam)] using checked
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

/-- A byte store with successful address and protection checks inserts its byte.
For example, a value-preserving protected input store is admitted. -/
private theorem store_raw_of_checks (state : SailJoltState) (address : Nat) (value : BitVec 8)
    (checked : Mmu.effective_address_ok state.jolt_device address true = true)
    (peripheral : Mmu.unsupported_store address = false)
    (preservesProtected : Mmu.protected_store_ok state address (value.zeroExtend 64) 1 = true) :
    Mmu.store_raw? state address value =
      some { state with sail := { state.sail with mem := state.sail.mem.insert address value } } := by
  by_cases inRam : RAM_START_ADDRESS ≤ address
  · simp only [Mmu.store_raw?, checked, preservesProtected, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, inRam]
  · have readable : state.jolt_device.readable address = true := by
      simpa only [Mmu.effective_address_ok, if_pos (Nat.lt_of_not_ge inRam)] using checked
    simp only [Mmu.store_raw?, checked, preservesProtected, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, inRam, peripheral, JoltDevice.store?, readable]
    rfl

/-- Address, peripheral and protected-value checks suffice for a doubleword store
in the shared map, including I/O.
For example, replacing an input word by itself succeeds and preserves the device.
This primitive MMU fact is a candidate to move to JoltBytecode. -/
theorem store_doubleword_of_checks (state : SailJoltState) (address value : BitVec 64)
    (aligned : address &&& 7 = 0)
    (checked : ∀ k < 8, Mmu.effective_address_ok state.jolt_device (address.toNat + k) true = true)
    (peripheral : ∀ k < 8, Mmu.unsupported_store (address.toNat + k) = false)
    (preservesProtected : Mmu.protected_store_ok state address.toNat value 8 = true) :
    Mmu.store_doubleword address value state = .ok (.Ok true)
      { state with sail := { state.sail with
        mem := Mmu.write_ram_doubleword state.sail.mem address.toNat value } } := by
  by_cases inRam : RAM_START_ADDRESS ≤ address.toNat
  · exact Mmu.store_doubleword_ram state address value aligned inRam
      (by simpa only [Nat.add_zero] using checked 0 (by decide)) preservesProtected
  · have folded : ∃ after,
        (List.range 8).foldl (fun current k => current.bind fun s =>
          Mmu.store_raw? s (address.toNat + k) (value.extractLsb' (8 * k) 8))
          (some state) = some after ∧ Mmu.ProtectedMemory state after := by
      refine List.foldlRecOn (motive := fun current => ∃ after,
        current = some after ∧ Mmu.ProtectedMemory state after) (List.range 8) _
        ⟨state, rfl, Mmu.ProtectedMemory.refl state⟩ ?_
      intro current prior k member
      obtain ⟨middle, rfl, keeps⟩ := prior
      have within : k < 8 := List.mem_range.mp member
      have currentCheck : Mmu.effective_address_ok middle.jolt_device
          (address.toNat + k) true = true := by
        simpa only [Mmu.effective_address_ok, Mmu.ram_backing_end, keeps.layout,
          JoltDevice.readable, JoltDevice.is_input, JoltDevice.is_trusted_advice,
          JoltDevice.is_untrusted_advice, JoltDevice.is_output, JoltDevice.is_io_gap]
          using! checked k within
      have currentProtected : Mmu.protected_store_ok middle (address.toNat + k)
          ((value.extractLsb' (8 * k) 8).zeroExtend 64) 1 = true := by
        apply (Mmu.protected_store_byte_iff middle _ _).mpr
        intro hp
        have original : Mmu.protected_byte state (address.toNat + k) = true := by
          rwa [Mmu.protected_byte_congr _ keeps.layout keeps.code] at hp
        rw [keeps.bytes _ original]
        have byte := List.all_eq_true.mp preservesProtected k member
        simpa only [original, Bool.not_true, Bool.false_or, beq_iff_eq] using byte
      have stored := store_raw_of_checks middle (address.toNat + k)
        (value.extractLsb' (8 * k) 8) currentCheck (peripheral k within) currentProtected
      exact ⟨_, stored, keeps.trans (Mmu.store_raw_protected stored)⟩
    obtain ⟨after, bytes, _⟩ := folded
    have executed : Mmu.store_doubleword address value state = .ok (.Ok true) after := by
      simp only [Mmu.store_doubleword, Mmu.toNat_mod_eight_of_align aligned,
        ne_self_iff_false, ↓reduceIte, inRam, bytes]
    rw [executed]
    rw [store_doubleword_shape state after address value _ executed]

end JoltConstraints
