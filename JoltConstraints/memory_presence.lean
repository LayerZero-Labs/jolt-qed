import JoltConstraints.execution_facts
import JoltBytecode.InstructionEquivalence.ProofSupport.DeviceFrame

open Sail PreSail LeanRV64D.Functions
set_option autoImplicit false

/-
Stores need their old value when constructing the honest witness. A successful
store alone does not imply that the old RAM bytes exist. Initialization supplies
those bytes, and induction along HonestTrace carries their presence to each row.
-/

namespace RamMemoryKept

-- An instruction may overwrite bytes, but it never removes existing RAM bytes.
def Extends (before after : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ address, (before.get? address).isSome → (after.get? address).isSome

theorem insert_extends (mem : Std.ExtHashMap Nat (BitVec 8)) (address : Nat)
    (value : BitVec 8) : Extends mem (mem.insert address value) := by
  intro other present
  change mem[other]?.isSome = true at present
  change (mem.insert address value)[other]?.isSome = true
  rw [Std.ExtHashMap.isSome_getElem?_eq_contains] at present ⊢
  rw [Std.ExtHashMap.contains_insert, present, Bool.or_true]

theorem write_ram_extends (mem : Std.ExtHashMap Nat (BitVec 8)) (address : Nat)
    (value : BitVec 64) : Extends mem (JoltISA.Mmu.write_ram_doubleword mem address value) := by
  have fold : ∀ (offsets : List Nat) (mem : Std.ExtHashMap Nat (BitVec 8)),
      Extends mem (offsets.foldl
        (fun mem k => mem.insert (address + k) (value.extractLsb' (8 * k) 8)) mem) := by
    intro offsets
    induction offsets with
    | nil => intro mem other present; exact present
    | cons k rest ih =>
      intro mem other present
      exact ih _ _ (insert_extends mem _ _ other present)
  exact fold _ mem

theorem store_raw_extends {state after : SailJoltState} {address : Nat} {value : BitVec 8}
    (runs : JoltISA.Mmu.store_raw? state address value = some after) :
    Extends state.sail.mem after.sail.mem := by
  simp only [JoltISA.Mmu.store_raw?] at runs
  repeat' split at runs
  all_goals first
    | (cases runs; exact insert_extends _ _ _)
    | cases runs
    | (cases stored : state.jolt_device.store? address value <;> simp [stored] at runs
       cases runs
       exact fun _ present => present)

theorem store_bytes_extends (address : Nat) (value : BitVec 64) :
    ∀ (offsets : List Nat) (current : Option SailJoltState) (before after : SailJoltState),
      (∀ state, current = some state → Extends before.sail.mem state.sail.mem) →
      offsets.foldl (fun current k => current.bind fun state =>
        JoltISA.Mmu.store_raw? state (address + k) (value.extractLsb' (8 * k) 8)) current =
          some after → Extends before.sail.mem after.sail.mem := by
  intro offsets
  induction offsets with
  | nil => intro current before after kept runs; exact kept after runs
  | cons k rest ih =>
    intro current before after kept runs
    apply ih _ before after _ runs
    intro state stored
    cases current with
    | none => simp at stored
    | some middle =>
      exact fun address present => store_raw_extends stored address (kept middle rfl address present)

def Preserves {α : Type} (step : JoltMonad α) : Prop :=
  StatePreservation.Preserves (fun state after => Extends state.sail.mem after.sail.mem) step

theorem unchanged_rule {α : Type} {step : JoltMonad α}
    (same : ∀ state after value, step state = .ok value after →
      after.sail.mem = state.sail.mem) : Preserves step := by
  intro state after value runs address present
  rw [same state after value runs]
  exact present

theorem pure_rule {α : Type} (value : α) : Preserves (pure value) :=
  StatePreservation.pure_rule (fun _ _ present => present) value

theorem bind_rule {α β : Type} {first : JoltMonad α} {next : α → JoltMonad β}
    (keepsFirst : Preserves first) (keepsNext : ∀ value, Preserves (next value)) :
    Preserves (first >>= next) :=
  StatePreservation.bind_rule (fun _ _ _ first next address present => next address (first address present))
    keepsFirst keepsNext

theorem get_rule : Preserves (get : JoltMonad SailJoltState) :=
  StatePreservation.get_rule (fun _ _ present => present)

theorem throw_rule {α : Type} (failure : Error exception) :
    Preserves (throw failure : JoltMonad α) :=
  StatePreservation.throw_rule _ failure

theorem lift_rule {α : Type} {step : SailM α}
    (same : ∀ sail after value, step sail = .ok value after → after.mem = sail.mem) :
    Preserves (liftSail step) :=
  StatePreservation.liftSail_rule
    (fun _ _ equal address present => by simpa only [equal] using present) same

theorem read_rule (source : JoltISA.Src) : Preserves (JoltISA.readSrc source) :=
  unchanged_rule (fun _ _ _ runs => congrArg (·.mem) (SailUnchanged.read_rule source _ _ _ runs))

theorem write_rule (destination : JoltISA.Dst) (value : BitVec 64) :
    Preserves (JoltISA.writeDst destination value) := by
  cases destination with
  | vreg register =>
    apply unchanged_rule
    intro state after result runs
    simp only [JoltISA.writeDst, writeVReg] at runs
    split at runs <;> cases runs
    rfl
  | xreg register =>
    apply lift_rule
    intro sail after result runs
    rw [wX_bits_eq_stateAfterWrite register value sail after runs]
    rfl

theorem readReg_rule (register : Register) : Preserves (liftSail (Sail.readReg register)) :=
  lift_rule (fun sail after value runs => congrArg (·.mem) (readReg_pure register sail value after runs))

theorem writeReg_rule (register : Register) (value : RegisterType register) :
    Preserves (liftSail (Sail.writeReg register value)) :=
  lift_rule (fun _ _ _ runs => by cases runs; rfl)

theorem arch_pc_rule : Preserves (liftSail (get_arch_pc ())) :=
  lift_rule (fun sail after value runs => congrArg (·.mem) (readReg_pure Register.PC sail value after runs))

theorem jump_rule (target : BitVec 64) : Preserves (liftSail (jump_to target)) :=
  lift_rule (fun sail after result runs => by
    rcases jump_to_shape target sail after result runs with same | written
    · rw [same]
    · rw [written])

theorem load_doubleword_rule (address : BitVec 64) :
    Preserves (JoltISA.Mmu.load_doubleword address) :=
  unchanged_rule (fun _ _ _ runs => by rw [JoltISA.Mmu.load_doubleword_state runs])

theorem store_doubleword_rule (address value : BitVec 64) :
    Preserves (JoltISA.Mmu.store_doubleword address value) := by
  intro state after result runs
  simp only [JoltISA.Mmu.store_doubleword] at runs
  repeat' split at runs
  all_goals first
    | (cases runs; exact write_ram_extends _ _ _)
    | (rename_i stored
       cases runs
       exact store_bytes_extends _ value _ (some state) state _
         (fun _ eq => by cases eq; exact fun _ present => present) stored)
    | cases runs

theorem execHostIO_rule : Preserves JoltISA.execHostIO :=
  unchanged_rule (fun state after result runs =>
    congrArg (·.mem) (execHostIO_keeps_sail state after result runs))

theorem execInstr_rule (instruction : JoltISA.Instr) :
    Preserves (JoltISA.execInstr instruction) := by
  cases instruction
  case VirtualAdviceLoad destination byteCount =>
    intro before after value runs
    simp only [JoltISA.execInstr] at runs
    cases tapeRead : JoltISA.readAdviceTape before.adviceTape byteCount with
    | none => simp only [tapeRead] at runs; cases runs
    | some pair =>
      obtain ⟨adviceValue, tape⟩ := pair
      simp only [tapeRead] at runs
      exact bind_rule (write_rule destination adviceValue) (fun _ => pure_rule _)
        { before with adviceTape := tape } after value runs
  all_goals simp only [JoltISA.execInstr]
  all_goals preservation_auto [read_rule _, write_rule _ _, pure_rule _, throw_rule _,
    get_rule, readReg_rule _, writeReg_rule _ _, arch_pc_rule, jump_rule _,
    load_doubleword_rule _, store_doubleword_rule _ _, execHostIO_rule] using bind_rule

end RamMemoryKept

-- The entire allocated RAM backing is populated at initialization.
def RamBytesPresent (state : SailJoltState) : Prop :=
  ∀ address, JoltISA.RAM_START_ADDRESS ≤ address →
    address < JoltISA.Mmu.ram_backing_end state.jolt_device →
    (state.sail.mem.get? address).isSome

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

theorem init_state_byte_present (entry : BitVec 64) (ram : Array (BitVec 8))
    (device : JoltDevice) (advice : JoltAdviceTape) (hostIO : JoltHostIOConfig)
    (offset : Nat) (inRange : offset < ram.size) :
    ((init_state entry ram device advice hostIO).sail.mem.get?
      (JoltISA.RAM_START_ADDRESS + offset)).isSome := by
  have fold : ∀ (bytes : List (BitVec 8 × Nat)) (mem : Std.ExtHashMap Nat (BitVec 8)),
      (∃ byte, (byte, offset) ∈ bytes) ∨ (mem.get? (JoltISA.RAM_START_ADDRESS + offset)).isSome →
      ((bytes.foldl (fun mem (byte, i) => mem.insert (JoltISA.RAM_START_ADDRESS + i) byte) mem).get?
        (JoltISA.RAM_START_ADDRESS + offset)).isSome := by
    intro bytes
    induction bytes with
    | nil => intro mem present; simpa using present
    | cons head tail ih =>
      intro mem present
      apply ih
      rcases present with ⟨byte, member⟩ | present
      · rcases List.mem_cons.mp member with eq | member
        · right
          cases eq
          change ((mem.insert (JoltISA.RAM_START_ADDRESS + offset) byte)[JoltISA.RAM_START_ADDRESS + offset]?).isSome = true
          simp
        · exact Or.inl ⟨byte, member⟩
      · exact Or.inr (RamMemoryKept.insert_extends _ _ _ _ present)
  apply fold
  left
  refine ⟨ram[offset], ?_⟩
  have member := List.getElem_mem (l := ram.toList.zipIdx) (n := offset) (by simpa using inRange)
  simpa using member

theorem initial_state_ram_present {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (state : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some state) : RamBytesPresent state := by
  unfold JoltInstance.initial_state at built
  cases layoutResult : joltInstance.memory_layout with
  | none => simp only [layoutResult, bind, Option.bind] at built; cases built
  | some layout =>
    simp only [layoutResult, bind, Option.bind] at built
    repeat' split at built
    all_goals first | cases built
    all_goals
      intro address above below
      have offsetFits : address - JoltISA.RAM_START_ADDRESS <
          (initialRam layout joltInstance.program.memory_init).size := by
        rw [initialRam_size]
        change address < JoltISA.RAM_START_ADDRESS +
          8 * ((layout.get_total_memory_size.toNat + 7) / 8) at below
        omega
      have present := init_state_byte_present joltInstance.program.entry_address
        (initialRam layout joltInstance.program.memory_init)
        { inputs := joltInstance.inputs, trusted_advice := joltInstance.trusted_advice,
          untrusted_advice := privateInputs.untrusted_advice, outputs := #[], panic := false,
          memory_layout := layout }
        { bytes := privateInputs.advice_tape, readPosition := 0 } {}
        (address - JoltISA.RAM_START_ADDRESS) offsetFits
      simpa only [Nat.add_sub_of_le above] using present

theorem execInstr_keeps_ram (instruction : JoltISA.Instr) (state after : SailJoltState)
    (result : ExecutionResult) (runs : JoltISA.execInstr instruction state = .ok result after)
    (present : RamBytesPresent state) : RamBytesPresent after := by
  intro address above below
  have sameLayout := (JoltIOSetupFrame.execInstr_rule instruction state after result runs).1
  have belowBefore : address < JoltISA.Mmu.ram_backing_end state.jolt_device := by
    simpa only [JoltISA.Mmu.ram_backing_end, sameLayout] using below
  exact RamMemoryKept.execInstr_rule instruction state after result runs address
    (present address above belowBefore)

theorem HonestTrace.ram_present {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (position : Nat) (row : TraceRow trace.bytecode)
    (atPosition : trace.rows[position]? = some row) : RamBytesPresent row.preState := by
  induction position generalizing row with
  | zero =>
    obtain ⟨_, _, startState⟩ := trace.starts row atPosition
    rw [startState]
    exact initial_state_ram_present joltInstance privateInputs trace.initialState trace.initialized
  | succ position ih =>
    obtain ⟨inRange, _⟩ := Array.getElem?_eq_some_iff.mp atPosition
    have previousAt : trace.rows[position]? = some trace.rows[position] :=
      Array.getElem?_eq_getElem (by omega)
    have previousEnd : RamBytesPresent trace.rows[position].postState :=
      execInstr_keeps_ram _ _ _ _ (trace.executes _ (Array.getElem_mem (by omega)))
        (ih trace.rows[position] previousAt)
    have link := trace.linked position trace.rows[position] row previousAt atPosition
    split at link
    · rw [link.2]; exact previousEnd
    · obtain ⟨_, _, _, _, startState⟩ := link
      rw [startState]
      exact previousEnd

theorem heap_end_le_ram_backing_end (device : JoltDevice) :
    device.memory_layout.heap_end.toNat ≤ JoltISA.Mmu.ram_backing_end device := by
  unfold JoltISA.Mmu.ram_backing_end MemoryLayout.get_total_memory_size
  rw [BitVec.toNat_sub]
  have heapBound := device.memory_layout.heap_end.isLt
  have base : (BitVec.ofNat 64 JoltISA.RAM_START_ADDRESS).toNat = 2147483648 := rfl
  rw [base]
  unfold JoltISA.RAM_START_ADDRESS
  omega

theorem new_panic_lt_termination (config : MemoryConfig) (layout : MemoryLayout)
    (built : MemoryLayout.new config = some layout) :
    layout.panic.toNat < layout.termination.toNat := by
  unfold MemoryLayout.new at built
  repeat' (rw [bind_some_iff] at built; obtain ⟨_, _, built⟩ := built)
  cases built
  have checked : ∀ a b c, MemoryLayout.checkedAdd a b = some c ↔
      c = a + b ∧ a + b < 2 ^ 64 := by
    intro a b c
    constructor
    · exact checkedAdd_some
    · rintro ⟨rfl, fits⟩
      simp only [MemoryLayout.checkedAdd, if_pos fits]
  simp only [checked] at *
  simp only [BitVec.toNat_ofNat]
  omega

theorem device_load_presence_of_layout (before after : JoltDevice) (address : Nat)
    (same : after.memory_layout = before.memory_layout) :
    (after.load? address).isSome = (before.load? address).isSome := by
  unfold JoltDevice.load? JoltDevice.is_panic JoltDevice.is_termination
    JoltDevice.is_input JoltDevice.is_output JoltDevice.is_trusted_advice
    JoltDevice.is_untrusted_advice
  simp only [same]
  split_ifs <;> rfl

theorem device_store_readable (before after : JoltDevice) (address : Nat) (value : BitVec 8)
    (ordered : before.memory_layout.panic.toNat < before.memory_layout.termination.toNat)
    (stored : before.store? address value = some after) :
    (before.load? address).isSome := by
  have writable : before.is_panic address = true ∨ before.is_termination address = true ∨
      before.is_output address = true := by
    unfold JoltDevice.store? at stored
    split at stored
    · rename_i atPanic
      left
      simp [JoltDevice.is_panic, atPanic, ordered]
    · split at stored
      · rename_i either
        simp only [Bool.or_eq_true] at either
        rcases either with panic | termination
        · exact Or.inl panic
        · exact Or.inr (Or.inl termination)
      · split at stored
        · rename_i output
          exact Or.inr (Or.inr output)
        · cases stored
  unfold JoltDevice.load?
  rcases writable with panic | termination | output
  · simp [panic]
  · simp only [termination, ↓reduceIte]
    split_ifs <;> rfl
  · simp only [output, ↓reduceIte]
    split_ifs <;> rfl

theorem store_raw_device_readable (before after : SailJoltState) (address : Nat)
    (value : BitVec 8) (below : address < JoltISA.RAM_START_ADDRESS)
    (ordered : before.jolt_device.memory_layout.panic.toNat <
      before.jolt_device.memory_layout.termination.toNat)
    (stored : JoltISA.Mmu.store_raw? before address value = some after) :
    (before.jolt_device.load? address).isSome := by
  unfold JoltISA.Mmu.store_raw? at stored
  rw [if_neg (by omega)] at stored
  split at stored
  · cases stored
  · split at stored
    · cases stored
    · cases deviceStore : before.jolt_device.store? address value with
      | none => simp [deviceStore] at stored
      | some device => exact device_store_readable _ _ _ _ ordered deviceStore

theorem store_bytes_device_readable (address : Nat) (value : BitVec 64) :
    ∀ (offsets : List Nat) (before after : SailJoltState),
      (∀ k ∈ offsets, address + k < JoltISA.RAM_START_ADDRESS) →
      before.jolt_device.memory_layout.panic.toNat < before.jolt_device.memory_layout.termination.toNat →
      offsets.foldl (fun current k => current.bind fun state =>
        JoltISA.Mmu.store_raw? state (address + k) (value.extractLsb' (8 * k) 8)) (some before) =
          some after →
      ∀ k ∈ offsets, (before.jolt_device.load? (address + k)).isSome := by
  intro offsets
  induction offsets with
  | nil => intro before after below ordered stored k member; cases member
  | cons head tail ih =>
    intro before after below ordered stored k member
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
        exact store_raw_device_readable _ _ _ _ (below _ List.mem_cons_self) ordered headStore
      · rw [← device_load_presence_of_layout before.jolt_device middle.jolt_device _ same]
        exact ih middle after (fun k member => below k (List.mem_cons_of_mem _ member))
          (by simpa only [same] using ordered) stored k inTail

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

theorem store_doubleword_old_present (state after : SailJoltState) (address value : BitVec 64)
    (result : Result Bool ExecutionResult) (present : RamBytesPresent state)
    (ordered : state.jolt_device.memory_layout.panic.toNat <
      state.jolt_device.memory_layout.termination.toNat)
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
        have belowHeap : address.toNat < state.jolt_device.memory_layout.heap_end.toNat := by
          simp only [JoltISA.Mmu.effective_address_ok,
            if_neg (by omega : ¬ address.toNat < JoltISA.RAM_START_ADDRESS),
            ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at valid
          exact valid.2
        rw [JoltISA.trace_doubleword?, if_neg (by omega)]
        apply read_doubleword_present
        intro k hk
        apply present _ (by omega)
        have bound := heap_end_le_ram_backing_end state.jolt_device
        have multiple : JoltISA.Mmu.ram_backing_end state.jolt_device % 8 = 0 := by
          simp [JoltISA.Mmu.ram_backing_end, JoltISA.RAM_START_ADDRESS]
        omega
      · cases stored
    · rename_i notRam
      split at stored
      · rename_i finalState writes
        rw [JoltISA.trace_doubleword?, if_pos (by omega)]
        apply read_doubleword_present
        intro k hk
        apply store_bytes_device_readable address.toNat value (List.range 8) state finalState
          ?_ ordered writes k (List.mem_range.mpr hk)
        intro k member
        have hk := List.mem_range.mp member
        have base : JoltISA.RAM_START_ADDRESS = 2147483648 := rfl
        omega
      · cases stored

theorem HonestTrace.panic_lt_termination {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (position : Nat) (row : TraceRow trace.bytecode)
    (atPosition : trace.rows[position]? = some row) :
    row.preState.jolt_device.memory_layout.panic.toNat <
      row.preState.jolt_device.memory_layout.termination.toNat := by
  induction position generalizing row with
  | zero =>
    obtain ⟨_, _, startState⟩ := trace.starts row atPosition
    rw [startState]
    exact new_panic_lt_termination _ _ (initial_state_device _ _ _ trace.initialized).1
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
      change trace.rows[position].postState.jolt_device.memory_layout.panic.toNat <
        trace.rows[position].postState.jolt_device.memory_layout.termination.toNat
      rw [same]
      exact previous

-- The old word exists for a store at row i of an initialized, linked honest trace.
-- No statement is made for an isolated row with an arbitrary pre-state.
theorem HonestTrace.store_word_present {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (inBounds : i < trace.rows.size) (base value : JoltISA.Src) (imm : BitVec 64)
    (isStore : trace.bytecode[trace.rows[i].rowIndex].instruction = .SD base value imm) :
    (JoltISA.trace_doubleword? trace.rows[i].preState
      (JoltISA.sourceValue base trace.rows[i].preState + imm)).isSome = true := by
  have atPosition := Array.getElem?_eq_getElem inBounds
  have present := trace.ram_present i trace.rows[i] atPosition
  have ordered := trace.panic_lt_termination i trace.rows[i] atPosition
  have runs := trace.executes trace.rows[i] (Array.getElem_mem inBounds)
  rw [withRuntimeAdvice_store _ base value imm isStore] at runs
  simp only [JoltISA.execInstr] at runs
  cases baseRead : JoltISA.readSrc base trace.rows[i].preState with
  | error failure middle => simp only [bind, EStateM.bind, baseRead] at runs; cases runs
  | ok baseValue middle =>
    obtain ⟨middleSame, baseIs⟩ := readSrc_value base _ _ _ baseRead
    simp only [bind, EStateM.bind, baseRead] at runs
    rw [middleSame] at runs
    cases valueRead : JoltISA.readSrc value trace.rows[i].preState with
    | error failure middle => rw [valueRead] at runs; cases runs
    | ok storedValue middle =>
      obtain ⟨storedSame, _⟩ := readSrc_value value _ _ _ valueRead
      rw [valueRead] at runs
      dsimp only at runs
      split at runs
      · rw [storedSame, baseIs] at runs
        cases stored : JoltISA.Mmu.store_doubleword
            (JoltISA.sourceValue base trace.rows[i].preState + imm) storedValue trace.rows[i].preState with
        | error failure after => simp only [EStateM.bind, stored] at runs; cases runs
        | ok result after =>
          exact store_doubleword_old_present _ _ _ _ _ present ordered stored
      · cases runs
