import JoltBytecode.InstructionEquivalence.ProofSupport.DeviceFrame
import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltConstraints.translation.program

open LeanRV64D
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D.Functions JoltISA

set_option autoImplicit false

/-- The code-word interval the code guard protects, or the empty interval `(0, 0)`
without a guard.
For example, a guard over words two and three gives `(2, 4)`.
A proof-side view of `SailJoltState.code_guard` (Jolt's `Mmu::code_guard`). -/
def SailJoltState.codeRegion (state : SailJoltState) : Nat × Nat :=
  (state.code_guard.map CodeGuard.region).getD (0, 0)

/-- Testing the guard's interval is testing `codeRegion`.
For example, without a guard both tests are false. -/
@[simp] theorem SailJoltState.code_guard_any_region (state : SailJoltState) (index : Nat) :
    (state.code_guard.any fun guard => guard.region.1 ≤ index && index < guard.region.2) =
      (decide (state.codeRegion.1 ≤ index) && decide (index < state.codeRegion.2)) := by
  unfold SailJoltState.codeRegion
  cases state.code_guard <;> simp

namespace JoltISA

/-- The state change of a halt besides its link and PC writes: `Cpu::halt` sets `halted`.
For example, a panic halt records `some .panic` and leaves the device unchanged;
Jolt copies the kind into the device's panic flag only in `take_jolt_device`.
Jolt at `504dd78a2`: `tracer/src/emulator/cpu.rs` (`Cpu::halt`). -/
abbrev recordHalt (kind : JoltHaltKind) (state : SailJoltState) : SailJoltState :=
  { state with halted := some kind }

/-- Install the input and advice bytes and the code guard on a state that holds the
program image, as `JoltInstance.initial_state` does after `JoltDevice.try_with_io`.
For example, input byte zero is written at `memory_layout.input_start`. -/
def initialState (state : SailJoltState) (sources : List (BitVec 64 × Bool))
    (inputs trusted untrusted : Array (BitVec 8)) : Option SailJoltState :=
  let mem := state.jolt_device.initial_ram_state state.sail.mem inputs trusted untrusted
  protect_code { state with sail := { state.sail with mem := mem } } sources

end JoltISA

namespace JoltConstraints

/-- Inserting a byte retains the presence of every previously present byte.
For example, an output write keeps a present input byte present. -/
theorem insert_preserves_present (mem : Std.ExtHashMap Nat (BitVec 8))
    (address other : Nat) (value : BitVec 8) (present : (mem.get? other).isSome) :
    ((mem.insert address value).get? other).isSome := by
  by_cases same : address = other
  · subst other; simp
  · simpa [Std.ExtHashMap.getElem?_insert, same] using present

/-- A successful shared-memory initialization installs the I/O bytes and the code guard
and changes nothing else.
For example, it leaves every starting register and the execution tape unchanged.
Adapted from Quang Dao's `initialState_shape` in PR #73. -/
theorem initialState_shape (before after : SailJoltState)
    (sources : List (BitVec 64 × Bool)) (inputs trusted untrusted : Array (BitVec 8))
    (built : initialState before sources inputs trusted untrusted = some after) :
    ∃ guard,
      CodeGuard.new sources before.jolt_device.memory_layout.get_lowest_address.toNat =
        some guard ∧
      after = { before with
        sail := { before.sail with
          mem := before.jolt_device.initial_ram_state before.sail.mem inputs trusted untrusted }
        code_guard := some guard } := by
  unfold initialState protect_code at built
  obtain ⟨guard, guardBuilt, built⟩ := Option.bind_eq_some_iff.mp built
  exact ⟨guard, guardBuilt, (Option.some.inj built).symm⟩

/-- The code-word interval of a built guard is `code_region` of its sources.
For example, a guard built from one source at the lowest address protects word zero. -/
theorem CodeGuard.new_region {sources : List (BitVec 64 × Bool)} {lowest : Nat}
    {guard : CodeGuard} (built : CodeGuard.new sources lowest = some guard) :
    JoltISA.code_region sources lowest = some guard.region := by
  unfold CodeGuard.new at built
  obtain ⟨region, regionBuilt, built⟩ := Option.bind_eq_some_iff.mp built
  cases built
  exact regionBuilt

/-- Installing shared memory commutes with replacing the execution tape.
For example, the same inputs and program yield identical memory for either tape. -/
theorem initialState_with_adviceTape (state : SailJoltState)
    (sources : List (BitVec 64 × Bool)) (inputs trusted untrusted : Array (BitVec 8))
    (tape : JoltAdviceTape) :
    initialState { state with adviceTape := tape } sources inputs trusted untrusted =
      (initialState state sources inputs trusted untrusted).map
        (fun after => { after with adviceTape := tape }) := by
  unfold initialState protect_code
  dsimp only
  cases CodeGuard.new sources state.jolt_device.memory_layout.get_lowest_address.toNat <;> rfl

/-- A retiring halt row reads its link and source address, writes the link, then
puts nextPC back on its own address and records the halt.
For example, a panic halt writes the advanced PC to its scratch destination.
Jolt at `504dd78a2`: `tracer/src/emulator/cpu.rs` (`Cpu::halt`).
Adapted from Quang Dao's `execHalt_shape` in PR #73. -/
theorem execHalt_shape (kind : JoltHaltKind) (dst : Dst) (src : Src) (imm : BitVec 12)
    (pre post : SailJoltState)
    (runs : execInstr (haltRow kind dst src imm) pre = .ok RETIRE_SUCCESS post) :
    ∃ link address middle,
      pre.sail.regs.get? Register.nextPC = some link ∧
      pre.sail.regs.get? Register.PC = some address ∧
      writeDst dst link pre = .ok () middle ∧
      post = recordHalt kind { middle with sail := { middle.sail with
        regs := middle.sail.regs.insert Register.nextPC address } } := by
  have unfolded : execInstr (haltRow kind dst src imm) =
      (do let address ← liftSail (LeanRV64D.readReg Register.PC); execHalt kind address dst) := by
    cases kind <;> rfl
  rw [unfolded] at runs
  cases pc : pre.sail.regs.get? Register.PC with
  | none =>
    have failed : liftSail (LeanRV64D.readReg Register.PC) pre =
        .error .Unreachable pre := by
      unfold liftSail
      rw [readReg_eq_of_get?_none Register.PC pre.sail pc]
    simp only [bind, EStateM.bind, failed] at runs
    cases runs
  | some address =>
    have readPC : liftSail (LeanRV64D.readReg Register.PC) pre = .ok address pre := by
      unfold liftSail
      rw [readReg_eq_of_get? Register.PC pre.sail address pc]
    simp only [bind, EStateM.bind, readPC] at runs
    unfold execHalt at runs
    cases next : pre.sail.regs.get? Register.nextPC with
    | none =>
      have failed : liftSail (LeanRV64D.readReg Register.nextPC) pre =
          .error .Unreachable pre := by
        unfold liftSail
        rw [readReg_eq_of_get?_none Register.nextPC pre.sail next]
      simp only [bind, EStateM.bind, failed] at runs
      cases runs
    | some link =>
      have readNext : liftSail (LeanRV64D.readReg Register.nextPC) pre = .ok link pre := by
        unfold liftSail
        rw [readReg_eq_of_get? Register.nextPC pre.sail link next]
      simp only [bind, EStateM.bind, readNext] at runs
      cases written : writeDst dst link pre with
      | error error middle => simp only [written] at runs; cases runs
      | ok value middle =>
        cases value
        simp only [written] at runs
        cases runs
        exact ⟨link, address, middle, rfl, rfl, written, rfl⟩

/-- A raw byte store commutes with a state transformation that preserves its checks
and shared memory, and commutes with replacing memory.
For example, changing tape bytes or an unused register satisfies these conditions.
This primitive frame is a candidate to move into JoltBytecode. -/
theorem store_raw_map (transform : SailJoltState → SailJoltState)
    (device : ∀ state, (transform state).jolt_device = state.jolt_device)
    (memory : ∀ state, (transform state).sail.mem = state.sail.mem)
    (protection : ∀ state address value width,
      Mmu.assert_write_protected_store (transform state) address value width =
        Mmu.assert_write_protected_store state address value width)
    (replace : ∀ state mem,
      { transform state with sail := { (transform state).sail with mem := mem } } =
        transform { state with sail := { state.sail with mem := mem } })
    (state : SailJoltState) (address : Nat) (value : BitVec 8) :
    Mmu.store_raw? (transform state) address value =
      (Mmu.store_raw? state address value).map transform := by
  unfold Mmu.store_raw?
  simp only [device, memory, protection]
  split_ifs <;> simp only [Option.map_none, Option.map_some, Option.map_map]
  · simpa only [device] using congrArg some (replace state (state.sail.mem.insert address value))
  · congr 1
    funext mem
    simpa only [device, Function.comp_apply] using replace state mem

/-- Byte-store folds commute whenever their individual stores commute.
For example, the eight byte writes of a doubleword commute with a tape replacement. -/
theorem store_bytes_map (transform : SailJoltState → SailJoltState)
    (commutes : ∀ state address value, Mmu.store_raw? (transform state) address value =
      (Mmu.store_raw? state address value).map transform)
    (address : Nat) (value : BitVec 64) (offsets : List Nat)
    (start : Option SailJoltState) :
    offsets.foldl (fun current k => current.bind fun state =>
      Mmu.store_raw? state (address + k) (value.extractLsb' (8 * k) 8))
        (start.map transform) =
      (offsets.foldl (fun current k => current.bind fun state =>
        Mmu.store_raw? state (address + k) (value.extractLsb' (8 * k) 8)) start).map
          transform := by
  induction offsets generalizing start with
  | nil => rfl
  | cons k rest ih =>
    simp only [List.foldl_cons]
    cases start with
    | none => simpa using ih none
    | some state =>
      simp only [Option.map_some, Option.bind_some]
      rw [commutes]
      exact ih (Mmu.store_raw? state (address + k) (value.extractLsb' (8 * k) 8))

/-- A checked doubleword store preserves any relation permitting Sail-state changes.
For example, stores preserve both the non-memory device and the advice tape.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`store_doubleword`).
This primitive frame is a candidate to move into JoltBytecode. -/
theorem store_doubleword_relation (relation : SailJoltState → SailJoltState → Prop)
    (refl : ∀ state, relation state state)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (sail : ∀ state after, relation state { state with sail := after })
    (address value : BitVec 64) :
    StatePreservation.Preserves relation (Mmu.store_doubleword address value) := by
  intro s t result runs
  simp only [Mmu.store_doubleword] at runs
  split at runs
  · cases runs
  · split at runs
    · split at runs
      · cases runs; exact sail _ _
      · cases runs
    · split at runs
      · rename_i stored
        cases runs
        exact InstructionFrame.storeFold_rule_of_step
          (relation := relation) _ value s (List.range 8)
          (fun k _ before after kept store => trans _ _ _ kept
            (InstructionFrame.storeRaw_rule sail (fun state _ _ _ _ => sail state _)
              before after _ _ store))
          (some s) (fun _ same => by cases same; exact refl _) _ stored
      · cases runs

/-- A checked doubleword store keeps the entire non-memory device.
For example, an output store changes shared bytes, not the panic claim. -/
theorem store_doubleword_keeps_device (address value : BitVec 64) :
    StatePreservation.Preserves
      (fun s t : SailJoltState => s.jolt_device = t.jolt_device)
      (Mmu.store_doubleword address value) :=
  store_doubleword_relation (fun s t => s.jolt_device = t.jolt_device)
    (fun _ => rfl) (fun _ _ _ ab bc => ab.trans bc) (fun _ _ => rfl) address value

/-- Primitive rules for a device relation.
For example, layout equality and equality of the whole device both qualify:
no instruction changes the device, since a halt records only `halted` and
stores change shared memory. -/
theorem deviceRelationRules (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ device, relation device device)
    (trans : ∀ a b c, relation a b → relation b c → relation a c) :
    InstructionFrame.Rules (fun s t => relation s.jolt_device t.jolt_device) where
  refl s := refl s.jolt_device
  trans a b c := trans a.jolt_device b.jolt_device c.jolt_device
  sail s _ _ := refl s.jolt_device
  vreg s _ _ := refl s.jolt_device
  store address value s t result runs := by
    change relation s.jolt_device t.jolt_device
    rw [← store_doubleword_keeps_device address value s t result runs]
    exact refl s.jolt_device
  halt s _ := refl s.jolt_device
  append s _ := refl s.jolt_device

/-- Every instruction preserves a reflexive, transitive device relation.
For example, every row preserves its memory layout. -/
theorem execInstr_device_relation (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ device, relation device device)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (instruction : Instr) :
    StatePreservation.Preserves
      (fun s t => relation s.jolt_device t.jolt_device) (execInstr instruction) :=
  InstructionFrame.execInstr_rule (deviceRelationRules relation refl trans)
    instruction (fun _ _ _ s _ _ _ => refl s.jolt_device)

end JoltConstraints
