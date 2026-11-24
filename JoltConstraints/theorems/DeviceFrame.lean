import JoltBytecode.InstructionEquivalence.ProofSupport.DeviceFrame

open LeanRV64D
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail
  LeanRV64D.Functions JoltISA

set_option autoImplicit false

namespace JoltConstraints

/-- A successful shared-memory initialization changes only memory, the code span,
the panic claim and the halted marker.
For example, it leaves every starting register and the execution tape unchanged.
This primitive initialization fact is a candidate to move into JoltBytecode. -/
theorem initialState_shape (before after : SailJoltState)
    (sources : List (BitVec 64 × Bool)) (inputs trusted untrusted : Array (BitVec 8))
    (built : initialState before sources inputs trusted untrusted = some after) :
    ∃ region mem,
      codeRegionOf before.jolt_device.memory_layout sources = some region ∧
      before.jolt_device.initialMem before.sail.mem inputs trusted untrusted = some mem ∧
      after = { before with
        sail := { before.sail with mem := mem }
        jolt_device := { before.jolt_device with panic := false }
        codeRegion := region
        halted := none } := by
  obtain ⟨region, regionBuilt, built⟩ := Option.bind_eq_some_iff.mp built
  obtain ⟨mem, memBuilt, built⟩ := Option.bind_eq_some_iff.mp built
  exact ⟨region, mem, regionBuilt, memBuilt, (Option.some.inj built).symm⟩

/-- Installing shared memory commutes with replacing the execution tape.
For example, the same inputs and program yield identical memory for either tape.
This primitive frame is a candidate to move into JoltBytecode. -/
theorem initialState_with_adviceTape (state : SailJoltState)
    (sources : List (BitVec 64 × Bool)) (inputs trusted untrusted : Array (BitVec 8))
    (tape : JoltAdviceTape) :
    initialState { state with adviceTape := tape } sources inputs trusted untrusted =
      (initialState state sources inputs trusted untrusted).map
        (fun after => { after with adviceTape := tape }) := by
  unfold initialState
  cases codeRegionOf state.jolt_device.memory_layout sources <;>
    cases state.jolt_device.initialMem state.sail.mem inputs trusted untrusted <;> rfl

/-- A checked doubleword store keeps the entire non-memory device.
For example, an output store changes shared bytes, not the layout or panic claim.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`store_doubleword`).
This shared-memory frame is a candidate to move into JoltBytecode. -/
theorem store_doubleword_keeps_device (address value : BitVec 64) :
    StatePreservation.Preserves
      (fun s t : SailJoltState => s.jolt_device = t.jolt_device)
      (Mmu.store_doubleword address value) := by
  intro s t result runs
  simp only [Mmu.store_doubleword] at runs
  split at runs
  · cases runs
  · split at runs
    · split at runs
      · cases runs; rfl
      · cases runs
    · split at runs
      · rename_i stored
        cases runs
        exact InstructionFrame.storeFold_rule_of_step
          (relation := fun s t : SailJoltState => s.jolt_device = t.jolt_device)
          _ value s (List.range 8)
          (fun k _ before after kept store => kept.trans
            (InstructionFrame.storeRaw_rule
              (relation := fun s t : SailJoltState => s.jolt_device = t.jolt_device)
              (fun _ _ => rfl) (fun _ _ _ _ _ => rfl) before after _ _ store))
          (some s) (fun _ same => by cases same; rfl) _ stored
      · cases runs

/-- Primitive rules for a device relation, with halt updates made explicit.
For example, layout equality permits every halt; equality of the whole device does not.
Stores affect shared memory and need no device-update premise. -/
theorem deviceRelationRules (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ device, relation device device)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (halt : ∀ device kind,
      relation device { device with panic := (kind == JoltHaltKind.panic) }) :
    InstructionFrame.Rules (fun s t => relation s.jolt_device t.jolt_device) where
  refl s := refl s.jolt_device
  trans a b c := trans a.jolt_device b.jolt_device c.jolt_device
  sail s _ _ := refl s.jolt_device
  vreg s _ _ := refl s.jolt_device
  store address value s t result runs := by
    change relation s.jolt_device t.jolt_device
    rw [← store_doubleword_keeps_device address value s t result runs]
    exact refl s.jolt_device
  halt s kind := halt s.jolt_device kind
  append s _ := refl s.jolt_device

/-- Every instruction preserves a device relation compatible with both halt updates.
For example, every row preserves its memory layout.
The new halt obligation replaces the former device-byte-store obligation. -/
theorem execInstr_device_relation (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ device, relation device device)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (halt : ∀ device kind,
      relation device { device with panic := (kind == JoltHaltKind.panic) })
    (instruction : Instr) :
    StatePreservation.Preserves
      (fun s t => relation s.jolt_device t.jolt_device) (execInstr instruction) :=
  InstructionFrame.execInstr_rule (deviceRelationRules relation refl trans halt)
    instruction (fun _ _ _ s _ _ _ => refl s.jolt_device)

end JoltConstraints
