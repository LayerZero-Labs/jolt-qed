import JoltConstraints.theorems.DeviceFrame

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

/-- A successful doubleword store has the same shared-map effect in RAM and
the I/O window, with no device-array update.
For example, a gap-word store writes all eight little-endian bytes and retains
the panic claim and code interval.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`Mmu::store_doubleword_raw`).
This primitive execution fact is a candidate to move into JoltBytecode. -/
theorem store_doubleword_shape (before after : SailJoltState) (address value : BitVec 64)
    (stored : Mmu.store_doubleword address value before = .ok (.Ok true) after) :
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

end JoltConstraints
