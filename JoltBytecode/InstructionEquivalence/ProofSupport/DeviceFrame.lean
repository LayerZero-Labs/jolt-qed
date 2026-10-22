import JoltBytecode.JoltISA.Semantics
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionFrame
import Batteries.Data.Array.Lemmas

/-
Every Jolt ISA instruction leaves the device's memory layout, inputs and advice
buffers unchanged; Rust fixes them in `create_emulator` and never updates them.
-/

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

namespace JoltIOSetupFrame

open JoltISA

/-- The device fields that Rust fixes in `create_emulator` and never updates.
Rust: https://github.com/a16z/jolt/blob/754fc88214936801a7d8a2260d9fc73478be4cbd/tracer/src/lib.rs#L401-L404 -/
def Same (a b : JoltDevice) : Prop :=
  b.memory_layout = a.memory_layout ∧ b.trusted_advice = a.trusted_advice ∧
    b.untrusted_advice = a.untrusted_advice ∧ b.inputs = a.inputs

theorem Same.refl (a : JoltDevice) : Same a a := ⟨rfl, rfl, rfl, rfl⟩

theorem Same.trans {a b c : JoltDevice} (hab : Same a b) (hbc : Same b c) : Same a c :=
  ⟨hbc.1.trans hab.1, hbc.2.1.trans hab.2.1, hbc.2.2.1.trans hab.2.2.1,
    hbc.2.2.2.trans hab.2.2.2⟩

def Preserves {α : Type} (m : JoltMonad α) : Prop :=
  StatePreservation.Preserves (fun s t => Same s.jolt_device t.jolt_device) m

theorem storeDeviceByte_same (io io' : JoltDevice) (address : Nat) (value : BitVec 8)
    (h : JoltDevice.store? io address value = some io') : Same io io' := by
  unfold JoltDevice.store? at h
  split_ifs at h <;> cases h <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A successful device byte store preserves the layout and keeps the output
byte count within the layout's `max_output_size.toNat`. -/
theorem storeDeviceByte_outputs_fit (layout : MemoryLayout)
    (outputSpan : layout.panic.toNat =
      layout.output_start.toNat + layout.max_output_size.toNat)
    (io io' : JoltDevice) (address : Nat) (value : BitVec 8)
    (sameLayout : io.memory_layout = layout)
    (oldBound : io.outputs.size ≤ layout.max_output_size.toNat)
    (stored : io.store? address value = some io') :
    io'.memory_layout = layout ∧
      io'.outputs.size ≤ layout.max_output_size.toNat := by
  unfold JoltDevice.store? at stored
  split_ifs at stored with isPanic special isOutput
  · cases stored
    exact ⟨sameLayout, oldBound⟩
  · cases stored
    exact ⟨sameLayout, oldBound⟩
  · cases stored
    refine ⟨sameLayout, ?_⟩
    have notPanic : io.is_panic address = false := by
      cases hp : io.is_panic address <;> simp_all
    have outputRange : layout.output_start.toNat ≤ address ∧
        address < layout.termination.toNat := by
      simpa [JoltDevice.is_output, sameLayout] using isOutput
    have beforePanic : address < layout.panic.toNat := by
      have panicRange : ¬ (layout.panic.toNat ≤ address ∧
          address < layout.termination.toNat) := by
        simpa [JoltDevice.is_panic, sameLayout] using notPanic
      omega
    simp only [Array.size_set!, Array.size_append, Array.size_replicate]
    rw [sameLayout]
    omega

/-- Writing an integer or virtual register leaves the Jolt device unchanged,
so it preserves every reflexive relation on devices.
For example, writing x5 preserves equality of the input arrays. -/
theorem writeDst_rule_of_device_relation
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (dst : Dst) (value : BitVec 64) :
    StatePreservation.Preserves
      (fun s t : SailJoltState => relation s.jolt_device t.jolt_device)
      (writeDst dst value) :=
  InstructionFrame.writeDst_rule _ (fun _ _ => refl _) (fun _ _ _ => refl _) dst value

/-- Shared instruction frame for any reflexive, transitive device relation
that a successful device byte store preserves.
For example, equality of device inputs is preserved even when an instruction
updates RAM, writes an output byte, or consumes the advice tape. -/
theorem execInstr_rule_of_device_relation
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (store : ∀ io io' address value,
      JoltDevice.store? io address value = some io' → relation io io')
    (instr : Instr) :
    StatePreservation.Preserves
      (fun s t => relation s.jolt_device t.jolt_device) (execInstr instr) :=
  InstructionFrame.execInstr_rule
    (relation := fun s t => relation s.jolt_device t.jolt_device)
    { refl := fun _ => refl _
      trans := fun _ _ _ first second => trans _ _ _ first second
      sail := fun _ _ => refl _
      vreg := fun _ _ _ => refl _
      store := fun _ _ _ _ stored => store _ _ _ _ stored
      append := fun _ _ => refl _ }
    instr (fun _ _ _ _ _ _ _ => refl _)

/-- A raw byte store preserves the device setup fields: layout, advice buffers,
and inputs.
For example, writing an output byte leaves the input array unchanged. -/
theorem store_raw_same (s s' : SailJoltState) (ea : Nat) (value : BitVec 8)
    (h : Mmu.store_raw? s ea value = some s') : Same s.jolt_device s'.jolt_device :=
  InstructionFrame.storeRaw_rule (relation := fun s t => Same s.jolt_device t.jolt_device)
    (fun _ _ => Same.refl _) (fun _ _ _ _ stored => storeDeviceByte_same _ _ _ _ stored)
    s s' ea value h

/-- Every Jolt ISA instruction preserves the device setup fields. -/
theorem execInstr_rule (instr : Instr) : Preserves (execInstr instr) :=
  execInstr_rule_of_device_relation Same Same.refl
    (fun _ _ _ first next => first.trans next) storeDeviceByte_same instr

theorem execProgram_rule (program : Program) : Preserves (execProgram program) := by
  induction program with
  | done result =>
    exact StatePreservation.pure_rule (fun (s : SailJoltState) => Same.refl s.jolt_device) _
  | instr instr rest ih =>
    simp only [execProgram]
    refine StatePreservation.bind_rule
      (relation := fun (s t : SailJoltState) => Same s.jolt_device t.jolt_device)
      (fun _ _ _ first next => first.trans next)
      (execInstr_rule instr) (fun result => ?_)
    split
    · exact ih
    · exact StatePreservation.pure_rule
        (fun (s : SailJoltState) => Same.refl s.jolt_device) _

-- A step that runs any tail program after it keeps the memory layout.
theorem layout_of_tail_run {step : Program → Program} {s t : SailJoltState}
    (h : ∀ tail, (execProgram (step tail)).run s = (execProgram tail).run t) :
    t.jolt_device.memory_layout = s.jolt_device.memory_layout :=
  (execProgram_rule _ s t _ (h (.done RETIRE_SUCCESS))).1

-- A single instruction keeps the memory layout.
theorem layout_of_instr_run {instr : Instr} {s t : SailJoltState} {r : ExecutionResult}
    (h : (execInstr instr).run s = .ok r t) :
    t.jolt_device.memory_layout = s.jolt_device.memory_layout :=
  (execInstr_rule instr s t r h).1

end JoltIOSetupFrame
