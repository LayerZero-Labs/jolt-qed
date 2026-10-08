import JoltBytecode.JoltISA.Semantics
import JoltBytecode.InstructionEquivalence.ProofSupport.Preservation

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

theorem pure_rule {α : Type} (v : α) : Preserves (pure v) :=
  StatePreservation.pure_rule (fun (s : SailJoltState) => Same.refl s.jolt_device) v

theorem bind_rule {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    (hm : Preserves m) (hf : ∀ x, Preserves (f x)) : Preserves (m >>= f) :=
  StatePreservation.bind_rule (fun _ _ _ first next => first.trans next) hm hf

theorem lift_rule {α : Type} (m : SailM α) : Preserves (liftSail m) :=
  StatePreservation.liftSail_rule (sailRelation := fun _ _ => True)
    (fun _ _ _ => Same.refl _) (fun _ _ _ _ => True.intro)

theorem throw_rule {α : Type} (e : Error exception) :
    Preserves (throw e : JoltMonad α) :=
  StatePreservation.throw_rule _ e

theorem get_rule : Preserves (get : JoltMonad SailJoltState) :=
  StatePreservation.get_rule (fun (s : SailJoltState) => Same.refl s.jolt_device)

theorem modify_rule (f : SailJoltState → SailJoltState)
    (hf : ∀ s, (f s).jolt_device = s.jolt_device) : Preserves (modify f : JoltMonad Unit) :=
  StatePreservation.modify_rule f (fun s => by rw [hf s]; exact Same.refl _)

theorem read_rule (src : Src) : Preserves (readSrc src) := by
  cases src with
  | vreg vr =>
    intro s t v h
    simp only [readSrc, readVReg, bind, EStateM.bind, get, getThe, MonadStateOf.get,
      EStateM.get, pure, EStateM.pure] at h
    cases h
    exact Same.refl _
  | xreg rs => exact lift_rule _

theorem write_rule (dst : Dst) (value : BitVec 64) : Preserves (writeDst dst value) := by
  cases dst with
  | vreg vr =>
    by_cases hw : vr.toNat < 32
    · simp only [writeDst, writeVReg, hw, ↓reduceIte]
      exact throw_rule _
    · simp only [writeDst, writeVReg, hw, ↓reduceIte]
      exact modify_rule _ (fun _ => rfl)
  | xreg rd => exact lift_rule _

theorem storeDeviceByte_same (io io' : JoltDevice) (address : Nat) (value : BitVec 8)
    (h : JoltDevice.store? io address value = some io') : Same io io' := by
  unfold JoltDevice.store? at h
  split_ifs at h <;> cases h <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem store_raw_same (s s' : SailJoltState) (ea : Nat) (value : BitVec 8)
    (h : Mmu.store_raw? s ea value = some s') : Same s.jolt_device s'.jolt_device := by
  simp only [Mmu.store_raw?] at h
  repeat' split at h
  all_goals first
    | (cases h; exact Same.refl _)
    | cases h
    | (cases hst : s.jolt_device.store? ea value with
        | none => simp [hst] at h
        | some d =>
            simp only [hst, Option.map_some] at h
            cases h
            exact storeDeviceByte_same _ _ _ _ hst)

theorem store_raw_fold_same (ea : Nat) (value : BitVec 64) (s0 : SailJoltState) :
    ∀ (l : List Nat) (start : Option SailJoltState),
      (∀ s, start = some s → Same s0.jolt_device s.jolt_device) →
      ∀ s', l.foldl (fun current k => current.bind fun s =>
        Mmu.store_raw? s (ea + k) (value.extractLsb' (8 * k) 8)) start = some s' →
      Same s0.jolt_device s'.jolt_device := by
  intro l
  induction l with
  | nil => intro start hstart s' hs'; exact hstart s' hs'
  | cons k l ih =>
    intro start hstart s' hs'
    refine ih _ ?_ s' hs'
    intro s hs
    cases hst : start with
    | none => rw [hst] at hs; cases hs
    | some e =>
      rw [hst] at hs
      exact (hstart e hst).trans (store_raw_same _ _ _ _ hs)

theorem load_doubleword_rule (address : BitVec 64) :
    Preserves (Mmu.load_doubleword address) := by
  intro s t v h
  simp only [Mmu.load_doubleword] at h
  repeat' split at h
  all_goals first | (cases h; exact Same.refl _) | cases h

theorem store_doubleword_rule (address value : BitVec 64) :
    Preserves (Mmu.store_doubleword address value) := by
  intro s t v h
  simp only [Mmu.store_doubleword] at h
  repeat' split at h
  all_goals first
    | (cases h; exact Same.refl _)
    | (rename_i heq
       cases h
       exact store_raw_fold_same _ value s _ (some s)
         (fun s1 hs1 => by cases hs1; exact Same.refl _) _ heq)
    | cases h

theorem load_rule (address : BitVec 64) : Preserves (Mmu.load address) := by
  intro s t v h
  simp only [Mmu.load] at h
  split at h
  all_goals first | (cases h; exact Same.refl _) | cases h

theorem readHostBytes_rule
    (overflowChecks incrementAfterLast : Bool) {width : Nat}
    (pointer : BitVec width) (n : Nat) (bytes : Array (BitVec 8)) :
    Preserves (readHostBytes Mmu.load overflowChecks incrementAfterLast pointer n bytes) := by
  induction n generalizing pointer bytes with
  | zero => exact pure_rule _
  | succ n ih =>
    dsimp only [readHostBytes]
    refine bind_rule (load_rule _) (fun result => ?_)
    cases result with
    | Err e => exact pure_rule _
    | Ok byte =>
      split_ifs with h
      · exact bind_rule (throw_rule _) (fun _ => ih _ _)
      · exact bind_rule (pure_rule _) (fun _ => ih _ _)

theorem execHostIO_rule : Preserves execHostIO := by
  unfold execHostIO execHostIOWith
  refine bind_rule get_rule (fun config => ?_)
  dsimp only
  split
  · exact pure_rule _
  · refine bind_rule (pure_rule _) (fun _ => ?_)
    refine bind_rule (read_rule _) (fun callId => ?_)
    preservation_auto [readHostBytes_rule _ _ _ _ _, read_rule _, pure_rule _, throw_rule _,
      modify_rule _ (fun _ => rfl)] using bind_rule

/-- Every Jolt ISA instruction preserves the device setup fields. -/
theorem execInstr_rule (instr : Instr) : Preserves (execInstr instr) := by
  cases instr
  case VirtualAdviceLoad dst byteCount =>
    intro s t v h
    simp only [execInstr] at h
    cases hr : readAdviceTape s.adviceTape byteCount with
    | none => simp only [hr] at h; cases h
    | some pair =>
      obtain ⟨value, tape⟩ := pair
      simp only [hr] at h
      exact (bind_rule (write_rule dst value) (fun _ => pure_rule _))
        { s with adviceTape := tape } t v h
  all_goals simp only [execInstr]
  all_goals preservation_auto [read_rule _, write_rule _ _, pure_rule _, throw_rule _,
    get_rule, lift_rule _, load_doubleword_rule _, store_doubleword_rule _ _, execHostIO_rule]
    using bind_rule

theorem execProgram_rule (program : Program) : Preserves (execProgram program) := by
  induction program with
  | done result => exact pure_rule _
  | instr instr rest ih =>
    simp only [execProgram]
    refine bind_rule (execInstr_rule instr) (fun result => ?_)
    split
    · exact ih
    · exact pure_rule _

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
