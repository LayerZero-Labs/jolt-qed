import JoltBytecode.JoltISA.Semantics
import JoltBytecode.InstructionEquivalence.ProofSupport.Preservation
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
so it preserves every reflexive relation on devices. -/
theorem writeDst_rule_of_device_relation
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (dst : Dst) (value : BitVec 64) :
    StatePreservation.Preserves
      (fun s t : SailJoltState => relation s.jolt_device t.jolt_device)
      (writeDst dst value) := by
  cases dst with
  | vreg vr =>
    intro s t result runs
    simp only [writeDst, writeVReg] at runs
    split at runs
    · cases runs
    · cases runs
      exact refl _
  | xreg rd =>
    exact StatePreservation.liftSail_rule (sailRelation := fun _ _ => True)
      (fun _ _ _ => refl _) (fun _ _ _ _ => True.intro)

/-- Shared instruction frame for any reflexive, transitive device relation
that a successful device byte store preserves. -/
theorem execInstr_rule_of_device_relation
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (store : ∀ io io' address value,
      JoltDevice.store? io address value = some io' → relation io io')
    (instr : Instr) :
    StatePreservation.Preserves
      (fun s t => relation s.jolt_device t.jolt_device) (execInstr instr) := by
  let Rel (s t : SailJoltState) : Prop := relation s.jolt_device t.jolt_device
  have reflState (s : SailJoltState) : Rel s s := refl _
  have transState (s m t : SailJoltState) (sm : Rel s m) (mt : Rel m t) : Rel s t :=
    trans _ _ _ sm mt
  have pureRule {α : Type} (value : α) :
      StatePreservation.Preserves Rel (pure value : JoltMonad α) :=
    StatePreservation.pure_rule reflState value
  have bindRule {α β : Type} {first : JoltMonad α} {next : α → JoltMonad β}
      (firstKeeps : StatePreservation.Preserves Rel first)
      (nextKeeps : ∀ result, StatePreservation.Preserves Rel (next result)) :
      StatePreservation.Preserves Rel (first >>= next) :=
    StatePreservation.bind_rule transState firstKeeps nextKeeps
  have throwRule {α : Type} (failure : Error exception) :
      StatePreservation.Preserves Rel (throw failure : JoltMonad α) :=
    StatePreservation.throw_rule Rel failure
  have getRule : StatePreservation.Preserves Rel (get : JoltMonad SailJoltState) :=
    StatePreservation.get_rule reflState
  have liftRule {α : Type} (step : SailM α) :
      StatePreservation.Preserves Rel (liftSail step) :=
    StatePreservation.liftSail_rule (sailRelation := fun _ _ => True)
      (fun _ _ _ => refl _) (fun _ _ _ _ => True.intro)
  have modifyRule (change : SailJoltState → SailJoltState)
      (unchanged : ∀ s, (change s).jolt_device = s.jolt_device) :
      StatePreservation.Preserves Rel (modify change : JoltMonad Unit) := by
    apply StatePreservation.modify_rule (relation := Rel) change
    intro s
    simpa only [Rel, unchanged s] using reflState s
  have readRule (src : Src) : StatePreservation.Preserves Rel (readSrc src) := by
    cases src with
    | vreg vr =>
      intro s t v h
      simp only [readSrc, readVReg, bind, EStateM.bind, get, getThe,
        MonadStateOf.get, EStateM.get, pure, EStateM.pure] at h
      cases h
      exact reflState _
    | xreg rs => exact liftRule _
  have writeRule (dst : Dst) (value : BitVec 64) :
      StatePreservation.Preserves Rel (writeDst dst value) := by
    exact writeDst_rule_of_device_relation relation refl dst value
  have storeRaw (s s' : SailJoltState) (ea : Nat) (value : BitVec 8)
      (h : Mmu.store_raw? s ea value = some s') : Rel s s' := by
    simp only [Mmu.store_raw?] at h
    repeat' split at h
    all_goals first
      | (cases h; exact reflState _)
      | cases h
      | (cases hst : s.jolt_device.store? ea value with
          | none => simp [hst] at h
          | some d =>
              simp only [hst, Option.map_some] at h
              cases h
              exact store _ _ _ _ hst)
  have storeFold (ea : Nat) (value : BitVec 64) (s0 : SailJoltState) :
      ∀ (l : List Nat) (start : Option SailJoltState),
        (∀ s, start = some s → Rel s0 s) →
        ∀ s', l.foldl (fun current k => current.bind fun s =>
          Mmu.store_raw? s (ea + k) (value.extractLsb' (8 * k) 8)) start = some s' →
          Rel s0 s' := by
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
        exact transState _ _ _ (hstart e hst) (storeRaw _ _ _ _ hs)
  have loadDoublewordRule (address : BitVec 64) :
      StatePreservation.Preserves Rel (Mmu.load_doubleword address) := by
    intro s t v h
    simp only [Mmu.load_doubleword] at h
    repeat' split at h
    all_goals first | (cases h; exact reflState _) | cases h
  have storeDoublewordRule (address value : BitVec 64) :
      StatePreservation.Preserves Rel (Mmu.store_doubleword address value) := by
    intro s t v h
    simp only [Mmu.store_doubleword] at h
    repeat' split at h
    all_goals first
      | (cases h; exact reflState _)
      | (rename_i heq
         cases h
         exact storeFold _ value s _ (some s)
           (fun s1 hs1 => by cases hs1; exact reflState _) _ heq)
      | cases h
  have loadRule (address : BitVec 64) :
      StatePreservation.Preserves Rel (Mmu.load address) := by
    intro s t v h
    simp only [Mmu.load] at h
    repeat' split at h
    all_goals first | (cases h; exact reflState _) | cases h
  have readHostBytesRule
      (overflowChecks incrementAfterLast : Bool) {width : Nat}
      (pointer : BitVec width) (n : Nat) (bytes : Array (BitVec 8)) :
      StatePreservation.Preserves Rel
        (readHostBytes Mmu.load overflowChecks incrementAfterLast pointer n bytes) := by
    induction n generalizing pointer bytes with
    | zero => exact pureRule _
    | succ n ih =>
      dsimp only [readHostBytes]
      refine bindRule (loadRule _) (fun result => ?_)
      cases result with
      | Err e => exact pureRule _
      | Ok byte =>
        split_ifs with h
        · exact bindRule (throwRule _) (fun _ => ih _ _)
        · exact bindRule (pureRule _) (fun _ => ih _ _)
  have execHostIORule : StatePreservation.Preserves Rel execHostIO := by
    unfold execHostIO execHostIOWith
    refine bindRule getRule (fun config => ?_)
    dsimp only
    split
    · exact pureRule _
    · refine bindRule (pureRule _) (fun _ => ?_)
      refine bindRule (readRule _) (fun callId => ?_)
      preservation_auto [readHostBytesRule _ _ _ _ _, readRule _, pureRule _, throwRule _,
        modifyRule _ (fun _ => rfl)] using bindRule
  cases instr
  case VirtualAdviceLoad dst byteCount =>
    intro s t v h
    simp only [execInstr] at h
    cases hr : readAdviceTape s.adviceTape byteCount with
    | none => simp only [hr] at h; cases h
    | some pair =>
      obtain ⟨value, tape⟩ := pair
      simp only [hr] at h
      exact (bindRule (writeRule dst value) (fun _ => pureRule _))
        { s with adviceTape := tape } t v h
  all_goals simp only [execInstr]
  all_goals preservation_auto [readRule _, writeRule _ _, pureRule _, throwRule _,
    getRule, liftRule _, loadDoublewordRule _, storeDoublewordRule _ _, execHostIORule]
    using bindRule

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
