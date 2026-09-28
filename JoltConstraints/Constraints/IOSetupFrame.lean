import JoltConstraints.Constraints.RamReadData

/-!
Execution never changes the device fields fixed when Rust builds its emulator:
the memory layout and both advice buffers. Sail steps do not touch the device,
device stores only change `outputs` and `panic`, and HostIO only appends to the
advice tape. The trace-level result carries this from the program's initial
state to the final recorded state.
-/

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

namespace JoltIOSetupFrame

open JoltISA

/-- The device fields that Rust fixes in `create_emulator` and never updates.
Rust: https://github.com/a16z/jolt/blob/754fc88214936801a7d8a2260d9fc73478be4cbd/tracer/src/lib.rs#L401-L404 -/
def Same (a b : JoltIOState) : Prop :=
  b.layout = a.layout ∧ b.trustedAdvice = a.trustedAdvice ∧
    b.untrustedAdvice = a.untrustedAdvice

theorem Same.refl (a : JoltIOState) : Same a a := ⟨rfl, rfl, rfl⟩

theorem Same.trans {a b c : JoltIOState} (hab : Same a b) (hbc : Same b c) : Same a c :=
  ⟨hbc.1.trans hab.1, hbc.2.1.trans hab.2.1, hbc.2.2.trans hab.2.2⟩

def Preserves {α : Type} (m : JoltMonad α) : Prop :=
  ∀ (s t : SailJoltState) (v : α), m s = .ok v t → Same s.io t.io

theorem pure_rule {α : Type} (v : α) : Preserves (pure v) := by
  intro s t x h
  cases h
  exact Same.refl _

theorem bind_rule {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    (hm : Preserves m) (hf : ∀ x, Preserves (f x)) : Preserves (m >>= f) := by
  intro s t v h
  cases hr : m s with
  | error e s' => simp only [bind, EStateM.bind, hr] at h; cases h
  | ok x s' =>
    simp only [bind, EStateM.bind, hr] at h
    exact (hm s s' x hr).trans (hf x s' t v h)

theorem lift_rule {α : Type} (m : SailM α) : Preserves (liftSail m) := by
  intro s t v h
  cases hr : m s.sail with
  | error e s' => simp only [liftSail, hr] at h; cases h
  | ok x s' =>
    simp only [liftSail, hr] at h
    cases h
    exact Same.refl _

theorem throw_rule {α : Type} (e : Error exception) :
    Preserves (throw e : JoltMonad α) := by
  intro s t x h
  cases h

theorem get_rule : Preserves (get : JoltMonad SailJoltState) := by
  intro s t x h
  cases h
  exact Same.refl _

theorem modify_rule (f : SailJoltState → SailJoltState)
    (hf : ∀ s, (f s).io = s.io) : Preserves (modify f : JoltMonad Unit) := by
  intro s t x h
  cases h
  rw [hf s]
  exact Same.refl _

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

theorem storeDeviceByte_same (io io' : JoltIOState) (address : Nat) (value : BitVec 8)
    (h : storeDeviceByte? io address value = some io') : Same io io' := by
  unfold storeDeviceByte? at h
  split_ifs at h <;> cases h <;> exact ⟨rfl, rfl, rfl⟩

theorem storeDeviceWord_same (io io' : JoltIOState) (address value : BitVec 64)
    (h : storeDeviceWord? io address value = some io') : Same io io' := by
  unfold storeDeviceWord? at h
  suffices hfold : ∀ (l : List Nat) (start : Option JoltIOState),
      (∀ d, start = some d → Same io d) →
      ∀ d, l.foldl (fun current k => current.bind fun device =>
        storeDeviceByte? device (address.toNat + k) (value.extractLsb' (8 * k) 8)) start =
          some d → Same io d from
    hfold _ _ (fun d hd => by cases hd; exact Same.refl _) _ h
  intro l
  induction l with
  | nil => intro start hstart d hd; exact hstart d hd
  | cons k l ih =>
    intro start hstart d hd
    refine ih _ ?_ d hd
    intro d' hd'
    cases hs : start with
    | none => rw [hs] at hd'; cases hd'
    | some e =>
      rw [hs] at hd'
      exact (hstart e hs).trans (storeDeviceByte_same _ _ _ _ hd')

theorem readMemoryWord_rule (address : BitVec 64) :
    Preserves (readMemoryWord address) := by
  intro s t v h
  unfold readMemoryWord at h
  split_ifs at h
  · split at h <;> (cases h; exact Same.refl _)
  · exact lift_rule _ s t v h

theorem writeMemoryWord_rule (address value : BitVec 64) :
    Preserves (writeMemoryWord address value) := by
  intro s t v h
  unfold writeMemoryWord at h
  split_ifs at h
  · split at h
    · rename_i io hio
      cases h
      exact storeDeviceWord_same _ _ _ _ hio
    · cases h
      exact Same.refl _
  · exact lift_rule _ s t v h

theorem readMemoryByte_rule (address : BitVec 64) :
    Preserves (readMemoryByte address) := by
  intro s t v h
  unfold readMemoryByte at h
  dsimp only at h
  split_ifs at h
  · cases hb : deviceByte? s.io address.toNat with
    | none => simp only [hb] at h; cases h
    | some byte => simp only [hb] at h; cases h; exact Same.refl _
  · exact lift_rule _ s t v h

theorem readHostBytes_rule
    (overflowChecks incrementAfterLast : Bool) {width : Nat}
    (pointer : BitVec width) (n : Nat) (bytes : Array (BitVec 8)) :
    Preserves (readHostBytes readMemoryByte overflowChecks incrementAfterLast pointer n bytes) := by
  induction n generalizing pointer bytes with
  | zero => exact pure_rule _
  | succ n ih =>
    dsimp only [readHostBytes]
    refine bind_rule (readMemoryByte_rule _) (fun result => ?_)
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
    repeat' first
      | exact readHostBytes_rule _ _ _ _ _
      | exact read_rule _
      | exact pure_rule _
      | exact throw_rule _
      | exact modify_rule _ (fun _ => rfl)
      | split
      | refine bind_rule ?_ (fun x => ?_)

macro "jolt_io_setup_auto" : tactic => `(tactic|
  repeat' first
  | exact read_rule _
  | exact write_rule _ _
  | exact pure_rule _
  | exact throw_rule _
  | exact get_rule
  | exact lift_rule _
  | exact readMemoryWord_rule _
  | exact writeMemoryWord_rule _ _
  | exact execHostIO_rule
  | split
  | refine bind_rule ?_ (fun x => ?_))

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
  all_goals jolt_io_setup_auto

end JoltIOSetupFrame

namespace JoltConstraints

open JoltIOSetupFrame

/-- Every recorded pre-state has the program's initial device setup. -/
theorem trace_preState_ioSame {program : JoltProgram} (trace : JoltTrace program)
    (i : Nat) (hi : i < trace.rows.size) :
    Same program.initialState.io (getElem trace.rows i hi).preState.io := by
  induction i with
  | zero =>
    rw [trace.startsAtInitial (by omega)]
    exact Same.refl _
  | succ i ih =>
    have hprev := ih (by omega)
    have hexec := execInstr_rule _ _ _ _ (getElem trace.rows i (by omega)).executes
    have hlink := trace.linked i (by omega) hi
    dsimp only at hlink
    rw [hlink]
    split
    · exact hprev.trans hexec
    · exact hprev.trans hexec

/-- The final recorded state has the program's initial device setup. -/
theorem finalTraceState_ioSame {program : JoltProgram} (trace : JoltTrace program) :
    Same program.initialState.io (HonestWitness.finalTraceState trace).io := by
  unfold HonestWitness.finalTraceState
  split
  · rename_i nonempty
    exact (trace_preState_ioSame trace _ _).trans
      (execInstr_rule _ _ _ _ (getElem trace.rows (trace.rows.size - 1) _).executes)
  · exact Same.refl _

end JoltConstraints
