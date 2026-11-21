import JoltBytecode.Step.Lift
import JoltBytecode.JoltISA.Semantics

/-!
Jolt rows read RAM through zero-default byte reads and use the Jolt device
below RAM.
Thus two embedded Sail memories can differ in byte presence and below RAM
without changing a row's result.
For example, a missing RAM byte and an explicitly stored zero behave alike.
-/

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open JoltISA

set_option autoImplicit false

noncomputable section

namespace WholeRun

/-- A ghost has the same registers, virtual registers, device, advice tape and
host configuration as the real state, and the same zero-default RAM bytes.
Its other Sail fields and its memory below RAM may differ.
For example, adding a present zero byte to otherwise empty RAM gives a shadow. -/
structure Shadow (js g : SailJoltState) : Prop where
  regs : g.sail.regs = js.sail.regs
  vregs : g.vregs = js.vregs
  device : g.jolt_device = js.jolt_device
  tape : g.adviceTape = js.adviceTape
  host : g.hostIO = js.hostIO
  ram : ∀ a, RAM_START_ADDRESS ≤ a → Mmu.ram_byte g.sail.mem a = Mmu.ram_byte js.sail.mem a

/-- Memory evolution that preserves byte presence and keeps every byte below
RAM unchanged.
For example, inserting a byte at `0x80000000` has this property. -/
structure MemoryFrame (s t : SailJoltState) : Prop where
  present : ∀ a, (s.sail.mem.get? a).isSome → (t.sail.mem.get? a).isSome
  below : ∀ a, a < RAM_START_ADDRESS → t.sail.mem.get? a = s.sail.mem.get? a

private theorem MemoryFrame.refl (s : SailJoltState) : MemoryFrame s s :=
  ⟨fun _ h => h, fun _ _ => rfl⟩

private theorem MemoryFrame.trans {s t u : SailJoltState}
    (h : MemoryFrame s t) (k : MemoryFrame t u) : MemoryFrame s u :=
  ⟨fun a ha => k.present a (h.present a ha), fun a ha => (k.below a ha).trans (h.below a ha)⟩

private theorem frame_eq {s t : SailJoltState} (h : t.sail.mem = s.sail.mem) :
    MemoryFrame s t := by
  constructor
  · intro a ha; rwa [h]
  · intro a _; rw [h]

/-- Results agree in constructor and return value or error, with their states
related by `R`.
For example, two successful ADD rows return the same retirement value. -/
inductive SameResult {α : Type} (R : SailJoltState → SailJoltState → Prop) :
    EStateM.Result (Error exception) SailJoltState α →
    EStateM.Result (Error exception) SailJoltState α → Prop where
  | ok (a : α) {s t : SailJoltState} : R s t → SameResult R (.ok a s) (.ok a t)
  | error (e : Error exception) {s t : SailJoltState} :
      R s t → SameResult R (.error e s) (.error e t)

/-- A successful left result forces a successful right result with the same
value and related state; for example, a retiring real block forces its shadow
block to retire too. -/
theorem SameResult.ok_exists {α : Type} {R : SailJoltState → SailJoltState → Prop}
    {a : α} {s : SailJoltState} {q : EStateM.Result (Error exception) SailJoltState α}
    (h : SameResult R (.ok a s) q) : ∃ g, q = .ok a g ∧ R s g := by
  cases h with
  | ok a he => exact ⟨_, rfl, he⟩

private def Effects (s g s' g' : SailJoltState) : Prop :=
  Shadow s' g' ∧ MemoryFrame s s' ∧ MemoryFrame g g'

private theorem SameResult.mono {α : Type} {R S : SailJoltState → SailJoltState → Prop}
    {r q : EStateM.Result (Error exception) SailJoltState α}
    (h : SameResult R r q) (hf : ∀ s g, R s g → S s g) : SameResult S r q := by
  cases h with
  | ok a he => exact .ok a (hf _ _ he)
  | error e he => exact .error e (hf _ _ he)

private def continueResult {α β : Type} (f : α → JoltMonad β) :
    EStateM.Result (Error exception) SailJoltState α →
      EStateM.Result (Error exception) SailJoltState β
  | .ok a s => f a s
  | .error e s => .error e s

private theorem SameResult.bind {α β : Type} {R S : SailJoltState → SailJoltState → Prop}
    {r q : EStateM.Result (Error exception) SailJoltState α} (f : α → JoltMonad β)
    (h : SameResult R r q) (hf : ∀ a s g, R s g → SameResult S (f a s) (f a g))
    (he : ∀ s g, R s g → S s g) :
    SameResult S (continueResult f r) (continueResult f q) := by
  cases h with
  | ok a hr => exact hf a _ _ hr
  | error e hr => exact .error e (he _ _ hr)

private def Tracks {α : Type} (m : JoltMonad α) : Prop :=
  ∀ s g, Shadow s g → SameResult (Effects s g) (m s) (m g)

private theorem tracks_pure {α : Type} (a : α) : Tracks (pure a) :=
  fun s g h => .ok a ⟨h, .refl s, .refl g⟩

private theorem tracks_throw {α : Type} (e : Error exception) :
    Tracks (throw e : JoltMonad α) := fun s g h => .error e ⟨h, .refl s, .refl g⟩

private theorem tracks_bind {α β : Type} {m : JoltMonad α} {f : α → JoltMonad β}
    (hm : Tracks m) (hf : ∀ a, Tracks (f a)) : Tracks (m >>= f) := by
  intro s g h
  have hb : ∀ st, (m >>= f) st = continueResult f (m st) := by
    intro st
    change EStateM.bind m f st = continueResult f (m st)
    unfold EStateM.bind
    cases m st <;> rfl
  rw [hb s, hb g]
  refine SameResult.bind f (hm s g h) ?_ (fun _ _ he => he)
  intro a s' g' he
  exact (hf a s' g' he.1).mono fun _ _ hn =>
    ⟨hn.1, he.2.1.trans hn.2.1, he.2.2.trans hn.2.2⟩

private theorem tracks_ite {α : Type} {c : Prop} [Decidable c] {m n : JoltMonad α}
    (hm : Tracks m) (hn : Tracks n) : Tracks (if c then m else n) := by
  split <;> assumption

private theorem tracks_modify (f : SailJoltState → SailJoltState)
    (hf : ∀ s g, Shadow s g → Shadow (f s) (f g))
    (hmem : ∀ s, (f s).sail.mem = s.sail.mem) : Tracks (modify f) :=
  fun s g h => .ok () ⟨hf s g h, frame_eq (hmem s), frame_eq (hmem g)⟩

private theorem tracks_get_bind {α : Type} {f : SailJoltState → JoltMonad α}
    (hf : ∀ s g, Shadow s g → f g = f s) (ht : ∀ s, Tracks (f s)) :
    Tracks (get >>= f) := by
  intro s g h
  change SameResult _ (f s s) (f g g)
  rw [hf s g h]
  exact ht s s g h

private def SailTracks {α : Type} (m : SailM α) : Prop := Tracks (liftSail m)

private theorem sail_pure {α : Type} (a : α) : SailTracks (pure a) := tracks_pure a

private theorem sail_bind {α β : Type} {m : SailM α} {f : α → SailM β}
    (hm : SailTracks m) (hf : ∀ a, SailTracks (f a)) : SailTracks (m >>= f) := by
  unfold SailTracks
  rw [Projection.liftSail_bind]
  exact tracks_bind hm hf

private theorem sail_ite {α : Type} {c : Prop} [Decidable c] {m n : SailM α}
    (hm : SailTracks m) (hn : SailTracks n) : SailTracks (if c then m else n) := by
  split <;> assumption

private theorem sail_read (r : Register) :
    SailTracks (LeanRV64D.readReg r : SailM (RegisterType r)) := by
  intro s g h
  have hg : g.sail.regs.get? r = s.sail.regs.get? r := congrArg (·.get? r) h.regs
  unfold liftSail
  cases hs : s.sail.regs.get? r with
  | none =>
    rw [Step.readReg_eq_of_get?_none r _ hs, Step.readReg_eq_of_get?_none r _ (hg.trans hs)]
    exact .error _ ⟨h, .refl _, .refl _⟩
  | some v =>
    rw [readReg_eq_of_get? r _ v hs, readReg_eq_of_get? r _ v (hg.trans hs)]
    exact .ok _ ⟨h, .refl _, .refl _⟩

private theorem sail_write (r : Register) (v : RegisterType r) :
    SailTracks (LeanRV64D.writeReg r v : SailM Unit) := by
  intro s g h
  exact .ok () ⟨{ h with regs := congrArg (fun regs => regs.insert r v) h.regs },
    frame_eq rfl, frame_eq rfl⟩

private theorem sail_assert (b : Bool) (msg : String) :
    SailTracks (LeanRV64D.sail_assert b msg) := by
  intro s g h
  cases b
  · exact .error _ ⟨h, .refl _, .refl _⟩
  · exact .ok _ ⟨h, .refl _, .refl _⟩

private theorem sail_and {m n : SailM Bool} (hm : SailTracks m) (hn : SailTracks n) :
    SailTracks (m <&&> n) := by
  unfold _root_.andM
  refine sail_bind hm fun b => ?_
  cases b
  · exact sail_pure _
  · exact hn

local macro "sail_tracks" : tactic =>
  `(tactic| repeat' (first
    | exact sail_read _
    | exact sail_write _ _
    | exact sail_assert _ _
    | exact sail_pure _
    | apply sail_and
    | apply sail_ite
    | apply sail_bind
    | split
    | intro _))

private theorem sail_rX (r : regidx) : SailTracks (rX_bits r) := by
  unfold rX_bits rX
  sail_tracks

private theorem sail_wX (r : regidx) (v : BitVec 64) : SailTracks (wX_bits r v) := by
  unfold wX_bits wX xreg_write_callback
  sail_tracks

private theorem tracks_readSrc (src : Src) : Tracks (readSrc src) := by
  cases src with
  | xreg r => exact sail_rX r
  | vreg r =>
    intro s g h
    change SameResult _ (.ok (s.vregs r) s) (.ok (g.vregs r) g)
    rw [h.vregs]
    exact .ok _ ⟨h, .refl _, .refl _⟩

private theorem tracks_writeDst (dst : Dst) (v : BitVec 64) : Tracks (writeDst dst v) := by
  cases dst with
  | xreg r => exact sail_wX r v
  | vreg r =>
    unfold writeDst writeVReg
    apply tracks_ite (tracks_throw _)
    apply tracks_modify
    · intro s g h
      exact { h with vregs := by dsimp only; rw [h.vregs] }
    · intro _; rfl

private theorem load_raw_shadow {s g : SailJoltState} (h : Shadow s g) (a : Nat) :
    Mmu.load_raw? g a = Mmu.load_raw? s a := by
  unfold Mmu.load_raw?
  dsimp only
  rw [h.device]
  split
  · rfl
  · split
    · rw [h.ram a (by assumption)]
    · rfl

private theorem tracks_load (address : BitVec 64) : Tracks (Mmu.load address) := by
  intro s g h
  have he : Mmu.load? g address.toNat = Mmu.load? s address.toNat := by
    unfold Mmu.load?
    rw [h.device, load_raw_shadow h]
  unfold Mmu.load
  rw [he]
  cases Mmu.load? s address.toNat
  · exact .error _ ⟨h, .refl _, .refl _⟩
  · exact .ok _ ⟨h, .refl _, .refl _⟩

private theorem tracks_load_doubleword (address : BitVec 64) :
    Tracks (Mmu.load_doubleword address) := by
  intro s g h
  have hraw : Mmu.load_raw? g = Mmu.load_raw? s := funext (load_raw_shadow h)
  unfold Mmu.load_doubleword
  dsimp only
  rw [h.device, hraw]
  split
  · exact .error _ ⟨h, .refl _, .refl _⟩
  · split
    · rename_i hram
      have hd : Mmu.ram_doubleword g.sail.mem address.toNat =
          Mmu.ram_doubleword s.sail.mem address.toNat := by
        unfold Mmu.ram_doubleword
        rw [h.ram _ (by omega), h.ram _ (by omega), h.ram _ (by omega),
          h.ram _ (by omega), h.ram _ (by omega), h.ram _ (by omega),
          h.ram _ (by omega), h.ram _ hram]
      rw [hd]
      split
      · exact .ok _ ⟨h, .refl _, .refl _⟩
      · exact .error _ ⟨h, .refl _, .refl _⟩
    · cases read_doubleword? (Mmu.load_raw? s) address.toNat
      · exact .error _ ⟨h, .refl _, .refl _⟩
      · exact .ok _ ⟨h, .refl _, .refl _⟩

private theorem frame_insert (s : SailJoltState) (a : Nat) (v : BitVec 8)
    (ha : RAM_START_ADDRESS ≤ a) :
    MemoryFrame s { s with sail := { s.sail with mem := s.sail.mem.insert a v } } := by
  constructor
  · intro b hb
    by_cases hab : a = b
    · subst b; simp
    · simpa [Std.ExtHashMap.getElem?_insert, hab] using hb
  · intro b hb
    simp [Std.ExtHashMap.getElem?_insert, show a ≠ b by omega]

private theorem shadow_insert {s g : SailJoltState} (h : Shadow s g) (a : Nat)
    (v : BitVec 8) :
    Shadow { s with sail := { s.sail with mem := s.sail.mem.insert a v } }
      { g with sail := { g.sail with mem := g.sail.mem.insert a v } } := by
  refine { h with ram := ?_ }
  intro b hb
  by_cases hab : a = b
  · subst b; simp [Mmu.ram_byte]
  · simpa [Mmu.ram_byte, Std.ExtHashMap.getElem?_insert, hab] using h.ram b hb

private inductive SameOption (R : SailJoltState → SailJoltState → Prop) :
    Option SailJoltState → Option SailJoltState → Prop where
  | none : SameOption R none none
  | some {s g : SailJoltState} : R s g → SameOption R (some s) (some g)

private theorem SameOption.mono {R S : SailJoltState → SailJoltState → Prop}
    {r q : Option SailJoltState} (h : SameOption R r q)
    (hf : ∀ s g, R s g → S s g) : SameOption S r q := by
  cases h with
  | none => exact .none
  | some he => exact .some (hf _ _ he)

private theorem store_raw_shadow (s g : SailJoltState) (h : Shadow s g)
    (a : Nat) (v : BitVec 8) :
    SameOption (Effects s g) (Mmu.store_raw? s a v) (Mmu.store_raw? g a v) := by
  unfold Mmu.store_raw?
  rw [h.device]
  split
  · rename_i ha
    split
    · refine .some ⟨?_, frame_insert s a v ha, ?_⟩
      · simpa only [h.device] using shadow_insert h a v
      · exact ⟨(frame_insert g a v ha).present, (frame_insert g a v ha).below⟩
    · exact .none
  · split
    · exact .none
    · split
      · exact .none
      · cases hd : s.jolt_device.store? a v with
        | none => exact .none
        | some device =>
          exact .some ⟨{ h with device := rfl }, frame_eq rfl, frame_eq rfl⟩

private theorem store_bytes_shadow (a : Nat) (v : BitVec 64) (ks : List Nat)
    (s g : SailJoltState) (current ghost : Option SailJoltState)
    (h : SameOption (Effects s g) current ghost) :
    SameOption (Effects s g)
      (ks.foldl (fun c k => c.bind fun st =>
        Mmu.store_raw? st (a + k) (v.extractLsb' (8 * k) 8)) current)
      (ks.foldl (fun c k => c.bind fun st =>
        Mmu.store_raw? st (a + k) (v.extractLsb' (8 * k) 8)) ghost) := by
  induction ks generalizing current ghost with
  | nil => exact h
  | cons k ks ih =>
    apply ih
    cases h with
    | none => exact .none
    | some he =>
      exact (store_raw_shadow _ _ he.1 (a + k) (v.extractLsb' (8 * k) 8)).mono
        fun _ _ hf => ⟨hf.1, he.2.1.trans hf.2.1, he.2.2.trans hf.2.2⟩

private theorem ram_write_shadow (a : Nat) (v : BitVec 64) (ks : List Nat)
    (s g : SailJoltState) (h : Shadow s g) (ha : RAM_START_ADDRESS ≤ a) :
    Effects s g
      ({ s with sail := { s.sail with mem := ks.foldl (fun m k => m.insert (a + k) (v.extractLsb' (8 * k) 8)) s.sail.mem } })
      ({ g with sail := { g.sail with mem := ks.foldl (fun m k => m.insert (a + k) (v.extractLsb' (8 * k) 8)) g.sail.mem } }) := by
  induction ks generalizing s g with
  | nil => exact ⟨h, .refl _, .refl _⟩
  | cons k ks ih =>
    have hs := frame_insert s (a + k) (v.extractLsb' (8 * k) 8) (by omega)
    have hg := frame_insert g (a + k) (v.extractLsb' (8 * k) 8) (by omega)
    have hn := ih _ _ (shadow_insert h (a + k) (v.extractLsb' (8 * k) 8))
    exact ⟨hn.1, hs.trans hn.2.1, hg.trans hn.2.2⟩

private theorem tracks_store_doubleword (address v : BitVec 64) :
    Tracks (Mmu.store_doubleword address v) := by
  intro s g h
  unfold Mmu.store_doubleword
  dsimp only
  rw [h.device]
  split
  · exact .error _ ⟨h, .refl _, .refl _⟩
  · split
    · rename_i ha
      split
      · have he := ram_write_shadow _ v (List.range 8) s g h ha
        exact .ok _ ⟨by simpa only [Mmu.write_ram_doubleword, h.device] using he.1,
          he.2.1, ⟨he.2.2.present, he.2.2.below⟩⟩
      · exact .error _ ⟨h, .refl _, .refl _⟩
    · have hb := store_bytes_shadow address.toNat v (List.range 8) s g (some s) (some g)
        (.some ⟨h, .refl _, .refl _⟩)
      generalize hreal : (List.range 8).foldl (fun c k => c.bind fun st =>
        Mmu.store_raw? st (address.toNat + k) (v.extractLsb' (8 * k) 8)) (some s) = real
        at hb ⊢
      generalize hghost : (List.range 8).foldl (fun c k => c.bind fun st =>
        Mmu.store_raw? st (address.toNat + k) (v.extractLsb' (8 * k) 8)) (some g) = ghost
        at hb ⊢
      cases hb with
      | none => exact .error _ ⟨h, .refl _, .refl _⟩
      | some he => exact .ok _ he

private theorem sail_map {α β : Type} (f : α → β) {m : SailM α}
    (hm : SailTracks m) : SailTracks (f <$> m) := by
  have he : f <$> m = m >>= fun a => pure (f a) := by
    funext s; cases m s <;> rfl
  rw [he]
  exact sail_bind hm fun _ => sail_pure _

private def SailETracks {ε α : Type} (m : SailME ε α) : Prop := SailTracks (ExceptT.run m)

private theorem sailE_pure {ε α : Type} (a : α) : SailETracks (pure a : SailME ε α) :=
  sail_pure (Except.ok (ε := Error exception ⊕ ε) a)

private theorem sailE_bind {ε α β : Type} {m : SailME ε α} {f : α → SailME ε β}
    (hm : SailETracks m) (hf : ∀ a, SailETracks (f a)) : SailETracks (m >>= f) := by
  change SailTracks (ExceptT.run m >>= ExceptT.bindCont f)
  refine sail_bind hm fun result => ?_
  cases result with
  | error _ => exact sail_pure _
  | ok a => exact hf a

private theorem sailE_lift {ε α : Type} {m : SailM α} (hm : SailTracks m) :
    SailETracks (liftM m : SailME ε α) := sail_map Except.ok hm

private theorem sailE_and {ε : Type} {m n : SailME ε Bool}
    (hm : SailETracks m) (hn : SailETracks n) : SailETracks (m <&&> n) := by
  unfold _root_.andM
  refine sailE_bind hm fun b => ?_
  cases b
  · exact sailE_pure _
  · exact hn

private theorem sailE_ite {ε α : Type} {c : Prop} [Decidable c] {m n : SailME ε α}
    (hm : SailETracks m) (hn : SailETracks n) : SailETracks (if c then m else n) := by
  split <;> assumption

private theorem sailE_run {α : Type} {m : SailME α α} (hm : SailETracks m) :
    SailTracks (SailME.run m) := by
  unfold SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  refine sail_bind hm fun result => ?_
  cases result with
  | ok _ => exact sail_pure _
  | error e =>
    cases e with
    | inl e => exact tracks_throw e
    | inr _ => exact sail_pure _

private theorem sail_next_pc (pc : BitVec 64) : SailTracks (set_next_pc pc) := by
  unfold set_next_pc
  exact sail_bind (sail_write _ _) fun _ => sail_pure _

private theorem sail_enabled : SailTracks (currentlyEnabled extension.Ext_Zca) := by
  simp only [currentlyEnabled]
  refine sail_and (sail_pure _) ?_
  refine sail_bind ?_ fun _ => sail_pure _
  exact sail_and (sail_pure _) (sail_bind (sail_read _) fun _ => sail_pure _)

private theorem sail_jump (pc : BitVec 64) : SailTracks (jump_to pc) := by
  unfold jump_to ext_control_check_pc
  apply sailE_run
  refine sailE_bind (sailE_lift (sail_assert _ _)) fun _ => ?_
  refine sailE_bind ?_ fun _ => ?_
  · refine sailE_and (sailE_pure _) ?_
    exact sailE_bind (sailE_lift sail_enabled) fun _ => sailE_pure _
  · exact sailE_ite (sailE_pure _)
      (sailE_bind (sailE_lift (sail_next_pc _)) fun _ => sailE_pure _)

private theorem tracks_readHostBytes
    (loadByte : BitVec 64 → JoltMonad (Result (BitVec 8) ExecutionResult))
    (hload : ∀ a, Tracks (loadByte a)) (overflowChecks incrementAfterLast : Bool)
    {width : Nat} (pointer : BitVec width) (count : Nat) (bytes : Array (BitVec 8)) :
    Tracks (readHostBytes loadByte overflowChecks incrementAfterLast pointer count bytes) := by
  induction count generalizing pointer bytes with
  | zero => exact tracks_pure _
  | succ count ih =>
    unfold readHostBytes
    refine tracks_bind (hload _) fun result => ?_
    cases result with
    | Err _ => exact tracks_pure _
    | Ok _ =>
      dsimp only
      exact tracks_ite (tracks_bind (tracks_throw _) fun _ => ih _ _) (ih _ _)

private theorem tracks_tape_modify (f : JoltAdviceTape → JoltAdviceTape) :
    Tracks (modify fun s : SailJoltState => { s with adviceTape := f s.adviceTape }) := by
  apply tracks_modify
  · intro s g h
    exact { h with tape := congrArg f h.tape }
  · intro _; rfl

local macro "jolt_tracks" : tactic =>
  `(tactic| repeat' (first
    | exact tracks_readSrc _
    | exact tracks_writeDst _ _
    | exact tracks_pure _
    | exact tracks_throw _
    | exact tracks_tape_modify _
    | apply tracks_ite
    | refine tracks_bind ?_ (fun _ => ?_)
    | exact sail_jump _
    | exact sail_next_pc _
    | exact sail_read _
    | exact sail_write _ _
    | exact tracks_load _
    | exact tracks_load_doubleword _
    | exact tracks_store_doubleword _ _
    | split))

private theorem tracks_hostIO : Tracks execHostIO := by
  unfold execHostIO execHostIOWith
  refine tracks_get_bind (fun _ _ h => by rw [h.host]) fun _ => ?_
  jolt_tracks
  all_goals first
    | exact tracks_readHostBytes _ tracks_load _ _ _ _ _
    | exact tracks_tape_modify (fun tape => { tape with bytes := tape.bytes ++ _ })

private theorem tracks_adviceLoad (rd : Dst) (n : BitVec 64) :
    Tracks (execInstr (.VirtualAdviceLoad rd n)) := by
  intro s g h
  simp only [execInstr, h.tape]
  cases readAdviceTape s.adviceTape n with
  | none => exact .error _ ⟨h, .refl _, .refl _⟩
  | some pair =>
    obtain ⟨value, tape⟩ := pair
    have he := tracks_bind (tracks_writeDst rd value) (fun _ => tracks_pure RETIRE_SUCCESS)
      { s with adviceTape := tape } { g with adviceTape := tape } { h with tape := rfl }
    exact he.mono fun _ _ ha =>
      ⟨ha.1, ⟨ha.2.1.present, ha.2.1.below⟩, ⟨ha.2.2.present, ha.2.2.below⟩⟩

/-- One Jolt row gives the same value or error on a shadow, preserves the
shadow relation, never removes a byte and never changes Sail memory below RAM.
For example, an SD row inserts the same eight RAM bytes on both sides. -/
theorem execInstr_shadow (i : Instr) (s g : SailJoltState) (h : Shadow s g) :
    SameResult (fun s' g' => Shadow s' g' ∧ MemoryFrame s s' ∧ MemoryFrame g g')
      (execInstr i s) (execInstr i g) := by
  suffices ht : Tracks (execInstr i) from ht s g h
  cases i
  case VirtualAdviceLoad rd n => exact tracks_adviceLoad rd n
  case VirtualHostIO => exact tracks_hostIO
  all_goals simp only [execInstr]
  all_goals jolt_tracks

/-- A whole Jolt program preserves shadows, including a program that stops
with an error or exception, and preserves memory presence and memory below RAM.
For example, the two sides of an honest division expansion request equal advice. -/
theorem execProgram_shadow (p : Program) (s g : SailJoltState) (h : Shadow s g) :
    SameResult (fun s' g' => Shadow s' g' ∧ MemoryFrame s s' ∧ MemoryFrame g g')
      (execProgram p s) (execProgram p g) := by
  suffices ht : Tracks (execProgram p) from ht s g h
  induction p with
  | done r => exact tracks_pure r
  | instr i rest ih =>
    unfold execProgram
    refine tracks_bind (execInstr_shadow i) fun r => ?_
    cases r with
    | Retire_Success u => cases u; exact ih
    | _ => exact tracks_pure _

end WholeRun
