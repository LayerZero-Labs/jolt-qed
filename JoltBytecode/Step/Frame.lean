import JoltBytecode.Step.Lift
import JoltBytecode.JoltISA.Semantics

/-!
# Register frames for Jolt rows

A row may overwrite an integer register or `nextPC`, but cannot remove a
register from the embedded Sail register map.
For example, an ADD row preserves `PC`, `misa` and every interrupt CSR even
when an operand read fails.
The proofs compose primitive effects, including error states, rather than
requiring a well-formed initial state.
-/

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

noncomputable section

namespace Step

variable {ε σ α β : Type}

/-- The Sail registers a Jolt row may write: the general-purpose registers
x1..x31 and `nextPC`.
For example, `x10` is writable, whereas `PC` and `misa` are not. -/
def JoltWritable (r : Register) : Prop :=
  match r with
  | .x1 | .x2 | .x3 | .x4 | .x5 | .x6 | .x7 | .x8
  | .x9 | .x10 | .x11 | .x12 | .x13 | .x14 | .x15 | .x16
  | .x17 | .x18 | .x19 | .x20 | .x21 | .x22 | .x23 | .x24
  | .x25 | .x26 | .x27 | .x28 | .x29 | .x30 | .x31 | .nextPC => True
  | _ => False

/-- How a Jolt computation may change the embedded Sail registers: every
register outside `JoltWritable` keeps its value, and every register present
before is still present after.
For example, a write to `x10` preserves the value and presence of `misa`. -/
structure RegFrame (js js' : SailJoltState) : Prop where
  keep : ∀ r, ¬ JoltWritable r → js'.sail.regs.get? r = js.sail.regs.get? r
  present : ∀ r, (js.sail.regs.get? r).isSome → (js'.sail.regs.get? r).isSome

/-- The final state of a result, success or error.
For example, `resultState (.error e js)` is `js`. -/
def resultState : EStateM.Result ε σ α → σ
  | .ok _ s => s
  | .error _ s => s

/-- Leaving a state unchanged preserves all its registers, including a missing
register: for example, an absent `misa` remains absent. -/
theorem RegFrame.refl (js : SailJoltState) : RegFrame js js :=
  ⟨fun _ _ => rfl, fun _ h => h⟩

/-- Two register frames compose: for example, writing `x1` then `nextPC`
still preserves every register outside `JoltWritable`. -/
theorem RegFrame.trans {a b c : SailJoltState} (hab : RegFrame a b)
    (hbc : RegFrame b c) : RegFrame a c :=
  ⟨fun r h => (hbc.keep r h).trans (hab.keep r h),
    fun r h => hbc.present r (hab.present r h)⟩

private theorem frame_of_regs_eq {a b : SailJoltState}
    (h : b.sail.regs = a.sail.regs) : RegFrame a b := by
  constructor
  · intro r _; rw [h]
  · intro r hr; rwa [h]

/-- A computation frames registers on every input, including its error result.
For example, `pure ()` frames registers because its state does not change. -/
def Frames (m : JoltMonad α) : Prop := ∀ js, RegFrame js (resultState (m js))

private theorem frames_pure (a : α) : Frames (pure a) := RegFrame.refl

private theorem frames_bind {m : JoltMonad α} {f : α → JoltMonad β}
    (hm : Frames m) (hf : ∀ a, Frames (f a)) : Frames (m >>= f) := by
  intro js
  have h := hm js
  change RegFrame js (resultState (EStateM.bind m f js))
  cases hms : m js with
  | ok a js' =>
    simp only [hms, resultState] at h
    simpa only [EStateM.bind, hms] using h.trans (hf a js')
  | error e js' =>
    simpa only [EStateM.bind, hms, resultState] using h

private theorem frames_ite {c : Prop} [Decidable c] {m n : JoltMonad α}
    (hm : Frames m) (hn : Frames n) : Frames (if c then m else n) := by
  split <;> assumption

private theorem frames_throw (e : Error exception) : Frames (throw e : JoltMonad α) :=
  RegFrame.refl

private theorem frames_get : Frames (get : JoltMonad SailJoltState) := RegFrame.refl

private theorem frames_modify (f : SailJoltState → SailJoltState)
    (hf : ∀ js, (f js).sail.regs = js.sail.regs) : Frames (modify f) := by
  intro js
  exact frame_of_regs_eq (hf js)

private def SailFrames (m : SailM α) : Prop := Frames (liftSail m)

private theorem sailFrames_pure (a : α) : SailFrames (pure a) := frames_pure a

private theorem sailFrames_bind {m : SailM α} {f : α → SailM β}
    (hm : SailFrames m) (hf : ∀ a, SailFrames (f a)) : SailFrames (m >>= f) := by
  unfold SailFrames
  rw [Projection.liftSail_bind]
  exact frames_bind hm hf

private theorem sailFrames_ite {c : Prop} [Decidable c] {m n : SailM α}
    (hm : SailFrames m) (hn : SailFrames n) : SailFrames (if c then m else n) := by
  split <;> assumption

private theorem sailFrames_readReg (r : Register) :
    SailFrames (LeanRV64D.readReg r : SailM (RegisterType r)) := by
  intro js
  unfold liftSail
  cases h : js.sail.regs.get? r with
  | none => rw [readReg_eq_of_get?_none r _ h]; exact RegFrame.refl js
  | some v => rw [readReg_eq_of_get? r _ v h]; exact RegFrame.refl js

private theorem sailFrames_writeReg (r : Register) (v : RegisterType r)
    (hr : JoltWritable r) : SailFrames (LeanRV64D.writeReg r v : SailM Unit) := by
  intro js
  change RegFrame js { js with sail := setReg js.sail r v }
  constructor
  · intro r' h'
    exact setReg_get?_ne _ _ (fun h => h' (h ▸ hr))
  · intro r' h'
    by_cases h : r = r'
    · subst r'; simp [setReg]
    · simpa only [setReg_get?_ne _ _ h] using h'

private theorem sailFrames_assert (b : Bool) (msg : String) :
    SailFrames (LeanRV64D.sail_assert b msg) := by
  intro js
  cases b <;> exact RegFrame.refl js

private theorem sailFrames_andM {m n : SailM Bool}
    (hm : SailFrames m) (hn : SailFrames n) : SailFrames (m <&&> n) := by
  unfold _root_.andM
  refine sailFrames_bind hm fun b => ?_
  cases b
  · exact sailFrames_pure _
  · exact hn

private theorem sailFrames_throw (e : Error exception) :
    SailFrames (throw e : SailM α) := by
  intro js
  exact RegFrame.refl js

private theorem sailFrames_map (f : α → β) {m : SailM α}
    (hm : SailFrames m) : SailFrames (f <$> m) := by
  have h : f <$> m = m >>= fun a => pure (f a) := by
    funext s
    cases m s <;> rfl
  rw [h]
  exact sailFrames_bind hm fun _ => sailFrames_pure _

private theorem sailFrames_set_next_pc (pc : BitVec 64) : SailFrames (set_next_pc pc) := by
  unfold set_next_pc
  exact sailFrames_bind (sailFrames_writeReg _ _ True.intro) fun _ => sailFrames_pure _

private theorem sailFrames_enabled : SailFrames (currentlyEnabled extension.Ext_Zca) := by
  simp only [currentlyEnabled]
  refine sailFrames_andM (sailFrames_pure _) ?_
  refine sailFrames_bind ?_ fun _ => sailFrames_pure _
  exact sailFrames_andM (sailFrames_pure _)
    (sailFrames_bind (sailFrames_readReg _) fun _ => sailFrames_pure _)

local macro "sail_frame" : tactic =>
  `(tactic| repeat' (first
    | exact sailFrames_readReg _
    | exact sailFrames_writeReg _ _ (by trivial)
    | exact sailFrames_assert _ _
    | exact sailFrames_pure _
    | apply sailFrames_andM
    | apply sailFrames_ite
    | apply sailFrames_bind
    | split
    | intro _))

private theorem sailFrames_rX (r : regidx) : SailFrames (rX_bits r) := by
  unfold rX_bits rX
  sail_frame

private theorem sailFrames_wX (r : regidx) (v : BitVec 64) :
    SailFrames (wX_bits r v) := by
  unfold wX_bits wX xreg_write_callback
  sail_frame

private theorem frames_readSrc (src : JoltISA.Src) : Frames (JoltISA.readSrc src) := by
  cases src with
  | xreg r => exact sailFrames_rX r
  | vreg r =>
    unfold JoltISA.readSrc readVReg
    exact frames_bind frames_get fun _ => frames_pure _

private theorem frames_writeDst (dst : JoltISA.Dst) (v : BitVec 64) :
    Frames (JoltISA.writeDst dst v) := by
  cases dst with
  | xreg r => exact sailFrames_wX r v
  | vreg r =>
    unfold JoltISA.writeDst writeVReg
    exact frames_ite (frames_throw _) (frames_modify _ fun _ => rfl)

private def SailEFrames (m : SailME ε α) : Prop := SailFrames (ExceptT.run m)

private theorem sailEFrames_pure (a : α) : SailEFrames (pure a : SailME ε α) :=
  sailFrames_pure (Except.ok (ε := Error exception ⊕ ε) a)

private theorem sailEFrames_bind {m : SailME ε α} {f : α → SailME ε β}
    (hm : SailEFrames m) (hf : ∀ a, SailEFrames (f a)) : SailEFrames (m >>= f) := by
  change SailFrames (ExceptT.run m >>= ExceptT.bindCont f)
  refine sailFrames_bind hm fun result => ?_
  cases result with
  | error e => exact sailFrames_pure _
  | ok a => exact hf a

private theorem sailEFrames_lift {m : SailM α} (hm : SailFrames m) :
    SailEFrames (liftM m : SailME ε α) := sailFrames_map Except.ok hm

private theorem sailEFrames_andM {m n : SailME ε Bool}
    (hm : SailEFrames m) (hn : SailEFrames n) : SailEFrames (m <&&> n) := by
  unfold _root_.andM
  refine sailEFrames_bind hm fun b => ?_
  cases b
  · exact sailEFrames_pure _
  · exact hn

private theorem sailEFrames_ite {c : Prop} [Decidable c] {m n : SailME ε α}
    (hm : SailEFrames m) (hn : SailEFrames n) : SailEFrames (if c then m else n) := by
  split <;> assumption

private theorem sailEFrames_run {m : SailME α α} (hm : SailEFrames m) :
    SailFrames (SailME.run m) := by
  unfold SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  refine sailFrames_bind hm fun result => ?_
  cases result with
  | ok a => exact sailFrames_pure _
  | error e =>
    cases e with
    | inl e => exact sailFrames_throw e
    | inr a => exact sailFrames_pure _

private theorem sailFrames_jump_to (target : BitVec 64) : SailFrames (jump_to target) := by
  unfold jump_to ext_control_check_pc
  apply sailEFrames_run
  refine sailEFrames_bind (sailEFrames_lift (sailFrames_assert _ _)) fun _ => ?_
  refine sailEFrames_bind ?_ fun b => ?_
  · refine sailEFrames_andM (sailEFrames_pure _) ?_
    exact sailEFrames_bind (sailEFrames_lift sailFrames_enabled) fun _ => sailEFrames_pure _
  · exact sailEFrames_ite (sailEFrames_pure _)
      (sailEFrames_bind (sailEFrames_lift (sailFrames_set_next_pc _)) fun _ => sailEFrames_pure _)

private theorem frames_load (address : BitVec 64) : Frames (JoltISA.Mmu.load address) := by
  intro js
  unfold JoltISA.Mmu.load
  split <;> exact RegFrame.refl js

private theorem frames_load_doubleword (address : BitVec 64) :
    Frames (JoltISA.Mmu.load_doubleword address) := by
  intro js
  unfold JoltISA.Mmu.load_doubleword
  dsimp only
  repeat' first | exact RegFrame.refl js | split

private theorem store_raw_regs (js : SailJoltState) (address : Nat) (v : BitVec 8)
    (js' : SailJoltState) (h : JoltISA.Mmu.store_raw? js address v = some js') :
    js'.sail.regs = js.sail.regs := by
  unfold JoltISA.Mmu.store_raw? at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · obtain ⟨device, _, h⟩ := Option.map_eq_some_iff.mp h
        cases h
        rfl

private theorem store_bytes_regs (js : SailJoltState) (address : Nat) (v : BitVec 64)
    (ks : List Nat) (current : Option SailJoltState)
    (hc : ∀ s, current = some s → s.sail.regs = js.sail.regs) :
    ∀ s, ks.foldl (fun state k => state.bind fun s =>
      JoltISA.Mmu.store_raw? s (address + k) (v.extractLsb' (8 * k) 8)) current = some s →
      s.sail.regs = js.sail.regs := by
  induction ks generalizing current with
  | nil => exact hc
  | cons k ks ih =>
    apply ih
    intro next hnext
    cases hcur : current with
    | none => simp [hcur] at hnext
    | some before =>
      simp only [hcur, Option.bind_some] at hnext
      exact (store_raw_regs before _ _ next hnext).trans (hc before hcur)

private theorem frames_store_doubleword (address v : BitVec 64) :
    Frames (JoltISA.Mmu.store_doubleword address v) := by
  intro js
  unfold JoltISA.Mmu.store_doubleword
  dsimp only
  split
  · exact RegFrame.refl js
  · split
    · split <;> exact frame_of_regs_eq rfl
    · split
      · rename_i js' h
        exact frame_of_regs_eq (store_bytes_regs js _ v (List.range 8) (some js)
          (fun s hs => by cases hs; rfl) js' h)
      · exact RegFrame.refl js

private theorem frames_hostLoad (address : BitVec 64) :
    Frames (JoltISA.Mmu.hostLoad address) :=
  fun js => RegFrame.refl js

private theorem frames_readHostBytes
    (loadByte : BitVec 64 → JoltMonad (Option (BitVec 8)))
    (hload : ∀ address, Frames (loadByte address)) {width : Nat}
    (pointer : BitVec width) (count : Nat) (bytes : Array (BitVec 8)) :
    Frames (JoltISA.readHostBytes loadByte pointer count bytes) := by
  induction count generalizing pointer bytes with
  | zero => exact frames_pure _
  | succ count ih =>
    unfold JoltISA.readHostBytes
    refine frames_bind (hload _) fun result => ?_
    cases result with
    | none => exact frames_pure _
    | some byte => exact ih _ _

local macro "jolt_frame" : tactic =>
  `(tactic| repeat' (first
    | exact frames_readSrc _
    | exact frames_writeDst _ _
    | exact frames_pure _
    | exact frames_throw _
    | exact frames_get
    | exact frames_modify _ (fun _ => rfl)
    | apply frames_ite
    | refine frames_bind ?_ (fun _ => ?_)
    | exact sailFrames_jump_to _
    | exact sailFrames_set_next_pc _
    | exact sailFrames_readReg _
    | exact sailFrames_writeReg _ _ (by trivial)
    | exact frames_load _
    | exact frames_load_doubleword _
    | exact frames_store_doubleword _ _
    | split))

private theorem frames_hostIO : Frames JoltISA.execHostIO := by
  unfold JoltISA.execHostIO JoltISA.execHostIOWith JoltISA.readHostRange
  jolt_frame
  all_goals exact frames_readHostBytes _ frames_hostLoad _ _ _

/-- A single Jolt row preserves every Sail register outside `JoltWritable`
and never removes a present register, on success or error.
For example, `JAL` can update `nextPC` and its destination but preserves `PC`. -/
theorem execInstr_regFrame (i : JoltISA.Instr) (js : SailJoltState) :
    RegFrame js (resultState (JoltISA.execInstr i js)) := by
  suffices h : Frames (JoltISA.execInstr i) from h js
  cases i
  case VirtualAdviceLoad rd num_bytes =>
    intro cpu
    simp only [JoltISA.execInstr]
    split
    · exact RegFrame.refl cpu
    · rename_i value tape h
      exact (frame_of_regs_eq (a := cpu) (b := { cpu with adviceTape := tape }) rfl).trans
        (frames_bind (frames_writeDst rd value) (fun _ => frames_pure _) _)
  case VirtualHostIO => exact frames_hostIO
  all_goals simp only [JoltISA.execInstr]
  all_goals jolt_frame

/-- Running a Jolt program preserves every Sail register outside
`JoltWritable` and never removes a present register, even if execution stops
with an error or an architectural exception.
For example, two ADD rows still preserve the initial `misa` value. -/
theorem execProgram_regFrame (p : JoltISA.Program) (js : SailJoltState) :
    RegFrame js (resultState (JoltISA.execProgram p js)) := by
  suffices h : Frames (JoltISA.execProgram p) from h js
  induction p with
  | done result => exact frames_pure result
  | instr i rest ih =>
    unfold JoltISA.execProgram
    refine frames_bind (execInstr_regFrame i) fun result => ?_
    cases result with
    | Retire_Success u => cases u; exact ih
    | _ => exact frames_pure _

end Step
