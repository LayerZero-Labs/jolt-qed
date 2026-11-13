import JoltConstraints.WholeRun.Basic

/-!
Jolt rows ignore the embedded Sail copies of the registers in `Untouched`.
These include the CSRs and reservation represented by Jolt virtual registers,
and Sail's instruction-retirement bookkeeping.
For example, replacing embedded `mstatus` commutes with an ADD row, including
when an operand is missing and the row returns an error.

`misa` is not in `Untouched`: the branch rows call Sail's `jump_to`, which reads
its C bit. Replacing embedded `misa` by a value with the C bit set still commutes
with every row that succeeds, and so with every successful block
(`execProgram_withMisa`); only the failure of a taken branch to a 2-aligned target
can differ, when the embedded C bit is clear.
-/

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

variable {α β ε : Type} {r : Register} {v : RegisterType r}

/-- The registers whose embedded copy every Jolt row ignores except through
Sail's `jump_to`: the `Untouched` registers, and `misa`, which `jump_to` reads
for its C bit. -/
private def Inert (r : Register) : Prop := Untouched r ∨ r = Register.misa

private theorem mapState_ite {σ τ : Type} (f : σ → τ) {c : Prop} [Decidable c]
    (a b : EStateM.Result ε σ α) :
    mapState f (if c then a else b) = if c then mapState f a else mapState f b := by
  split <;> rfl

/-- A computation commutes with replacing register `r` by `v`, on both success
and error results; for example, a constant computation has this property. -/
private def Commutes (r : Register) (v : RegisterType r) (m : JoltMonad α) : Prop :=
  ∀ js, m (withReg js r v) = mapState (withReg · r v) (m js)

private theorem commutes_pure (a : α) : Commutes r v (pure a) := fun _ => rfl

private theorem commutes_bind {m : JoltMonad α} {f : α → JoltMonad β}
    (hm : Commutes r v m) (hf : ∀ a, Commutes r v (f a)) :
    Commutes r v (m >>= f) := by
  intro js
  change EStateM.bind m f (withReg js r v) =
    mapState (withReg · r v) (EStateM.bind m f js)
  simp only [EStateM.bind, hm js]
  cases m js with
  | ok a js' => exact hf a js'
  | error e js' => rfl

private theorem commutes_ite {c : Prop} [Decidable c] {m n : JoltMonad α}
    (hm : Commutes r v m) (hn : Commutes r v n) :
    Commutes r v (if c then m else n) := by
  split <;> assumption

private theorem commutes_throw (e : Error exception) :
    Commutes r v (throw e : JoltMonad α) := fun _ => rfl

private theorem commutes_modify (f : SailJoltState → SailJoltState)
    (hf : ∀ js, f (withReg js r v) = withReg (f js) r v) :
    Commutes r v (modify f) := by
  intro js
  change EStateM.Result.ok () (f (withReg js r v)) = _
  rw [hf js]
  rfl

private theorem commutes_get_bind {f : SailJoltState → JoltMonad α}
    (hf : ∀ js, f (withReg js r v) = f js)
    (hc : ∀ js, Commutes r v (f js)) : Commutes r v (get >>= f) := by
  intro js
  change f (withReg js r v) (withReg js r v) = _
  rw [hf js]
  exact hc js js

/-- The same commutation property for Sail code lifted into the Jolt state;
for example, reading `PC` commutes with replacing embedded `mstatus`. -/
private def SailCommutes (r : Register) (v : RegisterType r) (m : SailM α) : Prop :=
  Commutes r v (liftSail m)

private theorem sailCommutes_pure (a : α) : SailCommutes r v (pure a) :=
  commutes_pure a

private theorem sailCommutes_bind {m : SailM α} {f : α → SailM β}
    (hm : SailCommutes r v m) (hf : ∀ a, SailCommutes r v (f a)) :
    SailCommutes r v (m >>= f) := by
  unfold SailCommutes
  rw [Projection.liftSail_bind]
  exact commutes_bind hm hf

private theorem sailCommutes_ite {c : Prop} [Decidable c] {m n : SailM α}
    (hm : SailCommutes r v m) (hn : SailCommutes r v n) :
    SailCommutes r v (if c then m else n) := by
  split <;> assumption

private theorem sailCommutes_readReg (q : Register) (hq : q ≠ r) :
    SailCommutes r v (LeanRV64D.readReg q : SailM (RegisterType q)) := by
  intro js
  have hg := Step.setReg_get?_ne js.sail v hq.symm
  unfold liftSail withReg
  cases h : js.sail.regs.get? q with
  | none =>
    rw [Step.readReg_eq_of_get?_none q _ h,
      Step.readReg_eq_of_get?_none q _ (hg.trans h)]
    rfl
  | some w =>
    rw [readReg_eq_of_get? q _ w h, readReg_eq_of_get? q _ w (hg.trans h)]
    rfl

private theorem sailCommutes_writeReg (q : Register) (w : RegisterType q) (hq : q ≠ r) :
    SailCommutes r v (LeanRV64D.writeReg q w : SailM Unit) := by
  intro js
  change EStateM.Result.ok () (withReg (withReg js r v) q w) =
    EStateM.Result.ok () (withReg (withReg js q w) r v)
  unfold withReg Step.setReg
  rw [System.extDHashMap_insert_comm_of_ne _ v w hq.symm]

private theorem sailCommutes_assert (b : Bool) (msg : String) :
    SailCommutes r v (LeanRV64D.sail_assert b msg) := by
  intro js
  cases b <;> rfl

private theorem sailCommutes_andM {m n : SailM Bool}
    (hm : SailCommutes r v m) (hn : SailCommutes r v n) :
    SailCommutes r v (m <&&> n) := by
  unfold _root_.andM
  refine sailCommutes_bind hm fun b => ?_
  cases b
  · exact sailCommutes_pure _
  · exact hn

private theorem sailCommutes_throw (e : Error exception) :
    SailCommutes r v (throw e : SailM α) := fun _ => rfl

private theorem sailCommutes_map (f : α → β) {m : SailM α}
    (hm : SailCommutes r v m) : SailCommutes r v (f <$> m) := by
  have h : f <$> m = m >>= fun a => pure (f a) := by
    funext s
    cases m s <;> rfl
  rw [h]
  exact sailCommutes_bind hm fun _ => sailCommutes_pure _

local macro "untouched_ne" : tactic =>
  `(tactic| (intro h; cases h; assumption))

local macro "inert_ne" : tactic =>
  `(tactic| (intro h; cases h; rcases ‹Inert _› with hr | hr <;> first | exact hr | cases hr))

private theorem sailCommutes_set_next_pc (hr : Inert r) (pc : BitVec 64) :
    SailCommutes r v (set_next_pc pc) := by
  unfold set_next_pc
  exact sailCommutes_bind (sailCommutes_writeReg _ _ (by inert_ne))
    fun _ => sailCommutes_pure _

private theorem sailCommutes_enabled (hr : Untouched r) :
    SailCommutes r v (currentlyEnabled extension.Ext_Zca) := by
  simp only [currentlyEnabled]
  refine sailCommutes_andM (sailCommutes_pure _) ?_
  refine sailCommutes_bind ?_ fun _ => sailCommutes_pure _
  exact sailCommutes_andM (sailCommutes_pure _)
    (sailCommutes_bind (sailCommutes_readReg _ (by untouched_ne))
      fun _ => sailCommutes_pure _)

local macro "sail_commutes" : tactic =>
  `(tactic| repeat' (first
    | exact sailCommutes_readReg _ (by inert_ne)
    | exact sailCommutes_writeReg _ _ (by inert_ne)
    | exact sailCommutes_assert _ _
    | exact sailCommutes_pure _
    | apply sailCommutes_andM
    | apply sailCommutes_ite
    | apply sailCommutes_bind
    | split
    | intro _))

private theorem sailCommutes_rX (hr : Inert r) (q : regidx) :
    SailCommutes r v (rX_bits q) := by
  unfold rX_bits rX
  sail_commutes

private theorem sailCommutes_wX (hr : Inert r) (q : regidx) (w : BitVec 64) :
    SailCommutes r v (wX_bits q w) := by
  unfold wX_bits wX xreg_write_callback
  sail_commutes

private theorem commutes_readSrc (hr : Inert r) (src : JoltISA.Src) :
    Commutes r v (JoltISA.readSrc src) := by
  cases src with
  | xreg q => exact sailCommutes_rX hr q
  | vreg q => intro js; rfl

private theorem commutes_writeDst (hr : Inert r) (dst : JoltISA.Dst) (w : BitVec 64) :
    Commutes r v (JoltISA.writeDst dst w) := by
  cases dst with
  | xreg q => exact sailCommutes_wX hr q w
  | vreg q =>
    unfold JoltISA.writeDst writeVReg
    exact commutes_ite (commutes_throw _) (commutes_modify _ fun _ => rfl)

/-- Commutation for Sail's exception transformer, whose ordinary and early
return values both carry the same final state; for example, `jump_to` uses it. -/
private def SailECommutes (r : Register) (v : RegisterType r) (m : SailME ε α) : Prop :=
  SailCommutes r v (ExceptT.run m)

private theorem sailECommutes_pure (a : α) : SailECommutes r v (pure a : SailME ε α) :=
  sailCommutes_pure (Except.ok (ε := Error exception ⊕ ε) a)

private theorem sailECommutes_bind {m : SailME ε α} {f : α → SailME ε β}
    (hm : SailECommutes r v m) (hf : ∀ a, SailECommutes r v (f a)) :
    SailECommutes r v (m >>= f) := by
  change SailCommutes r v (ExceptT.run m >>= ExceptT.bindCont f)
  refine sailCommutes_bind hm fun result => ?_
  cases result with
  | error e => exact sailCommutes_pure _
  | ok a => exact hf a

private theorem sailECommutes_lift {m : SailM α} (hm : SailCommutes r v m) :
    SailECommutes r v (liftM m : SailME ε α) := sailCommutes_map Except.ok hm

private theorem sailECommutes_andM {m n : SailME ε Bool}
    (hm : SailECommutes r v m) (hn : SailECommutes r v n) :
    SailECommutes r v (m <&&> n) := by
  unfold _root_.andM
  refine sailECommutes_bind hm fun b => ?_
  cases b
  · exact sailECommutes_pure _
  · exact hn

private theorem sailECommutes_ite {c : Prop} [Decidable c] {m n : SailME ε α}
    (hm : SailECommutes r v m) (hn : SailECommutes r v n) :
    SailECommutes r v (if c then m else n) := by
  split <;> assumption

private theorem sailECommutes_run {m : SailME α α} (hm : SailECommutes r v m) :
    SailCommutes r v (SailME.run m) := by
  unfold SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  refine sailCommutes_bind hm fun result => ?_
  cases result with
  | ok a => exact sailCommutes_pure _
  | error e =>
    cases e with
    | inl e => exact sailCommutes_throw e
    | inr a => exact sailCommutes_pure _

private theorem sailCommutes_jump_to (hr : Untouched r) (target : BitVec 64) :
    SailCommutes r v (jump_to target) := by
  unfold jump_to ext_control_check_pc
  apply sailECommutes_run
  refine sailECommutes_bind (sailECommutes_lift (sailCommutes_assert _ _)) fun _ => ?_
  refine sailECommutes_bind ?_ fun b => ?_
  · refine sailECommutes_andM (sailECommutes_pure _) ?_
    exact sailECommutes_bind (sailECommutes_lift (sailCommutes_enabled hr))
      fun _ => sailECommutes_pure _
  · exact sailECommutes_ite (sailECommutes_pure _)
      (sailECommutes_bind (sailECommutes_lift (sailCommutes_set_next_pc (Or.inl hr) _))
        fun _ => sailECommutes_pure _)

private theorem commutes_load (address : BitVec 64) :
    Commutes r v (JoltISA.Mmu.load address) := by
  intro js
  have h : JoltISA.Mmu.load? (withReg js r v) address.toNat =
      JoltISA.Mmu.load? js address.toNat := rfl
  unfold JoltISA.Mmu.load
  rw [h]
  cases JoltISA.Mmu.load? js address.toNat <;> rfl

private theorem commutes_load_doubleword (address : BitVec 64) :
    Commutes r v (JoltISA.Mmu.load_doubleword address) := by
  intro js
  have hraw : JoltISA.Mmu.load_raw? (withReg js r v) = JoltISA.Mmu.load_raw? js := rfl
  unfold JoltISA.Mmu.load_doubleword
  dsimp only
  rw [hraw]
  cases JoltISA.read_doubleword? (JoltISA.Mmu.load_raw? js) address.toNat <;>
    simp only [mapState_ite] <;> rfl

private theorem store_raw_withReg (js : SailJoltState) (address : Nat) (w : BitVec 8) :
    JoltISA.Mmu.store_raw? (withReg js r v) address w =
      (JoltISA.Mmu.store_raw? js address w).map (withReg · r v) := by
  unfold JoltISA.Mmu.store_raw? withReg Step.setReg
  dsimp only
  repeat' first | rfl | split
  cases js.jolt_device.store? address w <;> rfl

private theorem store_bytes_withReg (address : Nat) (w : BitVec 64)
    (ks : List Nat) (current : Option SailJoltState) :
    ks.foldl (fun state k => state.bind fun s =>
      JoltISA.Mmu.store_raw? s (address + k) (w.extractLsb' (8 * k) 8))
        (current.map (withReg · r v)) =
      (ks.foldl (fun state k => state.bind fun s =>
        JoltISA.Mmu.store_raw? s (address + k) (w.extractLsb' (8 * k) 8)) current).map
          (withReg · r v) := by
  induction ks generalizing current with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    cases current with
    | none => rfl
    | some js => exact store_raw_withReg js _ _

private theorem commutes_store_doubleword (address w : BitVec 64) :
    Commutes r v (JoltISA.Mmu.store_doubleword address w) := by
  intro js
  have h := store_bytes_withReg (r := r) (v := v) address.toNat w (List.range 8) (some js)
  simp only [Option.map_some] at h
  unfold JoltISA.Mmu.store_doubleword
  dsimp only
  rw [h]
  generalize hs : (List.range 8).foldl (fun state k => state.bind fun s =>
    JoltISA.Mmu.store_raw? s (address.toNat + k) (w.extractLsb' (8 * k) 8)) (some js) = stored
  cases stored <;> simp only [Option.map_none, Option.map_some, mapState_ite] <;> rfl

private theorem commutes_hostLoad (address : BitVec 64) :
    Commutes r v (JoltISA.Mmu.hostLoad address) := by
  intro js
  rfl

private theorem commutes_readHostBytes
    (loadByte : BitVec 64 → JoltMonad (Option (BitVec 8)))
    (hload : ∀ address, Commutes r v (loadByte address)) {width : Nat}
    (pointer : BitVec width) (count : Nat) (bytes : Array (BitVec 8)) :
    Commutes r v (JoltISA.readHostBytes loadByte pointer count bytes) := by
  induction count generalizing pointer bytes with
  | zero => exact commutes_pure _
  | succ count ih =>
    unfold JoltISA.readHostBytes
    refine commutes_bind (hload _) fun result => ?_
    cases result with
    | none => exact commutes_pure _
    | some byte => exact ih _ _

set_option hygiene false in
local macro "jolt_commutes" : tactic =>
  `(tactic| repeat' (first
    | exact commutes_readSrc (by assumption) _
    | exact commutes_writeDst (by assumption) _ _
    | exact commutes_pure _
    | exact commutes_throw _
    | exact commutes_modify _ (fun _ => rfl)
    | apply commutes_ite
    | refine commutes_bind ?_ (fun _ => ?_)
    | exact hjump rfl _
    | exact sailCommutes_set_next_pc (by assumption) _
    | exact sailCommutes_readReg _ (by inert_ne)
    | exact sailCommutes_writeReg _ _ (by inert_ne)
    | exact commutes_load _
    | exact commutes_load_doubleword _
    | exact commutes_store_doubleword _ _
    | split))

private theorem commutes_hostIO (hr : Inert r) : Commutes r v JoltISA.execHostIO := by
  unfold JoltISA.execHostIO JoltISA.execHostIOWith JoltISA.readHostRange
  have range : ∀ {width : Nat} (pointer : BitVec width) (count limit : Nat),
      Commutes r v (if pointer.toNat + count ≤ limit then
        JoltISA.readHostBytes JoltISA.Mmu.hostLoad pointer count #[] else pure none) :=
    fun _ _ _ => commutes_ite (commutes_readHostBytes _ commutes_hostLoad _ _ _) (commutes_pure _)
  refine commutes_bind (commutes_readSrc hr _) fun _ => ?_
  refine commutes_ite ?_ (commutes_ite ?_ (commutes_pure _))
  · refine commutes_bind (commutes_readSrc hr _) fun _ => ?_
    refine commutes_bind (commutes_readSrc hr _) fun _ => ?_
    refine commutes_bind (range _ _ _) fun result => ?_
    cases result with
    | none => exact commutes_pure _
    | some _ => exact commutes_bind (commutes_modify _ fun _ => rfl) fun _ => commutes_pure _
  · refine commutes_bind (commutes_readSrc hr _) fun _ => ?_
    refine commutes_bind (commutes_readSrc hr _) fun _ => ?_
    refine commutes_bind (commutes_readSrc hr _) fun _ => ?_
    refine commutes_get_bind (fun _ => rfl) fun _ => ?_
    exact commutes_ite (commutes_bind (range _ _ _) fun _ => commutes_pure _) (commutes_pure _)

private theorem commutes_adviceLoad (hr : Inert r) (rd : JoltISA.Dst)
    (num_bytes : BitVec 64) :
    Commutes r v (JoltISA.execInstr (.VirtualAdviceLoad rd num_bytes)) := by
  intro js
  have htape : (withReg js r v).adviceTape = js.adviceTape := rfl
  simp only [JoltISA.execInstr, htape]
  cases JoltISA.readAdviceTape js.adviceTape num_bytes with
  | none => rfl
  | some pair =>
    obtain ⟨value, tape⟩ := pair
    exact commutes_bind (commutes_writeDst hr rd value) (fun _ => commutes_pure _)
      { js with adviceTape := tape }

/-- The rows that call Sail's `jump_to`: the six branches. -/
private def usesJump : JoltISA.Instr → Bool
  | .BEQ _ _ _ | .BNE _ _ _ | .BLT _ _ _ | .BGE _ _ _ | .BLTU _ _ _ | .BGEU _ _ _ => true
  | _ => false

/-- One Jolt row commutes with replacing an `Inert` register, given that `jump_to`
does when the row calls it. -/
private theorem commutes_execInstr (i : JoltISA.Instr) (hr : Inert r)
    (hjump : usesJump i = true → ∀ t, SailCommutes r v (jump_to t)) :
    Commutes r v (JoltISA.execInstr i) := by
  cases i
  case VirtualAdviceLoad rd num_bytes => exact commutes_adviceLoad hr rd num_bytes
  case VirtualHostIO => exact commutes_hostIO hr
  all_goals simp only [JoltISA.execInstr]
  all_goals jolt_commutes

/-- Replacing an embedded Sail register in `Untouched` commutes with one Jolt
row, preserving its return value or error and replacing the same register in
its final state.
For example, an ADD row behaves identically after changing embedded `mstatus`,
even when its source register is absent. -/
theorem execInstr_withReg (i : JoltISA.Instr) (r : Register) (hr : Untouched r)
    (v : RegisterType r) (js : SailJoltState) :
    JoltISA.execInstr i (withReg js r v) = mapState (withReg · r v) (JoltISA.execInstr i js) :=
  commutes_execInstr i (Or.inl hr) (fun _ => sailCommutes_jump_to hr) js

/-- Replacing an embedded Sail register in `Untouched` commutes with running
a Jolt program, including an error or architectural exception that stops the
program before its remaining rows.
For example, changing embedded `minstret` before two ADD rows is the same as
changing it in the final state after running those rows. -/
theorem execProgram_withReg (p : JoltISA.Program) (r : Register) (hr : Untouched r)
    (v : RegisterType r) (js : SailJoltState) :
    JoltISA.execProgram p (withReg js r v) = mapState (withReg · r v) (JoltISA.execProgram p js) := by
  suffices h : Commutes r v (JoltISA.execProgram p) from h js
  induction p with
  | done result => exact commutes_pure result
  | instr i rest ih =>
    unfold JoltISA.execProgram
    refine commutes_bind (execInstr_withReg i r hr v) fun result => ?_
    cases result with
    | Retire_Success u => cases u; exact ih
    | _ => exact commutes_pure _

/-! ### `misa` and the branch rows

Of Sail's `jump_to`, only the test "bit 1 of the target is set and compressed
instructions are disabled" reads `misa`. A branch row that succeeds does not take
that exit, so it behaves the same under any `misa` whose C bit is set. -/

private theorem enabled_of_misa (s : SailState) (m : RegisterType Register.misa)
    (hm : s.regs.get? Register.misa = some m) :
    currentlyEnabled extension.Ext_Zca s = .ok (_get_Misa_C m == 1#1) s := by
  have hread := readReg_eq_of_get? Register.misa s m hm
  have hZca : hartSupports extension.Ext_Zca = true := by simp [hartSupports]
  unfold currentlyEnabled
  unfold currentlyEnabled
  simp [hZca, Step.hartSupports_C, Functions.not, andM, toBool, bind, EStateM.bind, pure, EStateM.pure, hread]

private theorem enabled_of_none (s : SailState) (hm : s.regs.get? Register.misa = none) :
    ∃ e, currentlyEnabled extension.Ext_Zca s = .error e s := by
  have hread := Step.readReg_eq_of_get?_none Register.misa s hm
  have hZca : hartSupports extension.Ext_Zca = true := by simp [hartSupports]
  unfold currentlyEnabled
  unfold currentlyEnabled
  simp [hZca, Step.hartSupports_C, andM, toBool, bind, EStateM.bind, pure, EStateM.pure, hread]

/-- `jump_to` on an aligned target, evaluated: the `misa` test, then `set_next_pc`. -/
private theorem jump_to_eval (t : BitVec 64) (s : SailState) (ht : BitVec.access t 0 = 0#1) :
    jump_to t s =
      if BitVec.access t 1 = 1#1 then
        (match currentlyEnabled extension.Ext_Zca s with
          | .ok b s2 => if b = true then ((fun _ => RETIRE_SUCCESS) <$> set_next_pc t) s2
              else .ok (ExecutionResult.Memory_Exception
                (virtaddr.Virtaddr t, ExceptionType.E_Fetch_Addr_Align ())) s2
          | .error e s2 => .error e s2)
      else ((fun _ => RETIRE_SUCCESS) <$> set_next_pc t) s := by
  unfold jump_to ext_control_check_pc
  simp [SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run]
  simp only [PreSail.sail_assert, pure, EStateM.pure, bind, EStateM.bind, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.run, andM, ExceptT.bind, ExceptT.mk,
    ExceptT.bindCont, ExceptT.map, ExceptT.pure, Functor.map, EStateM.map,
    Functions.not, bit_to_bool, toBool, bool_bit_backwards, ht]
  by_cases hb : BitVec.access t 1 = 1#1
  · simp only [hb, ite_true]
    rcases h : currentlyEnabled extension.Ext_Zca s with ⟨b, s2⟩ | ⟨e, s2⟩
    · cases b
      · simp [EStateM.bind, EStateM.map, EStateM.pure, h]
      · simp [EStateM.bind, EStateM.map, EStateM.pure, h]
        generalize set_next_pc t s2 = r
        cases r <;> rfl
    · simp [EStateM.bind, EStateM.map, EStateM.pure, h]
  · simp only [hb, ite_false]
    simp [EStateM.bind, EStateM.map, EStateM.pure]
    generalize set_next_pc t s = r
    cases r <;> rfl

/-- `jump_to` on a misaligned target asserts. -/
private theorem jump_to_odd (t : BitVec 64) (s : SailState) (ht : BitVec.access t 0 ≠ 0#1) :
    ∃ e s', jump_to t s = .error e s' := by
  have hb : (BitVec.access t 0 == 0#1) = false := by simpa using ht
  unfold jump_to ext_control_check_pc
  simp [SailME.run, Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run]
  simp only [PreSail.sail_assert, pure, bind, EStateM.bind, hb]
  exact ⟨_, _, rfl⟩

private theorem set_next_pc_run (t : BitVec 64) (s : SailState) :
    set_next_pc t s = .ok () (Step.setReg s Register.nextPC t) := rfl

private theorem map_success {m : SailM Unit} {s s' : SailState}
    (h : ((fun _ => RETIRE_SUCCESS) <$> m) s = .ok RETIRE_SUCCESS s') : m s = .ok () s' := by
  simp only [Functor.map, EStateM.map] at h
  cases hm : m s with
  | ok a s3 =>
    cases a
    simp only [hm] at h
    cases h
    rfl
  | error e s3 => simp [hm] at h

/-- A successful `jump_to` is an aligned `set_next_pc`, whatever `misa` says. -/
private theorem jump_to_success (t : BitVec 64) (s s' : SailState)
    (h : jump_to t s = .ok RETIRE_SUCCESS s') :
    BitVec.access t 0 = 0#1 ∧ s' = Step.setReg s Register.nextPC t := by
  by_cases ht : BitVec.access t 0 = 0#1
  · refine ⟨ht, ?_⟩
    rw [jump_to_eval t s ht] at h
    suffices hn : set_next_pc t s = .ok () s' by
      rw [set_next_pc_run] at hn
      exact (EStateM.Result.ok.inj hn).2.symm
    by_cases hb : BitVec.access t 1 = 1#1
    · simp only [hb, ite_true] at h
      rcases hm : s.regs.get? Register.misa with _ | m
      · obtain ⟨e, he⟩ := enabled_of_none s hm
        rw [he] at h
        cases h
      · rw [enabled_of_misa s m hm] at h
        by_cases hc : (_get_Misa_C m == 1#1) = true
        · simp only [hc, ite_true] at h
          exact map_success h
        · simp only [hc] at h
          cases h
    · simp only [hb, ite_false] at h
      exact map_success h
  · obtain ⟨e, s2, he⟩ := jump_to_odd t s ht
    rw [he] at h
    cases h

private theorem setReg_comm (s : SailState) (r q : Register) (hrq : r ≠ q)
    (a : RegisterType r) (b : RegisterType q) :
    Step.setReg (Step.setReg s r a) q b = Step.setReg (Step.setReg s q b) r a := by
  unfold Step.setReg
  rw [System.extDHashMap_insert_comm_of_ne _ a b hrq]

/-- A successful `jump_to` stays successful, with the same state change, when `misa`
is replaced by a value whose C bit is set. -/
private theorem jump_to_withMisa (v : RegisterType Register.misa) (hv : _get_Misa_C v = 1#1)
    (t : BitVec 64) (s s' : SailState) (h : jump_to t s = .ok RETIRE_SUCCESS s') :
    jump_to t (Step.setReg s Register.misa v) = .ok RETIRE_SUCCESS (Step.setReg s' Register.misa v) := by
  obtain ⟨ht, rfl⟩ := jump_to_success t s s' h
  have hm : (Step.setReg s Register.misa v).regs.get? Register.misa = some v :=
    Std.ExtDHashMap.get?_insert_self
  rw [jump_to_eval t _ ht, setReg_comm s _ _ (by decide)]
  have hen := enabled_of_misa _ v hm
  simp only [hv, beq_self_eq_true] at hen
  rw [hen]
  simp only [↓reduceIte, Functor.map, EStateM.map, set_next_pc_run]
  split <;> rfl

/-- A computation keeps a successful run, with the register replaced in the final
state, when the register is replaced before it. -/
private def KeepsSuccess (r : Register) (v : RegisterType r) (m : JoltMonad ExecutionResult) :
    Prop :=
  ∀ js t, m js = .ok RETIRE_SUCCESS t → m (withReg js r v) = .ok RETIRE_SUCCESS (withReg t r v)

private theorem keepsSuccess_of_commutes {m : JoltMonad ExecutionResult}
    (hm : Commutes r v m) : KeepsSuccess r v m := by
  intro js t h
  rw [hm js, h]
  rfl

private theorem keepsSuccess_bind {α : Type} {m : JoltMonad α} {f : α → JoltMonad ExecutionResult}
    (hm : Commutes r v m) (hf : ∀ a, KeepsSuccess r v (f a)) :
    KeepsSuccess r v (m >>= f) := by
  intro js t h
  change EStateM.bind m f js = _ at h
  change EStateM.bind m f (withReg js r v) = _
  rw [EStateM.bind, hm js]
  cases hmj : m js with
  | ok a js' =>
    simp only [EStateM.bind, hmj] at h
    exact hf a js' t h
  | error e js' => simp [EStateM.bind, hmj] at h

private theorem keepsSuccess_ite {c : Prop} [Decidable c] {m n : JoltMonad ExecutionResult}
    (hm : KeepsSuccess r v m) (hn : KeepsSuccess r v n) :
    KeepsSuccess r v (if c then m else n) := by
  split <;> assumption

/-- `jump_to` keeps a successful run when `misa` is replaced by a value whose C bit
is set. -/
private theorem keepsSuccess_jump_to (v : RegisterType Register.misa)
    (hv : _get_Misa_C v = 1#1) (t : BitVec 64) :
    KeepsSuccess Register.misa v (liftSail (jump_to t)) := by
  intro js t' h
  unfold liftSail at h ⊢
  cases hj : jump_to t js.sail with
  | ok a s' =>
    simp only [hj] at h
    cases h
    have := jump_to_withMisa v hv t js.sail s' hj
    simp only [withReg, this]
  | error e s' => simp [hj] at h

/-- A branch row keeps a successful run when `misa` is replaced by a value whose C
bit is set: the taken branch's `jump_to` is the only reader of `misa`. -/
private theorem keepsSuccess_branch (v : RegisterType Register.misa)
    (hv : _get_Misa_C v = 1#1) (lhs rhs : JoltISA.Src) (imm : BitVec 128)
    (decision : BitVec 64 → BitVec 64 → Bool) :
    KeepsSuccess Register.misa v (do
      let x ← JoltISA.readSrc lhs
      let y ← JoltISA.readSrc rhs
      if decision x y then
        let pc ← liftSail (LeanRV64D.readReg Register.PC)
        liftSail (jump_to (pc + imm.setWidth 64))
      else
        pure RETIRE_SUCCESS) :=
  keepsSuccess_bind (commutes_readSrc (Or.inr rfl) lhs) fun x =>
    keepsSuccess_bind (commutes_readSrc (Or.inr rfl) rhs) fun y =>
      keepsSuccess_ite
        (keepsSuccess_bind (sailCommutes_readReg _ (by decide)) fun pc =>
          keepsSuccess_jump_to v hv _)
        (keepsSuccess_of_commutes (commutes_pure _))

/-- One Jolt row keeps a successful run when embedded `misa` is replaced by a value
whose C bit is set. -/
private theorem keepsSuccess_execInstr (v : RegisterType Register.misa)
    (hv : _get_Misa_C v = 1#1) (i : JoltISA.Instr) :
    KeepsSuccess Register.misa v (JoltISA.execInstr i) := by
  cases i
  case BEQ lhs rhs imm =>
    exact keepsSuccess_branch v hv lhs rhs imm (JoltISA.branchDecisionPure (.BEQ lhs rhs imm))
  case BNE lhs rhs imm =>
    exact keepsSuccess_branch v hv lhs rhs imm (JoltISA.branchDecisionPure (.BNE lhs rhs imm))
  case BLT lhs rhs imm =>
    exact keepsSuccess_branch v hv lhs rhs imm (JoltISA.branchDecisionPure (.BLT lhs rhs imm))
  case BGE lhs rhs imm =>
    exact keepsSuccess_branch v hv lhs rhs imm (JoltISA.branchDecisionPure (.BGE lhs rhs imm))
  case BLTU lhs rhs imm =>
    exact keepsSuccess_branch v hv lhs rhs imm (JoltISA.branchDecisionPure (.BLTU lhs rhs imm))
  case BGEU lhs rhs imm =>
    exact keepsSuccess_branch v hv lhs rhs imm (JoltISA.branchDecisionPure (.BGEU lhs rhs imm))
  all_goals
    refine keepsSuccess_of_commutes ?_
    exact commutes_execInstr _ (Or.inr rfl) (fun h => by simp [usesJump] at h)

/-- Replacing embedded `misa` by a value whose C bit is set, before a Jolt program,
keeps the program's successful run. The embedded `misa` itself may have a clear C
bit: a taken branch to a 2-aligned target then does not retire, so a run that
retires never took one.
For example, a block of ADD rows retires identically under the Jolt initial `misa`
and under Sail's reset `misa`. -/
theorem execProgram_withMisa (p : JoltISA.Program) (v : RegisterType Register.misa)
    (hv : _get_Misa_C v = 1#1) (js t : SailJoltState)
    (h : JoltISA.execProgram p js = .ok RETIRE_SUCCESS t) :
    JoltISA.execProgram p (withReg js Register.misa v) =
      .ok RETIRE_SUCCESS (withReg t Register.misa v) := by
  induction p generalizing js t with
  | done result =>
    simp only [JoltISA.execProgram, pure, EStateM.pure] at h ⊢
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj h
    rfl
  | instr i rest ih =>
    simp only [JoltISA.execProgram, bind, EStateM.bind] at h ⊢
    cases hi : JoltISA.execInstr i js with
    | error e js' => simp [hi] at h
    | ok result js' =>
      simp only [hi] at h
      cases result <;> simp only [pure, EStateM.pure, RETIRE_SUCCESS] at h
      case Retire_Success u =>
        cases u
        have hk := keepsSuccess_execInstr v hv i js js' hi
        simp only [hk]
        exact ih js' t h
      all_goals cases h

end WholeRun
