import JoltConstraints.WholeRun.Basic

/-!
Jolt rows ignore the embedded Sail copies of the registers in `Untouched`.
These include the CSRs and reservation represented by Jolt virtual registers,
and Sail's instruction-retirement bookkeeping.
For example, replacing embedded `mstatus` commutes with an ADD row, including
when an operand is missing and the row returns an error.
-/

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

set_option autoImplicit false

noncomputable section

namespace WholeRun

variable {α β ε : Type} {r : Register} {v : RegisterType r}

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

private theorem sailCommutes_set_next_pc (hr : Untouched r) (pc : BitVec 64) :
    SailCommutes r v (set_next_pc pc) := by
  unfold set_next_pc
  exact sailCommutes_bind (sailCommutes_writeReg _ _ (by untouched_ne))
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
    | exact sailCommutes_readReg _ (by untouched_ne)
    | exact sailCommutes_writeReg _ _ (by untouched_ne)
    | exact sailCommutes_assert _ _
    | exact sailCommutes_pure _
    | apply sailCommutes_andM
    | apply sailCommutes_ite
    | apply sailCommutes_bind
    | split
    | intro _))

private theorem sailCommutes_rX (hr : Untouched r) (q : regidx) :
    SailCommutes r v (rX_bits q) := by
  unfold rX_bits rX
  sail_commutes

private theorem sailCommutes_wX (hr : Untouched r) (q : regidx) (w : BitVec 64) :
    SailCommutes r v (wX_bits q w) := by
  unfold wX_bits wX xreg_write_callback
  sail_commutes

private theorem commutes_readSrc (hr : Untouched r) (src : JoltISA.Src) :
    Commutes r v (JoltISA.readSrc src) := by
  cases src with
  | xreg q => exact sailCommutes_rX hr q
  | vreg q => intro js; rfl

private theorem commutes_writeDst (hr : Untouched r) (dst : JoltISA.Dst) (w : BitVec 64) :
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
      (sailECommutes_bind (sailECommutes_lift (sailCommutes_set_next_pc hr _))
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

private theorem commutes_readHostBytes
    (loadByte : BitVec 64 → JoltMonad (Result (BitVec 8) ExecutionResult))
    (hload : ∀ address, Commutes r v (loadByte address))
    (overflowChecks incrementAfterLast : Bool) {width : Nat}
    (pointer : BitVec width) (count : Nat) (bytes : Array (BitVec 8)) :
    Commutes r v
      (JoltISA.readHostBytes loadByte overflowChecks incrementAfterLast pointer count bytes) := by
  induction count generalizing pointer bytes with
  | zero => exact commutes_pure _
  | succ count ih =>
    unfold JoltISA.readHostBytes
    refine commutes_bind (hload _) fun result => ?_
    cases result with
    | Err _ => exact commutes_pure _
    | Ok byte =>
      dsimp only
      exact commutes_ite (commutes_bind (commutes_throw _) fun _ => ih _ _) (ih _ _)

local macro "jolt_commutes" : tactic =>
  `(tactic| repeat' (first
    | exact commutes_readSrc (by assumption) _
    | exact commutes_writeDst (by assumption) _ _
    | exact commutes_pure _
    | exact commutes_throw _
    | exact commutes_modify _ (fun _ => rfl)
    | apply commutes_ite
    | refine commutes_bind ?_ (fun _ => ?_)
    | exact sailCommutes_jump_to (by assumption) _
    | exact sailCommutes_set_next_pc (by assumption) _
    | exact sailCommutes_readReg _ (by untouched_ne)
    | exact sailCommutes_writeReg _ _ (by untouched_ne)
    | exact commutes_load _
    | exact commutes_load_doubleword _
    | exact commutes_store_doubleword _ _
    | split))

private theorem commutes_hostIO (hr : Untouched r) : Commutes r v JoltISA.execHostIO := by
  unfold JoltISA.execHostIO JoltISA.execHostIOWith
  refine commutes_get_bind (fun _ => rfl) (fun _ => ?_)
  jolt_commutes
  all_goals exact commutes_readHostBytes _ commutes_load _ _ _ _ _

private theorem commutes_adviceLoad (hr : Untouched r) (rd : JoltISA.Dst)
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

/-- Replacing an embedded Sail register in `Untouched` commutes with one Jolt
row, preserving its return value or error and replacing the same register in
its final state.
For example, an ADD row behaves identically after changing embedded `mstatus`,
even when its source register is absent. -/
theorem execInstr_withReg (i : JoltISA.Instr) (r : Register) (hr : Untouched r)
    (v : RegisterType r) (js : SailJoltState) :
    JoltISA.execInstr i (withReg js r v) = mapState (withReg · r v) (JoltISA.execInstr i js) := by
  suffices h : Commutes r v (JoltISA.execInstr i) from h js
  cases i
  case VirtualAdviceLoad rd num_bytes => exact commutes_adviceLoad hr rd num_bytes
  case VirtualHostIO => exact commutes_hostIO hr
  all_goals simp only [JoltISA.execInstr]
  all_goals jolt_commutes

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

end WholeRun
