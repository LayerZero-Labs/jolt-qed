import JoltBytecode.Step.TryStep
import JoltBytecode.InstructionEquivalence.ProofSupport.Preservation

/-!
# The generated Sail model's reservation policy

The reservation consists of a valid bit, a physical address and a byte width.
For example, LR.D records width 8 and permits SC.W at the same address.
The policy is documented in `docs/riscv-alignment.md`, section 3.
-/

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

noncomputable section
namespace Step

/-- No reservation: the reset values of the three reservation registers.
For example, reset stores `false`, address 0 and byte width 0. -/
def ReservationCleared (s : SailState) : Prop :=
  s.regs.get? Register.reservation_valid = some false ∧
    s.regs.get? Register.reservation_addr = some 0#64 ∧
    s.regs.get? Register.reservation_width = some 0

/-- The reservation registers are unchanged from `s` to `s'`.
For example, writing only the PC keeps the reservation. -/
def ReservationKept (s s' : SailState) : Prop :=
  s'.regs.get? Register.reservation_valid = s.regs.get? Register.reservation_valid ∧
    s'.regs.get? Register.reservation_addr = s.regs.get? Register.reservation_addr ∧
    s'.regs.get? Register.reservation_width = s.regs.get? Register.reservation_width

/-- Jolt's reservation policy (docs/riscv-alignment.md, section 3).
For example, LR.D permits SC.W at the same address, and that SC clears the reservation. -/
structure ReservationPolicyLegal : Prop where
  /-- Rule 1. -/
  load : ∀ (a : BitVec 64) (w : Nat) (s : SailState),
    load_reservation a w s =
      .ok () (setReg (setReg (setReg s Register.reservation_valid true)
        Register.reservation_addr a) Register.reservation_width (w : Int))
  /-- Rule 2, for a nonnegative stored byte width, such as 0, 4 or 8. -/
  match_iff : ∀ (a : BitVec 64) (w : Nat) (s : SailState) (v : Bool) (ra : BitVec 64) (rw : Int),
    0 ≤ rw →
    s.regs.get? Register.reservation_valid = some v →
    s.regs.get? Register.reservation_addr = some ra →
    s.regs.get? Register.reservation_width = some rw →
    match_reservation a w s = .ok (v && a == ra && decide ((w : Int) ≤ rw)) s
  /-- Rule 3. -/
  sc_cancels : ∀ (aq rl : Bool) (rs2 rs1 rd : regidx) (width : Nat) (s s' : SailState),
    execute_STORECON aq rl rs2 rs1 width rd s = .ok RETIRE_SUCCESS s' → ReservationCleared s'
  /-- Rule 4. -/
  reset_clears : ∀ (s s' : SailState), reset_sys () s = .ok () s' → ReservationCleared s'
  /-- Rule 5, traps and xRET. -/
  xret_keeps : plat_reservation_invalidate_on_xret = false
  handler_keeps : ∀ (p : Privilege) (ctl : ctl_result) (pc : BitVec 64) (s s' : SailState) v,
    exception_handler p ctl pc s = .ok v s' → ReservationKept s s'

private theorem reservation_load (a : BitVec 64) (w : Nat) (s : SailState) :
    load_reservation a w s =
      .ok () (setReg (setReg (setReg s Register.reservation_valid true)
        Register.reservation_addr a) Register.reservation_width (w : Int)) := rfl

private theorem reservation_match (a : BitVec 64) (w : Nat) (s : SailState)
    (v : Bool) (ra : BitVec 64) (rw : Int) (hrw : 0 ≤ rw)
    (hv : s.regs.get? Register.reservation_valid = some v)
    (ha : s.regs.get? Register.reservation_addr = some ra)
    (hw : s.regs.get? Register.reservation_width = some rw) :
    match_reservation a w s = .ok (v && a == ra && decide ((w : Int) ≤ rw)) s := by
  have hle : (w ≤ rw.toNat) ↔ (w : Int) ≤ rw := by omega
  unfold match_reservation
  simp [plat_reservation_require_exact_addr_match, plat_reservation_require_width_within,
    LeanRV64D.Functions.not, orM, toBool, bind, EStateM.bind, pure, EStateM.pure,
    readReg_eq_of_get? _ _ _ hv, readReg_eq_of_get? _ _ _ ha,
    readReg_eq_of_get? _ _ _ hw, hle, Bool.and_assoc]

private theorem reservation_cancel (s : SailState) :
    ReservationCleared (setReg (setReg (setReg s Register.reservation_valid false)
      Register.reservation_addr 0#64) Register.reservation_width 0) := by
  simp [ReservationCleared, setReg, Std.ExtDHashMap.get?_insert]

private theorem kept_refl (s : SailState) : ReservationKept s s := ⟨rfl, rfl, rfl⟩

private theorem kept_trans (s t u : SailState) (h : ReservationKept s t)
    (h' : ReservationKept t u) : ReservationKept s u :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

/-- A successful computation preserves all three reservation registers;
for example, reading `mstatus` preserves them. -/
private abbrev Keeps {α : Type} (m : SailM α) :=
  StatePreservation.Preserves ReservationKept m

private theorem keeps_pure {α : Type} (v : α) : Keeps (pure v) :=
  StatePreservation.pure_rule kept_refl v

private theorem keeps_bind {α β : Type} {m : SailM α} {f : α → SailM β}
    (hm : Keeps m) (hf : ∀ a, Keeps (f a)) : Keeps (m >>= f) :=
  StatePreservation.bind_rule kept_trans hm hf

private theorem keeps_read (r : Register) : Keeps (LeanRV64D.readReg r) := by
  unfold LeanRV64D.readReg Sail.ConcurrencyInterfaceV1.PreSail.readReg
  preservation_auto [StatePreservation.get_rule kept_refl,
    StatePreservation.throw_rule _ _, keeps_pure _] using keeps_bind

private theorem keeps_write (r : Register) (v : RegisterType r)
    (hv : r ≠ Register.reservation_valid) (ha : r ≠ Register.reservation_addr)
    (hw : r ≠ Register.reservation_width) : Keeps (LeanRV64D.writeReg r v) := by
  intro s s' a h
  rw [writeReg_run] at h
  cases h
  exact ⟨setReg_get?_ne _ _ hv, setReg_get?_ne _ _ ha, setReg_get?_ne _ _ hw⟩

private theorem keeps_throw {α : Type} (e : Error exception) :
    Keeps (throw e : SailM α) := StatePreservation.throw_rule _ e

private theorem keeps_assert (b : Bool) (msg : String) :
    Keeps (LeanRV64D.sail_assert b msg) := by
  cases b
  · exact keeps_throw _
  · exact keeps_pure _

private theorem keeps_internal_error {α : Type} (file : String) (line : Int) (msg : String) :
    Keeps (internal_error (k_a := α) file line msg) := keeps_throw _

private theorem keeps_callback (name : String) (value : BitVec 64) {csr : BitVec 12}
    (hm : csr_name_map_backwards name = (pure csr : SailM (BitVec 12))) :
    Keeps (csr_name_write_callback name value) := by
  unfold csr_name_write_callback
  rw [hm]
  exact keeps_bind (keeps_pure _) fun _ => keeps_pure _

-- Compose frames while reducing the generated backend's local continuations.
local macro "reservation_frame" "[" rules:term,* "]" : tactic => do
  let mut step ← `(tactic| first
    | dsimp only
    | with_reducible exact keeps_pure _
    | with_reducible exact keeps_read _
    | with_reducible exact keeps_write _ _ (by decide) (by decide) (by decide)
    | with_reducible exact keeps_throw _
    | with_reducible exact keeps_assert _ _
    | with_reducible exact keeps_internal_error _ _ _
    | (with_reducible apply keeps_callback; rfl)
    | refine keeps_bind ?_ (fun _ => ?_)
    | split)
  for rule in rules.getElems.reverse do
    let previous ← `(tacticSeq| $step:tactic)
    step ← `(tactic| first | with_reducible exact $rule | $previous)
  let sequence ← `(tacticSeq| $step:tactic)
  `(tactic| repeat' $sequence)

private theorem keeps_zca : Keeps (currentlyEnabled .Ext_Zca) := by
  unfold currentlyEnabled
  unfold currentlyEnabled
  simp only [andM]
  reservation_frame []

private theorem keeps_u : Keeps (currentlyEnabled .Ext_U) := by
  have h : currentlyEnabled .Ext_U = (pure false : SailM Bool) :=
    funext HartConfig.currentlyEnabled_U_run
  rw [h]
  exact keeps_pure _

private theorem keeps_s : Keeps (currentlyEnabled .Ext_S) := by
  have h : currentlyEnabled .Ext_S = (pure false : SailM Bool) :=
    funext HartConfig.currentlyEnabled_S_run
  rw [h]
  exact keeps_pure _

private theorem keeps_priv_bits (bits : BitVec 2 × BitVec 1) :
    Keeps (privLevel_bits_forwards bits) := by
  unfold privLevel_bits_forwards
  reservation_frame []

private theorem keeps_trap_vector (p : Privilege) (cause : BitVec 64) :
    Keeps (prepare_trap_vector p cause) := by
  unfold prepare_trap_vector
  reservation_frame []

private theorem keeps_xret_target (p : Privilege) : Keeps (prepare_xret_target p) := by
  unfold prepare_xret_target get_xepc align_pc
  preservation_auto [keeps_zca, keeps_pure _, keeps_read _, keeps_internal_error _ _ _]
    using keeps_bind

private theorem keeps_track_trap (p : Privilege) : Keeps (track_trap p) := by
  unfold track_trap long_csr_write_callback
  reservation_frame []

private theorem keeps_delegatee (e : ExceptionType) (p : Privilege) :
    Keeps (exception_delegatee e p) := by
  unfold exception_delegatee
  reservation_frame [keeps_s]

private theorem keeps_trap_handler (p : Privilege) (c : TrapCause) (pc : BitVec 64)
    (info : Option (BitVec 64)) (ext : Option Unit) :
    Keeps (trap_handler p c pc info ext) := by
  unfold trap_handler
  simp only [get_config_print_exception, get_config_print_interrupt,
    hartSupports, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  reservation_frame [keeps_track_trap _, keeps_trap_vector _ _, keeps_s]

private theorem keeps_exception_handler (p : Privilege) (ctl : ctl_result) (pc : BitVec 64) :
    Keeps (exception_handler p ctl pc) := by
  unfold exception_handler
  simp only [get_config_print_exception, hartSupports,
    Bool.false_eq_true, ↓reduceIte]
  unfold long_csr_write_callback
  reservation_frame [keeps_delegatee _ _, keeps_trap_handler _ _ _ _ _,
    keeps_xret_target _, keeps_priv_bits _, keeps_u]

private theorem keeps_range {α : Type} (range : IntRange)
    (body : (i : Int) → i ∈ range → α → SailM (ForInStep α))
    (hb : ∀ i hi x, Keeps (body i hi x)) (x : α) :
    Keeps (IntRange.forIn' range x body) := by
  have loop : ∀ (y : α) (i : Int) (hs : (i - range.start) % range.step = 0),
      Keeps (IntRange.forIn'.loop range body y i hs) := by
    intro y i hs
    induction y, i, hs using IntRange.forIn'.loop.induct range with
    | case1 y i hs hi ih =>
      rw [IntRange.forIn'.loop.eq_1, dite_eq_left hi]
      apply keeps_bind (hb i hi y)
      intro result
      cases result with
      | done z => exact keeps_pure z
      | yield z => exact ih z
    | case2 y i hs hi =>
      rw [IntRange.forIn'.loop.eq_1, dite_eq_right hi]
      exact keeps_pure y
  exact loop x range.start _

private theorem keeps_reset_pmp : Keeps (reset_pmp ()) := by
  unfold reset_pmp
  apply keeps_bind
  · apply keeps_range
    intro i hi x
    reservation_frame []
  · intro _
    exact keeps_pure _

private theorem keeps_reset_stateen : Keeps (reset_stateen ()) := by
  unfold reset_stateen
  reservation_frame []

/-- Every normal result leaves the reservation cleared; for example,
`cancel_reservation ()` stores `false`, address 0 and byte width 0. -/
private def Clears {α : Type} (m : SailM α) : Prop :=
  ∀ s s' a, m s = .ok a s' → ReservationCleared s'

private theorem clears_cancel : Clears (cancel_reservation ()) := by
  intro s s' a h
  change EStateM.Result.ok (ε := Error exception) ()
    (setReg (setReg (setReg s Register.reservation_valid false)
      Register.reservation_addr 0#64) Register.reservation_width 0) = .ok a s' at h
  cases h
  exact reservation_cancel s

private theorem clears_tail {α β : Type} {m : SailM α} {f : α → SailM β}
    (hf : ∀ a, Clears (f a)) : Clears (m >>= f) := by
  intro s s' b h
  cases hm : m s with
  | error e t => simp only [bind, EStateM.bind, hm] at h; cases h
  | ok a t =>
    simp only [bind, EStateM.bind, hm] at h
    exact hf a t s' b h

private theorem clears_keep_bind {α β : Type} {m : SailM α} {f : α → SailM β}
    (hm : Clears m) (hf : ∀ a, Keeps (f a)) : Clears (m >>= f) := by
  intro s s' b h
  cases hms : m s with
  | error e t => simp only [bind, EStateM.bind, hms] at h; cases h
  | ok a t =>
    simp only [bind, EStateM.bind, hms] at h
    have hc := hm s t a hms
    have hk := hf a t s' b h
    exact ⟨hk.1.trans hc.1, hk.2.1.trans hc.2.1, hk.2.2.trans hc.2.2⟩

private theorem reservation_reset : Clears (reset_sys ()) := by
  unfold reset_sys
  repeat' first
    | apply clears_keep_bind clears_cancel
    | apply clears_tail; intro _
  intro _
  simp only [hartSupports, Bool.false_eq_true, ↓reduceIte]
  reservation_frame [keeps_reset_pmp, keeps_reset_stateen]

-- Unlike register frames, these predicates constrain returned values. They
-- allow arbitrary memory effects while ruling out a successful retirement
-- masquerading as a memory error.
/-- Every normal result satisfies `p`, regardless of memory effects;
for example, a memory write cannot return `.Err RETIRE_SUCCESS`. -/
private def Returns {α : Type} (p : α → Prop) (m : SailM α) : Prop :=
  ∀ s s' a, m s = .ok a s' → p a

private theorem returns_pure {α : Type} {p : α → Prop} (a : α) (ha : p a) :
    Returns p (pure a) := by
  intro s s' a' h
  cases h
  exact ha

private theorem returns_bind {α β : Type} {p : α → Prop} {q : β → Prop}
    {m : SailM α} {f : α → SailM β} (hm : Returns p m)
    (hf : ∀ a, p a → Returns q (f a)) : Returns q (m >>= f) := by
  intro s s' b h
  cases hms : m s with
  | error e t => simp only [bind, EStateM.bind, hms] at h; cases h
  | ok a t =>
    simp only [bind, EStateM.bind, hms] at h
    exact hf a (hm s t a hms) t s' b h

/-- An early return satisfies `p` and a normal result satisfies `q`.
For example, a write-loop iteration may return a memory exception early. -/
private def Checked {ε α : Type} (p : ε → Prop) (q : α → Prop)
    (m : SailME ε α) : Prop :=
  Returns (fun r => match r with
    | .ok a => q a
    | .error (.inr e) => p e
    | .error (.inl _) => True) (ExceptT.run m)

private theorem checked_pure {ε α : Type} {p : ε → Prop} {q : α → Prop}
    (a : α) (ha : q a) : Checked p q (pure a) := returns_pure _ ha

private theorem checked_bind {ε α β : Type} {p : ε → Prop} {q : β → Prop}
    {m : SailME ε α} {f : α → SailME ε β}
    (hm : Checked p (fun _ => True) m) (hf : ∀ a, Checked p q (f a)) :
    Checked p q (m >>= f) := by
  change Returns _ (ExceptT.run m >>= ExceptT.bindCont f)
  refine returns_bind (m := ExceptT.run m) (f := ExceptT.bindCont f) hm ?_
  intro r hr
  cases r with
  | ok a => exact hf a
  | error e => cases e <;> exact returns_pure _ hr

private theorem checked_lift_of_returns {ε α : Type} {p : ε → Prop} {q : α → Prop}
    {m : SailM α} (hm : Returns q m) : Checked p q (liftM m) := by
  intro s s' r h
  change EStateM.map (@Except.ok (Error exception ⊕ ε) α) m s = .ok r s' at h
  cases hms : m s with
  | error e t => simp [EStateM.map, hms] at h
  | ok a t =>
    simp only [EStateM.map, hms, EStateM.Result.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact hm s t a hms

private theorem checked_lift {ε α : Type} (p : ε → Prop) (m : SailM α) :
    Checked p (fun _ => True) (liftM m) :=
  checked_lift_of_returns (fun _ _ _ _ => trivial)

private theorem checked_throw {ε α : Type} {p : ε → Prop} {q : α → Prop}
    (e : ε) (he : p e) : Checked p q (SailME.throw e) := returns_pure _ he

private theorem checked_run {α : Type} {p : α → Prop} {m : SailME α α}
    (hm : Checked p p m) : Returns p (SailME.run m) := by
  unfold SailME.run Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run
  refine returns_bind (m := ExceptT.run m) hm ?_
  intro r hr
  cases r with
  | ok a => exact returns_pure a hr
  | error e =>
    cases e with
    | inr a => exact returns_pure a hr
    | inl e => intro s s' a h; cases h

-- Invariant of the generated write loop: every early return satisfies p.
-- The current offset, memory contents and translation results are unrestricted.
private theorem checked_until {ε α : Type} {p : ε → Prop} (fuel : Nat)
    (cond : α → SailME ε Bool) (body : α → SailME ε α)
    (hc : ∀ x, Checked p (fun _ => True) (cond x))
    (hb : ∀ x, Checked p (fun _ => True) (body x)) (x : α) :
    Checked p (fun _ => True) (untilFuelM fuel cond x body) := by
  unfold untilFuelM
  induction fuel generalizing x with
  | zero => exact checked_pure _ trivial
  | succ n ih =>
    unfold untilFuelM.go
    apply checked_bind (hb x)
    intro y
    apply checked_bind (hc y)
    intro b
    split
    · exact checked_pure _ trivial
    · exact ih y

/-- A memory-write result cannot disguise successful retirement as an error;
for example, `.Err (Memory_Exception ...)` satisfies this predicate. -/
private def WriteResultLegal (r : Result Bool ExecutionResult) : Prop :=
  r ≠ .Err RETIRE_SUCCESS

local macro "reservation_result" : tactic =>
  `(tactic| repeat' (first
    | dsimp only
    | with_reducible exact checked_pure _ (by simp [WriteResultLegal, RETIRE_SUCCESS])
    | with_reducible exact checked_throw _ (by simp [WriteResultLegal, RETIRE_SUCCESS])
    | with_reducible exact checked_lift _ _
    | apply checked_until <;> intro _
    | split
    | refine checked_bind ?_ (fun _ => ?_)))

private theorem vmem_write_addr_result (vaddr : virtaddr) (width : Nat)
    (data : BitVec (8 * width)) (access : MemoryAccessType mem_payload)
    (aq rl res : Bool) :
    Returns WriteResultLegal (vmem_write_addr vaddr width data access aq rl res) := by
  unfold vmem_write_addr
  apply checked_run
  simp only [andM]
  reservation_result

private theorem vmem_write_result (rs : regidx) (offset : BitVec 64) (width : Nat)
    (data : BitVec (8 * width)) (access : MemoryAccessType mem_payload)
    (aq rl res : Bool) :
    Returns WriteResultLegal (vmem_write rs offset width data access aq rl res) := by
  unfold vmem_write
  apply checked_run
  refine checked_bind ?_ (fun _ => checked_lift_of_returns
    (vmem_write_addr_result _ _ _ _ _ _ _))
  apply checked_bind (checked_lift _ _)
  intro result
  split
  · exact checked_pure _ trivial
  · exact checked_throw _ (by simp [WriteResultLegal, RETIRE_SUCCESS])

private theorem bind_ok {α β : Type} {m : SailM α} {f : α → SailM β}
    {s s' : SailState} {b : β} (h : (m >>= f) s = .ok b s') :
    ∃ a t, m s = .ok a t ∧ f a t = .ok b s' := by
  cases hm : m s with
  | error e t => simp only [bind, EStateM.bind, hm] at h; cases h
  | ok a t => exact ⟨a, t, rfl, by simpa only [bind, EStateM.bind, hm] using h⟩

private theorem reservation_sc (aq rl : Bool) (rs2 rs1 rd : regidx) (width : Nat)
    (s s' : SailState)
    (h : execute_STORECON aq rl rs2 rs1 width rd s = .ok RETIRE_SUCCESS s') :
    ReservationCleared s' := by
  unfold execute_STORECON at h
  obtain ⟨_, t, _, h⟩ := bind_ok h
  obtain ⟨data, u, _, h⟩ := bind_ok h
  simp only [pure_bind] at h
  obtain ⟨result, v, hr, h⟩ := bind_ok h
  cases result with
  | Ok success =>
    exact clears_tail (fun _ => clears_keep_bind clears_cancel (fun _ => keeps_pure _))
      v s' _ h
  | Err e =>
    change EStateM.Result.ok (ε := Error exception) e v = .ok RETIRE_SUCCESS s' at h
    cases h
    exact False.elim ((vmem_write_result rs1 0#64 width _ (.StoreConditional .Data)
      (aq && rl) rl true u s' _ hr) rfl)

/-- Sail implements the five reservation rules: for example, SC.W can use an
LR.D reservation at the same address and clears it after either normal result. -/
theorem reservationPolicyLegal : ReservationPolicyLegal where
  load := reservation_load
  match_iff := reservation_match
  sc_cancels := reservation_sc
  reset_clears := fun s s' h => reservation_reset s s' () h
  xret_keeps := rfl
  handler_keeps := keeps_exception_handler

/-- Jolt's SC sequences compare the address with `w` (SC.W) or `d` (SC.D),
where `w` is the address of any live reservation and `d` that of a live
doubleword reservation, else 0. Given the encoding of Sail's registers in
`w` and `d`, Sail's `match_reservation` makes the same comparison.
For example, `w = d = a = 16` makes both SC widths succeed. -/
theorem match_reservation_jolt (s : SailState) (w d a : BitVec 64)
    (hv : s.regs.get? Register.reservation_valid = some (w != 0#64))
    (ha : s.regs.get? Register.reservation_addr = some w)
    (hw : s.regs.get? Register.reservation_width =
      some (if w = 0#64 then 0 else if d = w then 8 else 4))
    (hpair : d = 0#64 ∨ d = w) (ha0 : a ≠ 0#64) :
    match_reservation a 4 s = .ok (a == w) s ∧ match_reservation a 8 s = .ok (a == d) s := by
  have hnonneg : (0 : Int) ≤ (if w = 0#64 then 0 else if d = w then 8 else 4) := by
    split <;> omega
  rw [reservation_match a 4 s _ _ _ hnonneg hv ha hw,
    reservation_match a 8 s _ _ _ hnonneg hv ha hw]
  by_cases hw0 : w = 0#64
  · subst w
    have hd0 : d = 0#64 := hpair.elim id id
    subst d
    simp [ha0]
  · by_cases hd : d = w
    · subst d
      simp [hw0]
    · have hd0 := hpair.resolve_right hd
      subst d
      simp [hw0, hd, ha0]

end Step
