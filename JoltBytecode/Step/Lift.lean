import JoltBytecode.Step.TryStep
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection

/-!
# Lifting Jolt rows to one `try_step`

The instruction theorems compare a Jolt program with one Sail `execute`
clause. This file turns such a comparison into a statement about a whole
`try_step` on Jolt's hart.

The Jolt-side step `joltStep` runs Sail's own bookkeeping around the Jolt rows:
the prelude (count the instruction, set `nextPC` to the fall-through address)
and, after the rows retire, the result handling (advance the PC, bump
`minstret`). Both parts are lifted onto the embedded Sail state. Jolt has no
instruction counter of its own, and no Jolt row reads `minstret`,
`minstret_increment` or any other counter, so this bookkeeping changes nothing
Jolt observes.

The bookkeeping touches none of the nine system registers that `System.systemProject`
takes from Jolt's virtual registers (`OverlayLocal`), so it commutes with the
projection. `joltStep_eq_try_step` is the generic lifting lemma: if the Jolt
rows agree with `execute` after the prelude and the instruction retires, the
projected Jolt step equals `try_step`.
-/

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Step

/-! ## The CSR overlay -/

/-- The six CSRs and three reservation registers supplied by Jolt's virtual
registers in `System.systemProject`.
For example, Sail reservation_width is derived from v32 and v33. -/
def Overlaid (r : Register) : Prop :=
  r = Register.mtvec ∨ r = Register.mscratch ∨ r = Register.mepc ∨
    r = Register.mcause ∨ r = Register.mtval ∨ r = Register.mstatus ∨
    r = Register.reservation_valid ∨ r = Register.reservation_addr ∨
    r = Register.reservation_width

/-- Outside the nine overlaid registers, the projection reads the embedded Sail state. -/
theorem systemProject_get?_of_not_overlaid (js : SailJoltState) {r : Register}
    (hr : ¬ Overlaid r) :
    (System.systemProject js).regs.get? r = js.sail.regs.get? r := by
  simp only [Overlaid, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hr
  unfold System.systemProject
  simp only [System.extDHashMap_get?_insert_of_ne _ _ (Ne.symm h1),
    System.extDHashMap_get?_insert_of_ne _ _ (Ne.symm h2),
    System.extDHashMap_get?_insert_of_ne _ _ (Ne.symm h3),
    System.extDHashMap_get?_insert_of_ne _ _ (Ne.symm h4),
    System.extDHashMap_get?_insert_of_ne _ _ (Ne.symm h5),
    System.extDHashMap_get?_insert_of_ne _ _ (Ne.symm h6),
    System.extDHashMap_get?_insert_of_ne _ _ (Ne.symm h7),
    System.extDHashMap_get?_insert_of_ne _ _ (Ne.symm h8),
    System.extDHashMap_get?_insert_of_ne _ _ (Ne.symm h9)]

/-- Writing a register outside the overlay commutes with the projection. -/
theorem systemProject_setReg (js : SailJoltState) (r : Register) (v : RegisterType r)
    (hr : ¬ Overlaid r) :
    System.systemProject { js with sail := setReg js.sail r v } =
      setReg (System.systemProject js) r v := by
  simp only [Overlaid, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hr
  unfold System.systemProject setReg
  rw [System.extDHashMap_insert_comm_of_ne (h := h1),
    System.extDHashMap_insert_comm_of_ne (h := h2),
    System.extDHashMap_insert_comm_of_ne (h := h3),
    System.extDHashMap_insert_comm_of_ne (h := h4),
    System.extDHashMap_insert_comm_of_ne (h := h5),
    System.extDHashMap_insert_comm_of_ne (h := h6),
    System.extDHashMap_insert_comm_of_ne (h := h7),
    System.extDHashMap_insert_comm_of_ne (h := h8),
    System.extDHashMap_insert_comm_of_ne (h := h9)]

/-! ## Sail computations that commute with the overlay -/

/-- `m` reads and writes no overlaid CSR, so running it on the embedded Sail
state and projecting is the same as running it on the projection. -/
structure OverlayLocal (m : SailM α) : Prop where
  run : ∀ js : SailJoltState,
    System.systemProjectResult (liftSail m js) = m (System.systemProject js)

theorem OverlayLocal.pure (a : α) : OverlayLocal (pure a : SailM α) := ⟨fun _ => rfl⟩

theorem OverlayLocal.bind {m : SailM α} {f : α → SailM β}
    (hm : OverlayLocal m) (hf : ∀ a, OverlayLocal (f a)) :
    OverlayLocal (m >>= f) := by
  constructor
  intro js
  have h := hm.run js
  unfold liftSail System.systemProjectResult at h
  have hb : ∀ s, (m >>= f) s = EStateM.bind m f s := fun _ => rfl
  unfold liftSail
  rw [hb, hb]
  simp only [EStateM.bind]
  cases hms : m js.sail with
  | ok a s1 =>
    simp only [hms] at h
    rw [← h]
    exact (hf a).run { js with sail := s1 }
  | error e s1 =>
    simp only [hms] at h
    rw [← h]
    rfl

theorem OverlayLocal.ite {c : Prop} [Decidable c] {m₁ m₂ : SailM α}
    (h₁ : OverlayLocal m₁) (h₂ : OverlayLocal m₂) :
    OverlayLocal (if c then m₁ else m₂) := by
  split
  · exact h₁
  · exact h₂

theorem OverlayLocal.andM {x y : SailM Bool}
    (hx : OverlayLocal x) (hy : OverlayLocal y) :
    OverlayLocal (x <&&> y) := by
  unfold _root_.andM
  refine OverlayLocal.bind hx fun b => ?_
  cases b
  · exact OverlayLocal.pure _
  · exact hy

theorem readReg_eq_of_get?_none (r : Register) (s : SailState)
    (h : s.regs.get? r = none) :
    (LeanRV64D.readReg r : SailM (RegisterType r)) s = .error .Unreachable s := by
  unfold LeanRV64D.readReg Sail.ConcurrencyInterfaceV1.PreSail.readReg
  simp only [bind, EStateM.bind, MonadStateOf.get, EStateM.get, getThe, get, h]
  rfl

theorem OverlayLocal.readReg {r : Register} (hr : ¬ Overlaid r) :
    OverlayLocal (LeanRV64D.readReg r : SailM (RegisterType r)) := by
  constructor
  intro js
  have hg := systemProject_get?_of_not_overlaid js hr
  unfold liftSail
  cases h : js.sail.regs.get? r with
  | none =>
    rw [readReg_eq_of_get?_none r _ h, readReg_eq_of_get?_none r _ (hg.trans h)]
    rfl
  | some v =>
    rw [readReg_eq_of_get? r _ v h, readReg_eq_of_get? r _ v (hg.trans h)]
    rfl

theorem OverlayLocal.writeReg {r : Register} (v : RegisterType r) (hr : ¬ Overlaid r) :
    OverlayLocal (LeanRV64D.writeReg r v : SailM Unit) := by
  constructor
  intro js
  unfold liftSail
  rw [writeReg_run, writeReg_run]
  simp only [System.systemProjectResult]
  rw [systemProject_setReg js r v hr]

theorem OverlayLocal.sail_assert (b : Bool) (msg : String) :
    OverlayLocal (LeanRV64D.sail_assert b msg) := by
  constructor
  intro js
  cases b <;> rfl

/-- Discharge `OverlayLocal` for a straight-line Sail block that touches only
registers outside the overlay. -/
macro "overlay_local" : tactic =>
  `(tactic| repeat (first
    | exact OverlayLocal.readReg (by simp [Overlaid])
    | exact OverlayLocal.writeReg _ (by simp [Overlaid])
    | exact OverlayLocal.sail_assert _ _
    | exact OverlayLocal.pure _
    | apply OverlayLocal.andM
    | apply OverlayLocal.ite
    | apply OverlayLocal.bind
    | intro _))

/-- A local computation that succeeds on the embedded state succeeds the same
way on the projection. -/
theorem OverlayLocal.run_ok {m : SailM α} (hm : OverlayLocal m) (js : SailJoltState)
    {a : α} {s' : SailState} (h : m js.sail = .ok a s') :
    m (System.systemProject js) = .ok a (System.systemProject { js with sail := s' }) := by
  rw [← hm.run js]
  unfold liftSail
  rw [h]
  rfl

/-! ## The bookkeeping around the Jolt rows -/

/-- `try_step`'s prelude after fetch and decode: record whether this
instruction counts towards `minstret`, and set `nextPC` to the fall-through
address `len` bytes on. -/
def stepPrelude (len : Int) : SailM Unit := do
  let inc ← should_inc_minstret Privilege.Machine
  LeanRV64D.writeReg Register.minstret_increment inc
  let pc ← LeanRV64D.readReg Register.PC
  LeanRV64D.writeReg Register.nextPC (BitVec.addInt pc len)

theorem overlayLocal_should_inc_minstret :
    OverlayLocal (should_inc_minstret Privilege.Machine) := by
  unfold should_inc_minstret
  overlay_local

theorem overlayLocal_stepPrelude (len : Int) : OverlayLocal (stepPrelude len) := by
  unfold stepPrelude
  refine OverlayLocal.bind overlayLocal_should_inc_minstret fun _ => ?_
  overlay_local

theorem stepPrelude_run (len : Int) (s : SailState) (inc : Bool)
    (hinc : should_inc_minstret Privilege.Machine s = .ok inc s)
    (pc : BitVec 64) (hpc : s.regs.get? Register.PC = some pc) :
    stepPrelude len s = .ok () (preludeState s inc pc len) := by
  have hpc1 := readReg_eq_of_get? Register.PC (setReg s Register.minstret_increment inc) pc
    (by rw [setReg_get?_ne _ _ (by decide)]; exact hpc)
  unfold stepPrelude preludeState
  simp only [bind, EStateM.bind, hinc, writeReg_run, hpc1]

/-- `stepFinish` after a retired instruction: advance the PC and bump
`minstret`. It reads only `hart_state`, `nextPC`, `PC`,
`minstret_increment` and `minstret`. -/
theorem overlayLocal_stepFinish_retire (bits : BitVec 32) :
    OverlayLocal (stepFinish (.Step_Execute (RETIRE_SUCCESS, bits))) := by
  unfold stepFinish tick_pc
  simp only [RETIRE_SUCCESS, get_config_rvfi, Bool.false_eq_true, ↓reduceIte]
  refine OverlayLocal.bind (OverlayLocal.readReg (by simp [Overlaid])) fun _ => ?_
  refine OverlayLocal.bind (OverlayLocal.sail_assert _ _) fun _ => ?_
  refine OverlayLocal.bind (OverlayLocal.readReg (by simp [Overlaid])) fun hs => ?_
  cases hs with
  | HART_WAITING _ => exact OverlayLocal.pure _
  | HART_ACTIVE u =>
    cases u
    overlay_local

/-! ## The Jolt step -/

/-- One step of Jolt's machine for an instruction of `len` bytes with encoding
`bits`: Sail's prelude, the Jolt rows `prog`, then Sail's result handling. -/
def joltStep (len : Int) (bits : BitVec 32) (prog : JoltMonad ExecutionResult) :
    JoltMonad Bool := do
  liftSail (stepPrelude len)
  let r ← prog
  liftSail (stepFinish (.Step_Execute (r, bits)))

/-- The Jolt state after the prelude, on which the Jolt rows run. -/
def preludeJolt (js : SailJoltState) (inc : Bool) (pc : BitVec 64) (len : Int) :
    SailJoltState :=
  { js with sail := preludeState js.sail inc pc len }

theorem systemProject_preludeJolt (js : SailJoltState) (inc : Bool) (pc : BitVec 64)
    (len : Int) :
    System.systemProject (preludeJolt js inc pc len) =
      preludeState (System.systemProject js) inc pc len := by
  unfold preludeJolt preludeState
  rw [← systemProject_setReg _ _ _ (by simp [Overlaid])]
  exact systemProject_setReg { js with sail := setReg js.sail Register.minstret_increment inc }
    Register.nextPC _ (by simp [Overlaid])

/-- **Generic lifting lemma.** Suppose `try_step` on the projected state runs
the prelude and then executes `ast`, the Jolt rows `prog` agree with
`execute ast` after the prelude, and the instruction retires. Then one Jolt
step projects to one `try_step`, including when execution fails. -/
theorem joltStep_eq_try_step (n : Nat) (js : SailJoltState) (len : Int) (bits : BitVec 32)
    (ast : instruction) (prog : JoltMonad ExecutionResult) (inc : Bool) (pc : BitVec 64)
    (hinc : should_inc_minstret Privilege.Machine js.sail = .ok inc js.sail)
    (hpc : js.sail.regs.get? Register.PC = some pc)
    (htry : try_step n false (System.systemProject js) =
      executeAndFinish ast bits (preludeState (System.systemProject js) inc pc len))
    (hprog : System.systemProjectResult (prog (preludeJolt js inc pc len)) =
      execute ast (System.systemProject (preludeJolt js inc pc len)))
    (hretire : ∀ r s', execute ast (System.systemProject (preludeJolt js inc pc len)) =
      .ok r s' → r = RETIRE_SUCCESS) :
    System.systemProjectResult (joltStep len bits prog js) =
      try_step n false (System.systemProject js) := by
  rw [htry, ← systemProject_preludeJolt]
  have hpre : liftSail (stepPrelude len) js = .ok () (preludeJolt js inc pc len) := by
    unfold liftSail
    rw [stepPrelude_run len js.sail inc hinc pc hpc]
    rfl
  unfold joltStep executeAndFinish executeFull
  simp only [bind, EStateM.bind, hpre]
  cases hp : prog (preludeJolt js inc pc len) with
  | ok r js2 =>
    simp only [hp, System.systemProjectResult] at hprog
    rw [← hprog]
    have hr := hretire r _ hprog.symm
    subst hr
    exact (overlayLocal_stepFinish_retire bits).run js2
  | error e js2 =>
    simp only [hp, System.systemProjectResult] at hprog
    rw [← hprog]
    rfl

/-- Facts about the projected state transfer from the embedded Sail state. -/
theorem should_inc_minstret_systemProject (js : SailJoltState) (inc : Bool)
    (hinc : should_inc_minstret Privilege.Machine js.sail = .ok inc js.sail) :
    should_inc_minstret Privilege.Machine (System.systemProject js) =
      .ok inc (System.systemProject js) :=
  overlayLocal_should_inc_minstret.run_ok js hinc

/-- **Step theorem, 32-bit instructions.** On a state satisfying
`StepInvariant`, where `try_step` fetches the word `w` and decodes it to `ast`,
one Jolt step running `prog` projects to `try_step`, provided `prog` agrees
with `execute ast` after the prelude and the instruction retires. -/
theorem joltStep_base (n : Nat) (js : SailJoltState)
    (hinv : StepInvariant (System.systemProject js))
    (inc : Bool) (hinc : should_inc_minstret Privilege.Machine js.sail = .ok inc js.sail)
    (pc : BitVec 64) (hpc : js.sail.regs.get? Register.PC = some pc)
    (w : BitVec 32) (ast : instruction)
    (hfetch : fetch () (setReg (System.systemProject js) Register.minstret_increment inc) =
      .ok (.F_Base w) (setReg (System.systemProject js) Register.minstret_increment inc))
    (hdec : ext_decode w (setReg (System.systemProject js) Register.minstret_increment inc) =
      .ok ast (setReg (System.systemProject js) Register.minstret_increment inc))
    (prog : JoltMonad ExecutionResult)
    (hprog : System.systemProjectResult (prog (preludeJolt js inc pc 4)) =
      execute ast (System.systemProject (preludeJolt js inc pc 4)))
    (hretire : ∀ r s', execute ast (System.systemProject (preludeJolt js inc pc 4)) =
      .ok r s' → r = RETIRE_SUCCESS) :
    System.systemProjectResult (joltStep 4 (zero_extend (m := 32) w) prog js) =
      try_step n false (System.systemProject js) :=
  joltStep_eq_try_step n js 4 _ ast prog inc pc hinc hpc
    (try_step_base n _ hinv inc (should_inc_minstret_systemProject js inc hinc) pc
      (by rw [systemProject_get?_of_not_overlaid js (by simp [Overlaid])]; exact hpc)
      w ast hfetch hdec)
    hprog hretire

/-- A compressed instruction runs as the base instruction it abbreviates: when
`cast` and `base` agree under `executeFull` on every state satisfying the step
invariant, `try_step`'s execute-and-finish part agrees too. For example Sail's
`C_ADDI` executes as `pure (ExecuteAs (ITYPE …))`. -/
theorem executeAndFinish_congr (cast base : instruction) (bits : BitVec 32) (s : SailState)
    (hinv : StepInvariant s)
    (hexec : ∀ s', StepInvariant s' → executeFull cast s' = executeFull base s') :
    executeAndFinish cast bits s = executeAndFinish base bits s := by
  unfold executeAndFinish
  simp only [bind, EStateM.bind]
  rw [hexec s hinv]

/-- **Step theorem, compressed instructions.** On a state satisfying
`StepInvariant`, where `try_step` fetches the parcel `h` and decodes it to the
compressed AST `cast`, which runs as the base AST `base`, one Jolt step running
`prog` projects to `try_step`, provided `prog` agrees with `execute base` after
the prelude (fall-through address two bytes on) and `base` retires. -/
theorem joltStep_compressed (n : Nat) (js : SailJoltState)
    (hinv : StepInvariant (System.systemProject js))
    (inc : Bool) (hinc : should_inc_minstret Privilege.Machine js.sail = .ok inc js.sail)
    (pc : BitVec 64) (hpc : js.sail.regs.get? Register.PC = some pc)
    (h : BitVec 16) (cast base : instruction)
    (hfetch : fetch () (setReg (System.systemProject js) Register.minstret_increment inc) =
      .ok (.F_RVC h) (setReg (System.systemProject js) Register.minstret_increment inc))
    (hdec : ext_decode_compressed h
        (setReg (System.systemProject js) Register.minstret_increment inc) =
      .ok cast (setReg (System.systemProject js) Register.minstret_increment inc))
    (hexec : ∀ s', StepInvariant s' → executeFull cast s' = executeFull base s')
    (prog : JoltMonad ExecutionResult)
    (hprog : System.systemProjectResult (prog (preludeJolt js inc pc 2)) =
      execute base (System.systemProject (preludeJolt js inc pc 2)))
    (hretire : ∀ r s', execute base (System.systemProject (preludeJolt js inc pc 2)) =
      .ok r s' → r = RETIRE_SUCCESS) :
    System.systemProjectResult (joltStep 2 (zero_extend (m := 32) h) prog js) =
      try_step n false (System.systemProject js) := by
  have hpcp : (System.systemProject js).regs.get? Register.PC = some pc := by
    rw [systemProject_get?_of_not_overlaid js (by simp [Overlaid])]; exact hpc
  have hinvp : StepInvariant (preludeState (System.systemProject js) inc pc 2) :=
    (hinv.setReg Register.minstret_increment inc (by simp [invariantReg])).setReg
      Register.nextPC _ (by simp [invariantReg])
  refine joltStep_eq_try_step n js 2 _ base prog inc pc hinc hpc ?_ hprog hretire
  rw [try_step_compressed n _ hinv inc (should_inc_minstret_systemProject js inc hinc) pc hpcp
    h cast hfetch hdec]
  exact executeAndFinish_congr cast base _ _ hinvp hexec

end Step
