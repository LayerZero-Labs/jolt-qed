import JoltBytecode.Step.Lift
import JoltBytecode.Step.Frame

/-!
# The step invariant is preserved

`Step.StepInvariant` collects what the step theorems need of the Sail state:
every register present, the hart active in M-mode, `mie = 0`, `mideleg = 0`,
`misa.C = 1` and no landing pad expected. This file proves that a Jolt step
preserves it.

Sail's part of a retiring step writes `minstret_increment` and `nextPC` (the
prelude) and `PC` and `minstret` (the finish); the Jolt rows write only the
registers of `Step.JoltWritable` and Jolt's virtual registers. None of them is
an invariant register.
-/

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

namespace Step

variable {α β : Type}

/-! ## Register frames of Sail computations -/

/-- A successful run of `m` changes only the registers in `W` and keeps every
present register present. -/
structure SailFrame (W : Register → Prop) (m : SailM α) : Prop where
  run : ∀ s a s', m s = .ok a s' →
    (∀ r, ¬ W r → s'.regs.get? r = s.regs.get? r) ∧
    (∀ r, Assumptions.SailRegReadable r s → Assumptions.SailRegReadable r s')

theorem SailFrame.pure {W : Register → Prop} (a : α) : SailFrame W (pure a : SailM α) :=
  ⟨fun s a' s' h => by
    cases h
    exact ⟨fun _ _ => rfl, fun _ h => h⟩⟩

theorem SailFrame.bind {W : Register → Prop} {m : SailM α} {f : α → SailM β}
    (hm : SailFrame W m) (hf : ∀ a, SailFrame W (f a)) : SailFrame W (m >>= f) := by
  constructor
  intro s b s'' h
  have hb : (m >>= f) s = EStateM.bind m f s := rfl
  rw [hb] at h
  simp only [EStateM.bind] at h
  cases hms : m s with
  | error e s1 => rw [hms] at h; cases h
  | ok a s1 =>
    rw [hms] at h
    obtain ⟨k1, p1⟩ := hm.run s a s1 hms
    obtain ⟨k2, p2⟩ := (hf a).run s1 b s'' h
    exact ⟨fun r hr => (k2 r hr).trans (k1 r hr), fun r hr => p2 r (p1 r hr)⟩

theorem SailFrame.ite {W : Register → Prop} {c : Prop} [Decidable c] {m₁ m₂ : SailM α}
    (h₁ : SailFrame W m₁) (h₂ : SailFrame W m₂) : SailFrame W (if c then m₁ else m₂) := by
  split
  · exact h₁
  · exact h₂

theorem SailFrame.andM {W : Register → Prop} {x y : SailM Bool}
    (hx : SailFrame W x) (hy : SailFrame W y) : SailFrame W (x <&&> y) := by
  unfold _root_.andM
  refine SailFrame.bind hx fun b => ?_
  cases b
  · exact SailFrame.pure _
  · exact hy

theorem SailFrame.readReg {W : Register → Prop} (r : Register) :
    SailFrame W (LeanRV64D.readReg r : SailM (RegisterType r)) := by
  constructor
  intro s v s' h
  cases hg : s.regs.get? r with
  | none => rw [readReg_eq_of_get?_none r s hg] at h; cases h
  | some v0 =>
    rw [readReg_eq_of_get? r s v0 hg] at h
    cases h
    exact ⟨fun _ _ => rfl, fun _ h => h⟩

theorem SailFrame.writeReg {W : Register → Prop} {r : Register} (v : RegisterType r)
    (hr : W r) : SailFrame W (LeanRV64D.writeReg r v : SailM Unit) := by
  constructor
  intro s a s' h
  rw [writeReg_run] at h
  cases h
  refine ⟨fun r' hr' => setReg_get?_ne s v (fun he => hr' (he ▸ hr)), fun r' hp => ?_⟩
  by_cases he : r = r'
  · subst he
    exact ⟨v, by simp [setReg]⟩
  · obtain ⟨v', hv'⟩ := hp.exists_value
    exact ⟨v', by rw [setReg_get?_ne s v he]; exact hv'⟩

theorem SailFrame.sail_assert {W : Register → Prop} (b : Bool) (msg : String) :
    SailFrame W (LeanRV64D.sail_assert b msg) := by
  constructor
  intro s a s' h
  cases b
  · cases h
  · cases h
    exact ⟨fun _ _ => rfl, fun _ h => h⟩

/-- Discharge `SailFrame` for a straight-line Sail block whose writes are in
the frame. -/
macro "sail_frame_ok" : tactic =>
  `(tactic| repeat (first
    | exact SailFrame.readReg _
    | exact SailFrame.writeReg _ (by simp)
    | exact SailFrame.sail_assert _ _
    | exact SailFrame.pure _
    | apply SailFrame.andM
    | apply SailFrame.ite
    | apply SailFrame.bind
    | intro _))

/-- The finish of a retiring step writes only `PC` and `minstret`. -/
theorem sailFrame_stepFinish_retire (bits : BitVec 32) :
    SailFrame (fun r => r = Register.PC ∨ r = Register.minstret)
      (stepFinish (.Step_Execute (RETIRE_SUCCESS, bits))) := by
  unfold stepFinish tick_pc
  simp only [RETIRE_SUCCESS, get_config_rvfi, Bool.false_eq_true, ↓reduceIte]
  refine SailFrame.bind (SailFrame.readReg _) fun _ => ?_
  refine SailFrame.bind (SailFrame.sail_assert _ _) fun _ => ?_
  refine SailFrame.bind (SailFrame.readReg _) fun hs => ?_
  cases hs with
  | HART_WAITING _ => exact SailFrame.pure _
  | HART_ACTIVE u =>
    cases u
    sail_frame_ok

/-! ## The invariant under frames -/

theorem invariantReg_hart_state : invariantReg Register.hart_state := Or.inl rfl
theorem invariantReg_cur_privilege : invariantReg Register.cur_privilege := Or.inr (Or.inl rfl)
theorem invariantReg_mie : invariantReg Register.mie := Or.inr (Or.inr (Or.inl rfl))
theorem invariantReg_mideleg : invariantReg Register.mideleg :=
  Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem invariantReg_misa : invariantReg Register.misa :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
theorem invariantReg_elp : invariantReg Register.elp :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- The invariant holds in any state that agrees with an invariant state on
the invariant registers and has every register present. -/
theorem StepInvariant.of_agree {s s' : SailState} (hinv : StepInvariant s)
    (hkeep : ∀ r, invariantReg r → s'.regs.get? r = s.regs.get? r)
    (hpres : ∀ r, Assumptions.SailRegReadable r s') : StepInvariant s' where
  present := hpres
  active := by rw [hkeep _ invariantReg_hart_state]; exact hinv.active
  machine := by rw [hkeep _ invariantReg_cur_privilege]; exact hinv.machine
  mie_zero := by rw [hkeep _ invariantReg_mie]; exact hinv.mie_zero
  mideleg_zero := by rw [hkeep _ invariantReg_mideleg]; exact hinv.mideleg_zero
  misa_c := by rw [hkeep _ invariantReg_misa]; exact hinv.misa_c
  elp_none := by rw [hkeep _ invariantReg_elp]; exact hinv.elp_none

/-- A Sail computation whose frame avoids the invariant registers preserves
the invariant. -/
theorem StepInvariant.of_sailFrame {W : Register → Prop} {m : SailM α}
    (hf : SailFrame W m) (hW : ∀ r, W r → ¬ invariantReg r)
    {s : SailState} (hinv : StepInvariant s) {a : α} {s' : SailState}
    (h : m s = .ok a s') : StepInvariant s' := by
  obtain ⟨hk, hp⟩ := hf.run s a s' h
  exact hinv.of_agree (fun r hr => hk r fun hw => hW r hw hr) (fun r => hp r (hinv.present r))

/-- A retiring finish preserves the invariant. -/
theorem StepInvariant.stepFinish_retire {s : SailState} (hinv : StepInvariant s)
    (bits : BitVec 32) {b : Bool} {s' : SailState}
    (h : stepFinish (.Step_Execute (RETIRE_SUCCESS, bits)) s = .ok b s') :
    StepInvariant s' :=
  StepInvariant.of_sailFrame (sailFrame_stepFinish_retire bits)
    (by rintro r (rfl | rfl) <;> simp [invariantReg]) hinv h

/-- The prelude preserves the invariant. -/
theorem StepInvariant.preludeState {s : SailState} (hinv : StepInvariant s)
    (inc : Bool) (pc : BitVec 64) (len : Int) :
    StepInvariant (preludeState s inc pc len) :=
  (hinv.setReg _ _ (by simp [invariantReg])).setReg _ _ (by simp [invariantReg])

/-! ## A Jolt step preserves the invariant -/

/-- Every overlaid system register is present in the projected state. -/
theorem systemProject_overlaid_present (js : SailJoltState) {r : Register} (hr : Overlaid r) :
    Assumptions.SailRegReadable r (System.systemProject js) := by
  constructor
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [System.systemProject, Std.ExtDHashMap.get?_insert]

theorem not_overlaid_of_invariantReg {r : Register} (hr : invariantReg r) : ¬ Overlaid r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Overlaid]

theorem not_joltWritable_of_invariantReg {r : Register} (hr : invariantReg r) :
    ¬ JoltWritable r := by
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [JoltWritable]

/-- Jolt rows keep the invariant of the projected state: they write no
invariant register and remove no register. -/
theorem StepInvariant.systemProject_regFrame {js js' : SailJoltState}
    (hinv : StepInvariant (System.systemProject js)) (hf : RegFrame js js') :
    StepInvariant (System.systemProject js') := by
  refine hinv.of_agree (fun r hr => ?_) (fun r => ?_)
  · have ho := not_overlaid_of_invariantReg hr
    rw [systemProject_get?_of_not_overlaid js' ho, systemProject_get?_of_not_overlaid js ho,
      hf.keep r (not_joltWritable_of_invariantReg hr)]
  · by_cases ho : Overlaid r
    · exact systemProject_overlaid_present js' ho
    · obtain ⟨v, hv⟩ := (hinv.present r).exists_value
      rw [systemProject_get?_of_not_overlaid js ho] at hv
      obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp (hf.present r (by simp [hv]))
      exact ⟨v', by rw [systemProject_get?_of_not_overlaid js' ho]; exact hv'⟩

/-- **A retiring Jolt step preserves the invariant.** The rows `prog` may be
any Jolt computation with a register frame (every row is, by
`execInstr_regFrame` and `execProgram_regFrame`); the step must retire. -/
theorem joltStep_stepInvariant (len : Int) (bits : BitVec 32) (prog : JoltMonad ExecutionResult)
    (hframe : ∀ js0, RegFrame js0 (resultState (prog js0)))
    (js : SailJoltState) (hinv : StepInvariant (System.systemProject js))
    (inc : Bool) (hinc : should_inc_minstret Privilege.Machine js.sail = .ok inc js.sail)
    (pc : BitVec 64) (hpc : js.sail.regs.get? Register.PC = some pc)
    (hret : ∀ r js1, prog (preludeJolt js inc pc len) = .ok r js1 → r = RETIRE_SUCCESS)
    {b : Bool} {js' : SailJoltState} (h : joltStep len bits prog js = .ok b js') :
    StepInvariant (System.systemProject js') := by
  have hpre : liftSail (stepPrelude len) js = .ok () (preludeJolt js inc pc len) := by
    unfold liftSail
    rw [stepPrelude_run len js.sail inc hinc pc hpc]
    rfl
  have hinv1 : StepInvariant (System.systemProject (preludeJolt js inc pc len)) := by
    rw [systemProject_preludeJolt]
    exact hinv.preludeState inc pc len
  unfold joltStep at h
  simp only [bind, EStateM.bind, hpre] at h
  cases hp : prog (preludeJolt js inc pc len) with
  | error e js1 => rw [hp] at h; cases h
  | ok r js1 =>
    rw [hp] at h
    have hr := hret r js1 hp
    subst hr
    have hf := hframe (preludeJolt js inc pc len)
    rw [hp] at hf
    have hinv2 := hinv1.systemProject_regFrame hf
    have hfin := (overlayLocal_stepFinish_retire bits).run js1
    simp only at h
    rw [h] at hfin
    exact hinv2.stepFinish_retire bits hfin.symm

end Step
