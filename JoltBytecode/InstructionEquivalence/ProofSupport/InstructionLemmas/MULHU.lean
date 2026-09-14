import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# MULHU instruction semantics

Run lemmas for the Jolt ISA `MULHU` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `MULHU` from two real sources to a virtual destination reads both real
sources, writes the unsigned high product, and leaves the Sail state unchanged
when both reads are state-preserving. -/
theorem mulhu_run_vreg_xreg_xreg (vd : VReg) (lhs rhs : regidx)
    (js : SailJoltState) (x y : BitVec 64)
    (h₁ : rX_bits lhs js.sail = .ok x js.sail)
    (h₂ : rX_bits rhs js.sail = .ok y js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.MULHU (.vreg vd) (.xreg lhs) (.xreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_mulhu_value x y else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h₁, h₂, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd (jolt_mulhu_value x y) js hvd


/-- `MULHU` from two real sources to a virtual destination, packaged from a
known base Sail state. -/
theorem exists_state_after_mulhu_run_vreg_xreg_xreg
    (vd : VReg) (lhs rhs : regidx) (js : SailJoltState)
    (s : SailState) (x y : BitVec 64)
    (h_sail : js.sail = s)
    (h_lhs : rX_bits lhs s = .ok x s)
    (h_rhs : rX_bits rhs s = .ok y s)
    (hvd : WritableVReg vd) :
    ∃ js',
      rX_bits lhs js.sail = .ok x js.sail ∧
      rX_bits rhs js.sail = .ok y js.sail ∧
      js'.sail = s ∧
      js'.vregs vd = jolt_mulhu_value x y ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.MULHU (.vreg vd) (.xreg lhs) (.xreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_lhs_current : rX_bits lhs js.sail = .ok x js.sail := by
    simpa only [h_sail] using h_lhs
  have h_rhs_current : rX_bits rhs js.sail = .ok y js.sail := by
    simpa only [h_sail] using h_rhs
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then jolt_mulhu_value x y else js.vregs r }
  refine ⟨js', h_lhs_current, h_rhs_current, ?_, ?_, ?_, ?_⟩
  · exact h_sail
  · simp [js']
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using
      mulhu_run_vreg_xreg_xreg vd lhs rhs js x y h_lhs_current h_rhs_current
        hvd


/-- `MULHU` from a virtual source and a real source to a virtual destination
reads the real source through Sail and writes the unsigned high product. -/
theorem mulhu_run_vreg_vreg_xreg (vd lhs : VReg) (rhs : regidx)
    (js : SailJoltState) (y : BitVec 64)
    (h : rX_bits rhs js.sail = .ok y js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.MULHU (.vreg vd) (.vreg lhs) (.xreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_mulhu_value (js.vregs lhs) y else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd (jolt_mulhu_value (js.vregs lhs) y) js hvd

/-- `MULHU` from a virtual source and a real source to a virtual destination,
packaged from a known virtual-source value and a known base Sail state. -/
theorem exists_state_after_mulhu_run_vreg_vreg_xreg
    (vd lhs : VReg) (rhs : regidx) (js : SailJoltState)
    (s : SailState) (x y : BitVec 64)
    (h_sail : js.sail = s)
    (h_lhs : js.vregs lhs = x)
    (h_rhs : rX_bits rhs s = .ok y s)
    (hvd : WritableVReg vd) :
    ∃ js',
      rX_bits rhs js.sail = .ok y js.sail ∧
      js'.sail = s ∧
      js'.vregs vd = jolt_mulhu_value x y ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.MULHU (.vreg vd) (.vreg lhs) (.xreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_rhs_current : rX_bits rhs js.sail = .ok y js.sail := by
    simpa only [h_sail] using h_rhs
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then jolt_mulhu_value (js.vregs lhs) y else js.vregs r }
  refine ⟨js', h_rhs_current, ?_, ?_, ?_, ?_⟩
  · exact h_sail
  · simp [js', h_lhs]
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using mulhu_run_vreg_vreg_xreg vd lhs rhs js y h_rhs_current hvd

end JoltISA

end
