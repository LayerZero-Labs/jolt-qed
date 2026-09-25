import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

/-!
# SLTU instruction semantics

Run lemmas for the Jolt ISA `SLTU` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `SLTU` on virtual sources and a virtual destination reads both virtual
sources and writes the unsigned less-than flag. -/
theorem sltu_run_vreg_vreg_vreg (vd lhs rhs : VReg)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.SLTU (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r => if r = vd then jolt_sltu_value (js.vregs lhs) (js.vregs rhs) else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_sltu_value (js.vregs lhs) (js.vregs rhs)) js hvd


/-- `SLTU` from two virtual sources to a virtual destination, packaged from
known virtual-source values. -/
theorem exists_state_after_sltu_run_vreg_vreg_vreg
    (vd lhs rhs : VReg) (js : SailJoltState) (x y : BitVec 64)
    (h_lhs : js.vregs lhs = x)
    (h_rhs : js.vregs rhs = y)
    (hvd : WritableVReg vd) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd = jolt_sltu_value x y ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.SLTU (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  let js' : SailJoltState :=
    { js with
      vregs := fun r => if r = vd then jolt_sltu_value (js.vregs lhs) (js.vregs rhs)
        else js.vregs r }
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · simp [js', h_lhs, h_rhs]
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using sltu_run_vreg_vreg_vreg vd lhs rhs js hvd

end JoltISA

end
