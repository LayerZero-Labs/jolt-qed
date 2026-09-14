import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# AND instruction semantics

Run lemmas for the Jolt ISA `AND` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `AND` on virtual registers is a pure virtual-register update. -/
theorem execInstr_and_vreg_vreg_vreg_run (vd lhs rhs : VReg)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.AND (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs lhs &&& js.vregs rhs else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd (js.vregs lhs &&& js.vregs rhs) js hvd

end JoltISA

end
