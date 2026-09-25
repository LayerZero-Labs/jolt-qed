import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-! # `ANDN` instruction semantics -/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

theorem andn_run_vreg_vreg_vreg (vd lhs rhs : VReg)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.ANDN (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then js.vregs lhs &&& ~~~(js.vregs rhs) else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (js.vregs lhs &&& ~~~(js.vregs rhs)) js hvd

end JoltISA

end
