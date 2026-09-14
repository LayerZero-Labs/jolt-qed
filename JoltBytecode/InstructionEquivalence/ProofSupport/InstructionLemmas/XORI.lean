import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# XORI instruction semantics

Run lemmas for the Jolt ISA `XORI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `XORI` on virtual registers is a pure virtual-register update. -/
theorem execInstr_xori_vreg_vreg_run (vd vs : VReg) (imm : BitVec 12)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.XORI (.vreg vd) (.vreg vs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs vs ^^^ sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (js.vregs vs ^^^ sign_extend (m := 64) imm) js hvd

end JoltISA

end
