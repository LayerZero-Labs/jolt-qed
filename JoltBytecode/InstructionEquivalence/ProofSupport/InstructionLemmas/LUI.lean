import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# LUI instruction semantics

Run lemmas for the Jolt ISA `LUI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Guest `LUI`'s 20-bit immediate, normalized to the 64-bit value written by
the native Jolt instruction. -/
def luiValue (imm : BitVec 20) : BitVec 64 :=
  sign_extend (m := 64) (imm +++ (0x000#12 : BitVec 12))

/-- Execute guest RV64 `LUI` through the native Jolt `LUI` instruction. -/
def execLUI (imm : BitVec 20) (rd : regidx) : JoltMonad ExecutionResult :=
  execInstr (.LUI (.xreg rd) (luiValue imm))

/-- Jolt RV64 `LUI` writes the normalized immediate directly. -/
theorem execInstr_lui_vreg_run (vd : VReg) (imm : BitVec 64)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.LUI (.vreg vd) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then imm else js.vregs r } := by
  unfold execInstr writeDst
  exact writeVReg_retire_run_of_writable vd imm js hvd

end JoltISA

end
