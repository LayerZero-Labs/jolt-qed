import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.StateLemmas

/-!
# VirtualAdvice instruction semantics

Run lemmas for the Jolt ISA `VirtualAdvice` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualAdvice` writes the supplied advice value into a virtual register. -/
theorem virtual_advice_run (vd : VReg) (advice : BitVec 64) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualAdvice (.vreg vd) advice)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then advice else js.vregs r } := by
  unfold execInstr
  exact writeVReg_retire_run_of_writable vd advice js hvd




/-- Existential single-write post-state for `VirtualAdvice`. -/
theorem virtual_advice_run_ex (vd : VReg) (advice : BitVec 64) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    ∃ js',
      (execInstr (.VirtualAdvice (.vreg vd) advice)).run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = advice ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail :=
  writeSingleVReg_ex (virtual_advice_run vd advice js hvd)

end JoltISA

end
