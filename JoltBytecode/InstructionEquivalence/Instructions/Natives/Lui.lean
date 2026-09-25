import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.NativeDispatch
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas.LUI

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `LUI` equivalence statement. -/
def luiInstrEqSailStatement
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState)
    (_h : NoSourceReadWithLinkedCSRs js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execLUI imm rd).run js) =
    ((execute_UTYPE imm rd uop.LUI).run js.sail)

private abbrev op (imm : BitVec 20) : BitVec 64 :=
  JoltISA.luiValue imm

/-- Native `LUI` writes the normalized immediate in both Jolt and Sail. -/
theorem luiInstr_eq_sail
    (imm : BitVec 20)
    (rd : regidx)
    (js : SailJoltState)
    (h : NoSourceReadWithLinkedCSRs js) :
    luiInstrEqSailStatement imm rd js h := by
  unfold luiInstrEqSailStatement JoltISA.execLUI
  -- Select Rust's no-op for x0; its full state agrees with a discarded write.
  rw [NativeDispatch.pureWriteback_run_eq rd _ js (by
    intro hx0
    have hrd := JoltISA.eq_regidx_zero_of_isX0_eq_true hx0
    subst rd
    simp only [JoltISA.execInstr, JoltISA.readSrc, JoltISA.writeDst, liftSail,
      EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
      wX_bits_regidx_zero])]
  -- RHS
  simp only [execute_UTYPE, EStateM.run, bind, EStateM.bind]
  simp only [pure, EStateM.pure]
  obtain ⟨s', h_write⟩ := wX_shape rd (op imm) js.sail
  have h_write_sail :
      wX_bits rd (sign_extend (m := 64) (imm +++ (0x000#12 : BitVec 12))) js.sail =
        .ok () s' := by
    simpa only [op, JoltISA.luiValue] using h_write
  simp only [h_write_sail]

  -- LHS
  simp only [JoltISA.execInstr, JoltISA.writeDst, liftSail,
    bind, EStateM.bind, h_write]
  exact Projection.systemProjectResult_pure_retire_after_xreg_write rd js s'
    (op imm)
    h.linkedCSRs h_write
end Natives

end
