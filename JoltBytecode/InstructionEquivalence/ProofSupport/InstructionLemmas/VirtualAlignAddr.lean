import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-! # `VirtualAlignAddr` instruction semantics -/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualAlignAddr` reads an architectural base and writes the containing
aligned dword address to a virtual destination. -/
theorem virtual_align_addr_run_vreg_xreg (vd : VReg) (rs : regidx)
    (imm : BitVec 12) (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualAlignAddr (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_virtual_align_addr_value x imm else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [hread, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd (jolt_virtual_align_addr_value x imm) js hvd

end JoltISA

end
