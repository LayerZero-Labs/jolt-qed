import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# ORI instruction semantics

Run lemmas for the Jolt ISA `ORI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `ORI` from a real source to a virtual destination sets the immediate bits
in the source value and leaves Sail unchanged. -/
theorem ori_run_vreg_xreg (vd : VReg) (rs : regidx) (imm : BitVec 12)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (JoltISA.Encoded.ORI (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r => if r = vd then x ||| sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd
    (x ||| sign_extend (m := 64) imm) js hvd

/-- `ORI` from a real source to a virtual destination, packaged as an
instruction step from a known unchanged Sail state. -/
theorem exists_state_after_ori_run_vreg_xreg_of_sail_eq
    (vd : VReg) (rs : regidx) (imm : BitVec 12)
    (js : SailJoltState) (s : SailState) (x : BitVec 64)
    (h_sail : js.sail = s)
    (h_read : rX_bits rs s = .ok x s)
    (hvd : WritableVReg vd) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = js.sail ∧
      js'.vregs vd = x ||| sign_extend (m := 64) imm ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (JoltISA.Encoded.ORI (.vreg vd) (.xreg rs) imm)).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_read_current : rX_bits rs js.sail = .ok x js.sail := by
    simpa only [h_sail] using h_read
  let js' : SailJoltState :=
    { js with
      vregs := fun r =>
        if r = vd then x ||| sign_extend (m := 64) imm else js.vregs r }
  refine ⟨js', h_read_current, rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using ori_run_vreg_xreg vd rs imm js x h_read_current hvd


end JoltISA

end
