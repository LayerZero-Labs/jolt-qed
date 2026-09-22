import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# VirtualZeroExtendWord instruction semantics

Run lemmas for the Jolt ISA `VirtualZeroExtendWord` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualZeroExtendWord` from a real source to a virtual destination. -/
theorem virtual_zero_extend_word_run_vreg_xreg (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualZeroExtendWord (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then zero_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd
    (zero_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) js hvd

/-- `VirtualZeroExtendWord` from a real source to a virtual destination,
with the output state chosen by the instruction lemma. -/
theorem exists_state_after_virtual_zero_extend_word_run_vreg_xreg
    (vd : VReg) (rs : regidx) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    ∃ js',
      (execInstr (.VirtualZeroExtendWord (.vreg vd) (.xreg rs))).run js =
        .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = zero_extend (m := 64) (Sail.BitVec.extractLsb x 31 0) ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail := by
  let js' : SailJoltState :=
    { js with
      vregs := fun r =>
        if r = vd then zero_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)
        else js.vregs r }
  refine ⟨js', ?_, ?_, ?_, rfl⟩
  · simpa only [js'] using virtual_zero_extend_word_run_vreg_xreg vd rs js x h hvd
  · show (if vd = vd then _ else js.vregs vd) = _
    rw [if_pos rfl]
  · intro k hk
    show (if k = vd then _ else js.vregs k) = js.vregs k
    rw [if_neg hk]

end JoltISA

end
