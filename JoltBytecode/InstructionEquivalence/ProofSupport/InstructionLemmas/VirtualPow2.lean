import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# VirtualPow2 instruction semantics

Run lemmas for the Jolt ISA `VirtualPow2` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualPow2` from a real source to a virtual destination writes
`2 ^ rs[5:0]` to the scratch virtual register and leaves Sail unchanged. -/
theorem virtual_pow2_run_vreg_xreg (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualPow2 (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_virtual_pow2_value x else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd (jolt_virtual_pow2_value x) js hvd

/-- `VirtualPow2` from a real source to a virtual destination, packaged as an
instruction step. -/
theorem exists_state_after_virtual_pow2_run_vreg_xreg
    (vd : VReg) (rs : regidx) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = js.sail ∧
      js'.vregs vd = jolt_virtual_pow2_value x ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.VirtualPow2 (.vreg vd) (.xreg rs))).run js =
        .ok RETIRE_SUCCESS js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then jolt_virtual_pow2_value x else js.vregs r }
  refine ⟨js', h, rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using virtual_pow2_run_vreg_xreg vd rs js x h hvd

/-- `VirtualPow2` from a virtual source to a virtual destination writes
`2 ^ source[5:0]` and leaves Sail unchanged. -/
theorem virtual_pow2_run_vreg_vreg (vd vs : VReg)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.VirtualPow2 (.vreg vd) (.vreg vs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_virtual_pow2_value (js.vregs vs) else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd (jolt_virtual_pow2_value (js.vregs vs)) js hvd

end JoltISA

end
