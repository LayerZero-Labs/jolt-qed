import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# VirtualShiftRightBitmask instruction semantics

Run lemmas for the Jolt ISA `VirtualShiftRightBitmask` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualShiftRightBitmask` from a real source to a virtual destination
materializes the bitmask consumed by `VirtualSRL` and `VirtualSRA`. -/
theorem virtual_shift_right_bitmask_run_vreg_xreg (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualShiftRightBitmask (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_virtual_shift_right_bitmask_value x else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_shift_right_bitmask_value x) js hvd

/-- `VirtualShiftRightBitmask` from a real source to a virtual destination,
packaged as an instruction step. -/
theorem exists_state_after_virtual_shift_right_bitmask_run_vreg_xreg
    (vd : VReg) (rs : regidx) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = js.sail ∧
      js'.vregs vd = jolt_virtual_shift_right_bitmask_value x ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.VirtualShiftRightBitmask (.vreg vd) (.xreg rs))).run js =
        .ok RETIRE_SUCCESS js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r =>
        if r = vd then jolt_virtual_shift_right_bitmask_value x else js.vregs r }
  refine ⟨js', h, rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using virtual_shift_right_bitmask_run_vreg_xreg vd rs js x h hvd

/-- `VirtualShiftRightBitmask` can also read the shift amount from a virtual
register, which is how the word-shift expansions feed masked shift amounts
into `VirtualSRL`/`VirtualSRA`. -/
theorem virtual_shift_right_bitmask_run_vreg_vreg (vd vs : VReg)
    (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (.VirtualShiftRightBitmask (.vreg vd) (.vreg vs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_virtual_shift_right_bitmask_value (js.vregs vs) else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_shift_right_bitmask_value (js.vregs vs)) js hvd



end JoltISA

end
