import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-! # `VirtualShiftData*` instruction semantics -/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

theorem virtual_shift_data_b_run_vreg_xreg_vreg
    (vd : VReg) (rs : regidx) (address : VReg)
    (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualShiftDataB (.vreg vd) (.xreg rs) (.vreg address))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then
              jolt_virtual_shift_data_b_value x (js.vregs address)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_shift_data_b_value x (js.vregs address)) js hvd

theorem virtual_shift_data_h_run_vreg_xreg_vreg
    (vd : VReg) (rs : regidx) (address : VReg)
    (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualShiftDataH (.vreg vd) (.xreg rs) (.vreg address))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then
              jolt_virtual_shift_data_h_value x (js.vregs address)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_shift_data_h_value x (js.vregs address)) js hvd

theorem virtual_shift_data_w_run_vreg_xreg_vreg
    (vd : VReg) (rs : regidx) (address : VReg)
    (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualShiftDataW (.vreg vd) (.xreg rs) (.vreg address))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then
              jolt_virtual_shift_data_w_value x (js.vregs address)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_shift_data_w_value x (js.vregs address)) js hvd

end JoltISA

end
