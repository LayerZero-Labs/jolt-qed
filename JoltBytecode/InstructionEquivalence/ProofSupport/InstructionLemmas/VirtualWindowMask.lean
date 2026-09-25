import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-! # `VirtualWindowMask*` instruction semantics -/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

theorem virtual_window_mask_b_run_vreg_vreg (vd base : VReg)
    (imm : BitVec 12) (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (JoltISA.Encoded.VirtualWindowMaskB (.vreg vd) (.vreg base) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then
              jolt_virtual_window_mask_b_value (js.vregs base) imm
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_window_mask_b_value (js.vregs base) imm) js hvd

theorem virtual_window_mask_h_run_vreg_vreg (vd base : VReg)
    (imm : BitVec 12) (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (JoltISA.Encoded.VirtualWindowMaskH (.vreg vd) (.vreg base) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then
              jolt_virtual_window_mask_h_value (js.vregs base) imm
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_window_mask_h_value (js.vregs base) imm) js hvd

theorem virtual_window_mask_w_run_vreg_vreg (vd base : VReg)
    (imm : BitVec 12) (js : SailJoltState) (hvd : WritableVReg vd) :
    (execInstr (JoltISA.Encoded.VirtualWindowMaskW (.vreg vd) (.vreg base) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then
              jolt_virtual_window_mask_w_value (js.vregs base) imm
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_window_mask_w_value (js.vregs base) imm) js hvd

theorem virtual_window_mask_b_run_vreg_xreg (vd : VReg) (rs : regidx)
    (imm : BitVec 12) (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (JoltISA.Encoded.VirtualWindowMaskB (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then jolt_virtual_window_mask_b_value x imm else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [hread, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd (jolt_virtual_window_mask_b_value x imm) js hvd

theorem virtual_window_mask_h_run_vreg_xreg (vd : VReg) (rs : regidx)
    (imm : BitVec 12) (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (JoltISA.Encoded.VirtualWindowMaskH (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then jolt_virtual_window_mask_h_value x imm else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [hread, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd (jolt_virtual_window_mask_h_value x imm) js hvd

theorem virtual_window_mask_w_run_vreg_xreg (vd : VReg) (rs : regidx)
    (imm : BitVec 12) (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (JoltISA.Encoded.VirtualWindowMaskW (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then jolt_virtual_window_mask_w_value x imm else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [hread, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd (jolt_virtual_window_mask_w_value x imm) js hvd

end JoltISA

end
