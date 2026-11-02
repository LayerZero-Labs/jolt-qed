import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-! # `VirtualShiftData*` instruction semantics -/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Shift the low byte read from architectural register `rs` into the lane selected
by virtual register `address` plus the 64-bit wrapping immediate `imm`, writing
writable virtual register `vd` and leaving other virtual registers unchanged.
For example, an address value of 7 and immediate 1 select byte lane 0.
Mirrors `VirtualShiftDataB::exec` in `tracer/src/instruction/virtual_shift_data_b.rs`. -/
theorem virtual_shift_data_b_run_vreg_xreg_vreg
    (vd : VReg) (rs : regidx) (address : VReg)
    (imm : BitVec 64)
    (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualShiftDataB (.vreg vd) (.xreg rs) (.vreg address) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then
              jolt_virtual_shift_data_b_value x (js.vregs address + imm)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_shift_data_b_value x (js.vregs address + imm)) js hvd

/-- Shift the low halfword read from architectural register `rs` into the lane
selected by virtual register `address` plus the 64-bit wrapping immediate `imm`,
writing writable virtual register `vd` and leaving other virtual registers unchanged.
For example, an address value of 6 and immediate 2 select halfword lane 0.
Mirrors `VirtualShiftDataH::exec` in `tracer/src/instruction/virtual_shift_data_h.rs`. -/
theorem virtual_shift_data_h_run_vreg_xreg_vreg
    (vd : VReg) (rs : regidx) (address : VReg)
    (imm : BitVec 64)
    (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualShiftDataH (.vreg vd) (.xreg rs) (.vreg address) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then
              jolt_virtual_shift_data_h_value x (js.vregs address + imm)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_shift_data_h_value x (js.vregs address + imm)) js hvd

/-- Shift the low word read from architectural register `rs` into the lane selected
by virtual register `address` plus the 64-bit wrapping immediate `imm`, writing
writable virtual register `vd` and leaving other virtual registers unchanged.
For example, an address value of 4 and immediate 4 select word lane 0.
Mirrors `VirtualShiftDataW::exec` in `tracer/src/instruction/virtual_shift_data_w.rs`. -/
theorem virtual_shift_data_w_run_vreg_xreg_vreg
    (vd : VReg) (rs : regidx) (address : VReg)
    (imm : BitVec 64)
    (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.VirtualShiftDataW (.vreg vd) (.xreg rs) (.vreg address) imm)).run js =
      .ok RETIRE_SUCCESS
        { js with
          vregs := fun r =>
            if r = vd then
              jolt_virtual_shift_data_w_value x (js.vregs address + imm)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_shift_data_w_value x (js.vregs address + imm)) js hvd

end JoltISA

end
