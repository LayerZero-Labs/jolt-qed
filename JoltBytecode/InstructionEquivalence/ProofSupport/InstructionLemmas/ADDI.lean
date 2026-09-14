import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

/-!
# ADDI instruction semantics

Run lemmas for the Jolt ISA `ADDI` instruction.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `ADDI` from a real register to a virtual register reads the architectural
source and writes the immediate sum to the virtual destination. -/
theorem addi_run_vreg_xreg (vd : VReg) (rs : regidx)
    (imm : BitVec 12) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hvd : WritableVReg vd) :
    (execInstr (.ADDI (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then x + sign_extend (m := 64) imm else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    hvd, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet]

/-- `ADDI` from a virtual source to a virtual destination leaves Sail unchanged
and writes the immediate sum to the virtual destination. -/
theorem addi_run_vreg_vreg (vd vs : VReg)
    (imm : BitVec 12) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (execInstr (.ADDI (.vreg vd) (.vreg vs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then js.vregs vs + sign_extend (m := 64) imm
              else js.vregs r } := by
  unfold WritableVReg at hvd
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, hvd, ↓reduceIte,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `ADDI` from a virtual source to a real destination writes through Sail. -/
theorem addi_run_xreg_vreg (rd : regidx) (vs : VReg) (imm : BitVec 12)
    (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd (js.vregs vs + sign_extend (m := 64) imm) js.sail = .ok () s') :
    (execInstr (.ADDI (.xreg rd) (.vreg vs) imm)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `ADDI` from a real source to a real destination reads the source through
Sail and writes the immediate sum through Sail. -/
theorem addi_run_xreg_xreg (rd rs1 : regidx) (imm : BitVec 12)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs1 js.sail = .ok x js.sail)
    (hw : wX_bits rd (x + sign_extend (m := 64) imm) js.sail = .ok () s') :
    (execInstr (.ADDI (.xreg rd) (.xreg rs1) imm)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]


/-- Rust's pure-writeback `rd = x0` no-op replacement retires successfully and
leaves the Jolt state unchanged. -/
theorem pureWritebackRdZeroProgram_run (js : SailJoltState) :
    (execProgram pureWritebackRdZeroProgram).run js =
      .ok RETIRE_SUCCESS js := by
  have h_addi_succeeds :
      (execInstr
        (.ADDI (.xreg (regidx.Regidx 0)) (.xreg (regidx.Regidx 0)) (0 : BitVec 12))).run js =
        .ok RETIRE_SUCCESS js := by
    simpa using
      addi_run_xreg_xreg
        (regidx.Regidx 0) (regidx.Regidx 0) (0 : BitVec 12)
        js (0#64) js.sail
        (rX_bits_regidx_zero js.sail)
        (wX_bits_regidx_zero
          (0#64 + sign_extend (m := 64) (0 : BitVec 12)) js.sail)
  unfold pureWritebackRdZeroProgram
  rw [execProgram_instr_run_retire _ _ js js h_addi_succeeds]
  rfl

end JoltISA

end
