import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.StateLemmas

/-!
# VirtualNegateIf instruction semantics

Run lemmas for the source combinations used by the signed division and
remainder expansions.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualNegateIf` reads two real registers and writes a virtual register. -/
theorem virtual_negate_if_run_vreg_xreg_xreg
    (vd : VReg) (signRs valueRs : regidx)
    (js : SailJoltState) (sign value : BitVec 64)
    (hsign : rX_bits signRs js.sail = .ok sign js.sail)
    (hvalue : rX_bits valueRs js.sail = .ok value js.sail)
    (hvd : WritableVReg vd) :
    (execInstr
      (.VirtualNegateIf (.vreg vd) (.xreg signRs) (.xreg valueRs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_virtual_negate_if_value sign value
            else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [hsign, hvalue, bind, EStateM.bind, EStateM.run]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_negate_if_value sign value) js hvd

/-- Existential single-write form for two real sources. -/
theorem virtual_negate_if_run_vreg_xreg_xreg_ex
    (vd : VReg) (signRs valueRs : regidx)
    (js : SailJoltState) (sign value : BitVec 64)
    (hsign : rX_bits signRs js.sail = .ok sign js.sail)
    (hvalue : rX_bits valueRs js.sail = .ok value js.sail)
    (hvd : WritableVReg vd) :
    ∃ js',
      (execInstr
        (.VirtualNegateIf (.vreg vd) (.xreg signRs) (.xreg valueRs))).run js =
          .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = jolt_virtual_negate_if_value sign value ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      js'.sail = js.sail :=
  writeSingleVReg_ex
    (virtual_negate_if_run_vreg_xreg_xreg vd signRs valueRs js sign value
      hsign hvalue hvd)

/-- `VirtualNegateIf` reads two virtual registers and writes a virtual
register. -/
theorem virtual_negate_if_run_vreg_vreg_vreg
    (vd signVs valueVs : VReg) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    (execInstr
      (.VirtualNegateIf (.vreg vd) (.vreg signVs) (.vreg valueVs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then
              jolt_virtual_negate_if_value
                (js.vregs signVs) (js.vregs valueVs)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  exact writeVReg_retire_run_of_writable vd
    (jolt_virtual_negate_if_value (js.vregs signVs) (js.vregs valueVs)) js hvd

/-- Existential single-write form for two virtual sources. -/
theorem virtual_negate_if_run_vreg_vreg_vreg_ex
    (vd signVs valueVs : VReg) (js : SailJoltState)
    (hvd : WritableVReg vd) :
    ∃ js',
      (execInstr
        (.VirtualNegateIf (.vreg vd) (.vreg signVs) (.vreg valueVs))).run js =
          .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd =
        jolt_virtual_negate_if_value (js.vregs signVs) (js.vregs valueVs) ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      js'.sail = js.sail :=
  writeSingleVReg_ex
    (virtual_negate_if_run_vreg_vreg_vreg vd signVs valueVs js hvd)

/-- `VirtualNegateIf` reads a real sign source and virtual value and writes a
real register. -/
theorem virtual_negate_if_run_xreg_xreg_vreg
    (rd signRs : regidx) (valueVs : VReg)
    (js : SailJoltState) (sign : BitVec 64)
    (hsign : rX_bits signRs js.sail = .ok sign js.sail)
    (s' : SailState)
    (hwrite : wX_bits rd
      (jolt_virtual_negate_if_value sign (js.vregs valueVs)) js.sail =
        .ok () s') :
    (execInstr
      (.VirtualNegateIf (.xreg rd) (.xreg signRs) (.vreg valueVs))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hsign, hwrite, bind, EStateM.bind, pure, EStateM.pure,
    EStateM.run, get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualNegateIf` reads two virtual sources and writes a real register. -/
theorem virtual_negate_if_run_xreg_vreg_vreg
    (rd : regidx) (signVs valueVs : VReg)
    (js : SailJoltState) (s' : SailState)
    (hwrite : wX_bits rd
      (jolt_virtual_negate_if_value
        (js.vregs signVs) (js.vregs valueVs)) js.sail = .ok () s') :
    (execInstr
      (.VirtualNegateIf (.xreg rd) (.vreg signVs) (.vreg valueVs))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hwrite, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

end JoltISA

end
