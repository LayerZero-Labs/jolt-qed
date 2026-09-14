import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# VirtualAssertValidDiv0 instruction semantics

Run lemmas for the Jolt ISA `VirtualAssertValidDiv0` instructions.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Successful real-divisor div0 assertion leaves the state unchanged. -/
theorem virtual_assert_valid_div0_run_ok (divisor : regidx) (quotient : VReg)
    (js : SailJoltState) (value : BitVec 64)
    (hread : rX_bits divisor js.sail = .ok value js.sail)
    (hguard : ¬ (value = 0#64 ∧ js.vregs quotient ≠ (-1 : BitVec 64))) :
    (execInstr (.VirtualAssertValidDiv0 (.xreg divisor) (.vreg quotient))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold execInstr readSrc readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_neg hguard]
  rfl

/-- Failed real-divisor div0 assertion throws an assertion error. -/
theorem virtual_assert_valid_div0_run_err (divisor : regidx) (quotient : VReg)
    (js : SailJoltState) (value : BitVec 64)
    (hread : rX_bits divisor js.sail = .ok value js.sail)
    (hguard : value = 0#64 ∧ js.vregs quotient ≠ (-1 : BitVec 64)) :
    (execInstr (.VirtualAssertValidDiv0 (.xreg divisor) (.vreg quotient))).run js =
      .error (Error.Assertion "VirtualAssertValidDiv0: divisor = 0 but quotient ≠ -1") js := by
  unfold execInstr readSrc readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos hguard]
  rfl

/-- Successful virtual-divisor div0 assertion leaves the state unchanged. -/
theorem virtual_assert_valid_div0_v_run_ok (divisor quotient : VReg)
    (js : SailJoltState)
    (hguard : ¬ (js.vregs divisor = 0#64 ∧ js.vregs quotient ≠ (-1 : BitVec 64))) :
    (execInstr (.VirtualAssertValidDiv0 (.vreg divisor) (.vreg quotient))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold execInstr readSrc readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_neg hguard]
  rfl

/-- Failed virtual-divisor div0 assertion throws an assertion error. -/
theorem virtual_assert_valid_div0_v_run_err (divisor quotient : VReg)
    (js : SailJoltState)
    (hguard : js.vregs divisor = 0#64 ∧ js.vregs quotient ≠ (-1 : BitVec 64)) :
    (execInstr (.VirtualAssertValidDiv0 (.vreg divisor) (.vreg quotient))).run js =
      .error (Error.Assertion "VirtualAssertValidDiv0: divisor = 0 but quotient ≠ -1") js := by
  unfold execInstr readSrc readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos hguard]
  rfl

end JoltISA

end
