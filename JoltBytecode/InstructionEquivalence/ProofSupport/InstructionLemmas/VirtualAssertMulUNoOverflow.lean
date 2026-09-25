import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# VirtualAssertMulUNoOverflow instruction semantics

Run lemmas for multiplication-overflow Jolt assertions.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Successful real-source unsigned multiplication overflow assertion. -/
theorem virtual_assert_mulu_no_overflow_run_ok (lhs : VReg) (rhs : regidx)
    (js : SailJoltState) (value : BitVec 64)
    (hread : rX_bits rhs js.sail = .ok value js.sail)
    (hguard : (js.vregs lhs).toNat * value.toNat < 2^64) :
    (execInstr (.VirtualAssertMulUNoOverflow (.vreg lhs) (.xreg rhs))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold execInstr readSrc readVReg liftSail
  simp only [mulWide, hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos hguard]
  rfl

/-- Failed real-source unsigned multiplication overflow assertion. -/
theorem virtual_assert_mulu_no_overflow_run_err (lhs : VReg) (rhs : regidx)
    (js : SailJoltState) (value : BitVec 64)
    (hread : rX_bits rhs js.sail = .ok value js.sail)
    (hguard : ¬ ((js.vregs lhs).toNat * value.toNat < 2^64)) :
    (execInstr (.VirtualAssertMulUNoOverflow (.vreg lhs) (.xreg rhs))).run js =
      .error (Error.Assertion "VirtualAssertMulUNoOverflow") js := by
  unfold execInstr readSrc readVReg liftSail
  simp only [mulWide, hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_neg hguard]
  rfl

/-- Successful virtual-source unsigned multiplication overflow assertion. -/
theorem virtual_assert_mulu_no_overflow_v_run_ok (lhs rhs : VReg)
    (js : SailJoltState)
    (hguard : (js.vregs lhs).toNat * (js.vregs rhs).toNat < 2^64) :
    (execInstr (.VirtualAssertMulUNoOverflow (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold execInstr readSrc readVReg
  simp only [mulWide, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos hguard]
  rfl

/-- Failed virtual-source unsigned multiplication overflow assertion. -/
theorem virtual_assert_mulu_no_overflow_v_run_err (lhs rhs : VReg)
    (js : SailJoltState)
    (hguard : ¬ ((js.vregs lhs).toNat * (js.vregs rhs).toNat < 2^64)) :
    (execInstr (.VirtualAssertMulUNoOverflow (.vreg lhs) (.vreg rhs))).run js =
      .error (Error.Assertion "VirtualAssertMulUNoOverflow") js := by
  unfold execInstr readSrc readVReg
  simp only [mulWide, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_neg hguard]
  rfl

end JoltISA

end
