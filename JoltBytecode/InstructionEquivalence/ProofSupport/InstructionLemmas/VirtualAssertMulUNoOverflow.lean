import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

open LeanRV64D

/-!
# VirtualAssertMulUNoOverflow instruction semantics

Run lemmas for multiplication-overflow Jolt assertions.
-/

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions

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
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos (show mulWide _ _ < 2 ^ 64 from hguard)]
  rfl

/-- Failed real-source unsigned multiplication overflow assertion. -/
theorem virtual_assert_mulu_no_overflow_run_err (lhs : VReg) (rhs : regidx)
    (js : SailJoltState) (value : BitVec 64)
    (hread : rX_bits rhs js.sail = .ok value js.sail)
    (hguard : ¬ ((js.vregs lhs).toNat * value.toNat < 2^64)) :
    (execInstr (.VirtualAssertMulUNoOverflow (.vreg lhs) (.xreg rhs))).run js =
      .error (Error.Assertion "VirtualAssertMulUNoOverflow") js := by
  unfold execInstr readSrc readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_neg (show ¬mulWide _ _ < 2 ^ 64 from hguard)]
  rfl

/-- Successful virtual-source unsigned multiplication overflow assertion. -/
theorem virtual_assert_mulu_no_overflow_v_run_ok (lhs rhs : VReg)
    (js : SailJoltState)
    (hguard : (js.vregs lhs).toNat * (js.vregs rhs).toNat < 2^64) :
    (execInstr (.VirtualAssertMulUNoOverflow (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold execInstr readSrc readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos (show mulWide _ _ < 2 ^ 64 from hguard)]
  rfl

/-- Failed virtual-source unsigned multiplication overflow assertion. -/
theorem virtual_assert_mulu_no_overflow_v_run_err (lhs rhs : VReg)
    (js : SailJoltState)
    (hguard : ¬ ((js.vregs lhs).toNat * (js.vregs rhs).toNat < 2^64)) :
    (execInstr (.VirtualAssertMulUNoOverflow (.vreg lhs) (.vreg rhs))).run js =
      .error (Error.Assertion "VirtualAssertMulUNoOverflow") js := by
  unfold execInstr readSrc readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_neg (show ¬mulWide _ _ < 2 ^ 64 from hguard)]
  rfl

end JoltISA

end
