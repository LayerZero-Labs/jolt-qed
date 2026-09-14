import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# VirtualAssertValidUnsignedRemainder instruction semantics

Run lemmas for unsigned-remainder Jolt assertions.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Successful virtual-register unsigned-remainder assertion leaves state unchanged. -/
theorem virtual_assert_valid_unsigned_remainder_run_ok (remainder divisor : VReg)
    (js : SailJoltState)
    (hguard : js.vregs divisor = 0#64 ∨ (js.vregs remainder).toNat < (js.vregs divisor).toNat) :
    (execInstr (.VirtualAssertValidUnsignedRemainder (.vreg remainder) (.vreg divisor))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold execInstr readSrc readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos hguard]
  rfl

/-- Failed virtual-register unsigned-remainder assertion throws an assertion error. -/
theorem virtual_assert_valid_unsigned_remainder_run_err (remainder divisor : VReg)
    (js : SailJoltState)
    (hguard : ¬ (js.vregs divisor = 0#64 ∨
      (js.vregs remainder).toNat < (js.vregs divisor).toNat)) :
    (execInstr (.VirtualAssertValidUnsignedRemainder (.vreg remainder) (.vreg divisor))).run js =
      .error (Error.Assertion "VirtualAssertValidUnsignedRemainder: r ≥ d ∧ d ≠ 0") js := by
  unfold execInstr readSrc readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_neg hguard]
  rfl

/-- Successful real-divisor unsigned-remainder assertion leaves state unchanged. -/
theorem virtual_assert_valid_unsigned_remainder_real_run_ok
    (remainder : VReg) (divisor : regidx) (js : SailJoltState) (value : BitVec 64)
    (hread : rX_bits divisor js.sail = .ok value js.sail)
    (hguard : value = 0#64 ∨ (js.vregs remainder).toNat < value.toNat) :
    (execInstr (.VirtualAssertValidUnsignedRemainder (.vreg remainder) (.xreg divisor))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold execInstr readSrc readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos hguard]
  rfl

/-- Failed real-divisor unsigned-remainder assertion throws an assertion error. -/
theorem virtual_assert_valid_unsigned_remainder_real_run_err
    (remainder : VReg) (divisor : regidx) (js : SailJoltState) (value : BitVec 64)
    (hread : rX_bits divisor js.sail = .ok value js.sail)
    (hguard : ¬ (value = 0#64 ∨ (js.vregs remainder).toNat < value.toNat)) :
    (execInstr (.VirtualAssertValidUnsignedRemainder (.vreg remainder) (.xreg divisor))).run js =
      .error (Error.Assertion "VirtualAssertValidUnsignedRemainder: r ≥ d ∧ d ≠ 0") js := by
  unfold execInstr readSrc readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_neg hguard]
  rfl

end JoltISA

end
