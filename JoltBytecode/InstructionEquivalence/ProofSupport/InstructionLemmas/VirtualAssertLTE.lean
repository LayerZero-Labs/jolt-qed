import JoltBytecode.InstructionEquivalence.ProofSupport.Lemmas

/-!
# VirtualAssertLTE instruction semantics

Run lemmas for unsigned less-than-or-equal Jolt assertions.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Successful real-source unsigned LTE assertion. -/
theorem virtual_assert_lte_real_run_ok (lhs : VReg) (rhs : regidx)
    (js : SailJoltState) (value : BitVec 64)
    (hread : rX_bits rhs js.sail = .ok value js.sail)
    (hguard : (js.vregs lhs).toNat ≤ value.toNat) :
    (execInstr (.VirtualAssertLTE (.vreg lhs) (.xreg rhs))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold execInstr readSrc readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos hguard]
  rfl

/-- Failed real-source unsigned LTE assertion. -/
theorem virtual_assert_lte_real_run_err (lhs : VReg) (rhs : regidx)
    (js : SailJoltState) (value : BitVec 64)
    (hread : rX_bits rhs js.sail = .ok value js.sail)
    (hguard : ¬ ((js.vregs lhs).toNat ≤ value.toNat)) :
    (execInstr (.VirtualAssertLTE (.vreg lhs) (.xreg rhs))).run js =
      .error (Error.Assertion "VirtualAssertLTE") js := by
  unfold execInstr readSrc readVReg liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_neg hguard]
  rfl

/-- Successful virtual-source unsigned LTE assertion. -/
theorem virtual_assert_lte_run_ok (lhs rhs : VReg) (js : SailJoltState)
    (hguard : (js.vregs lhs).toNat ≤ (js.vregs rhs).toNat) :
    (execInstr (.VirtualAssertLTE (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS js := by
  unfold execInstr readSrc readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos hguard]
  rfl

/-- Failed virtual-source unsigned LTE assertion. -/
theorem virtual_assert_lte_run_err (lhs rhs : VReg) (js : SailJoltState)
    (hguard : ¬ ((js.vregs lhs).toNat ≤ (js.vregs rhs).toNat)) :
    (execInstr (.VirtualAssertLTE (.vreg lhs) (.vreg rhs))).run js =
      .error (Error.Assertion "VirtualAssertLTE") js := by
  unfold execInstr readSrc readVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_neg hguard]
  rfl

end JoltISA

end
