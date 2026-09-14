import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas

/-!
# `SailJoltState` bookkeeping lemmas

These lemmas are about the virtual-register component of `SailJoltState`.
They are not instruction-specific and do not belong to any instruction
equivalence family.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-- Update one virtual register while leaving the Sail state unchanged. -/
def stateAfterVRegWrite (js : SailJoltState) (vd : JoltISA.VReg)
    (value : BitVec 64) : SailJoltState :=
  { js with
    vregs := fun r => if r = vd then value else js.vregs r }

/-- After writing `v` to vreg `vd`, the lookup at `vd` returns `v`. -/
theorem vregs_write_self (js : SailJoltState) (vd : BitVec 7) (v : BitVec 64) :
    ({ sail := js.sail
       vregs := fun r => if r = vd then v else js.vregs r } : SailJoltState).vregs vd
      = v := by
  show (if vd = vd then v else js.vregs vd) = v
  rw [if_pos rfl]

/-- After writing `v` to vreg `vd`, other vregs are preserved. -/
theorem vregs_write_pres (js : SailJoltState) (vd : BitVec 7) (v : BitVec 64)
    (k : BitVec 7) (h : k ≠ vd) :
    ({ sail := js.sail
       vregs := fun r => if r = vd then v else js.vregs r } : SailJoltState).vregs k
      = js.vregs k := by
  show (if k = vd then v else js.vregs k) = js.vregs k
  rw [if_neg h]

/-- Package a single-virtual-register write into the standard existential
post-state used by straight-line expansion proofs.  From a run that writes
`value` to `vd` (leaving Sail and every other vreg untouched), produce the
post-state together with the `vd`-lookup, preservation, and Sail-unchanged
facts.  Instruction-agnostic: it abstracts over the computation `comp`. -/
theorem writeSingleVReg_ex
    {comp : JoltMonad ExecutionResult} {js : SailJoltState}
    {vd : BitVec 7} {value : BitVec 64}
    (hrun : comp.run js = .ok RETIRE_SUCCESS
      { sail := js.sail
        vregs := fun r => if r = vd then value else js.vregs r }) :
    ∃ js',
      comp.run js = .ok RETIRE_SUCCESS js' ∧
      js'.vregs vd = value ∧
      (∀ k, k ≠ vd → js'.vregs k = js.vregs k) ∧
      js'.sail = js.sail :=
  ⟨_, hrun, vregs_write_self js vd value,
    fun k h => vregs_write_pres js vd value k h, rfl⟩



end
