import JoltConstraints.Soundness.Layer3.History
import JoltConstraints.Soundness.Layer1.RamReads

/-! Selection turns RAM history increments into updates of one word. A zero
raw address has no selected word and no effect, even if `RamInc` is nonzero.
The same statements apply at the last cycle, updating `RamValFinal`. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include charAbove2pow127 context equations

private theorem ram_update_of_selected (address : Fin params.ramSize)
    (t : Fin params.traceLength) (chosen : Fin params.ramSize)
    (selected : witness.RamRa chosen t = 1) :
    witness.RamVal address t + witness.RamRa address t * witness.RamInc t =
      if address = chosen then witness.RamWriteValue t else witness.RamVal address t := by
  by_cases same : address = chosen
  · subst address
    rw [selected, one_mul, if_pos rfl]
    exact (ramWriteValue_of_selected charAbove2pow127 context equations t chosen selected).symm
  · rw [if_neg same]
    rcases ramRa_zero_or_one context equations address t with zero | one
    · simp [zero]
    · exact False.elim (same (ramRa_at_most_one charAbove2pow127 context equations
        t address chosen one selected))

/-- An in-domain successor changes only the selected word, to the write value. -/
theorem ramVal_succ_of_selected (address : Fin params.ramSize)
    (t : Fin params.traceLength) (next : t.val + 1 < params.traceLength)
    (chosen : Fin params.ramSize) (selected : witness.RamRa chosen t = 1) :
    witness.RamVal address ⟨t.val + 1, next⟩ =
      if address = chosen then witness.RamWriteValue t else witness.RamVal address t := by
  rw [ramVal_succ equations.ramValEqInitialPlusPrefixRamInc address t next]
  exact ram_update_of_selected charAbove2pow127 context equations address t chosen selected

/-- The final column changes only the last cycle's selected word. -/
theorem ramValFinal_of_selected (address : Fin params.ramSize)
    (t : Fin params.traceLength) (last : t.val + 1 = params.traceLength)
    (chosen : Fin params.ramSize) (selected : witness.RamRa chosen t = 1) :
    witness.RamValFinal address =
      if address = chosen then witness.RamWriteValue t else witness.RamVal address t := by
  rw [ramValFinal_eq_last_update equations.ramValEqInitialPlusPrefixRamInc
    equations.ramValFinalEqInitialPlusRamInc address t last]
  exact ram_update_of_selected charAbove2pow127 context equations address t chosen selected

/-- A zero RAM address leaves every word unchanged at the next cycle. -/
theorem ramVal_succ_of_address_zero (address : Fin params.ramSize)
    (t : Fin params.traceLength) (next : t.val + 1 < params.traceLength)
    (addressZero : witness.RamAddress t = 0) :
    witness.RamVal address ⟨t.val + 1, next⟩ = witness.RamVal address t := by
  rw [ramVal_succ equations.ramValEqInitialPlusPrefixRamInc address t next,
    (ram_zero_effects charAbove2pow127 context equations t addressZero).2.2 address, add_zero]

/-- A zero address at the last cycle leaves the final column unchanged. -/
theorem ramValFinal_of_address_zero (address : Fin params.ramSize)
    (t : Fin params.traceLength) (last : t.val + 1 = params.traceLength)
    (addressZero : witness.RamAddress t = 0) :
    witness.RamValFinal address = witness.RamVal address t := by
  rw [ramValFinal_eq_last_update equations.ramValEqInitialPlusPrefixRamInc
    equations.ramValFinalEqInitialPlusRamInc address t last,
    (ram_zero_effects charAbove2pow127 context equations t addressZero).2.2 address, add_zero]

end JoltConstraints.Soundness
