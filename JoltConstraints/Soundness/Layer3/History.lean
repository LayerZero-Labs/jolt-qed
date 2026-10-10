import JoltConstraints.Constraints.RamValEqInitialPlusPrefixRamInc
import JoltConstraints.Constraints.RamValFinalEqInitialPlusRamInc
import JoltConstraints.Soundness.Helpers.PrefixSum

/-! RAM histories for an arbitrary satisfying witness. These lemmas use only
the two history equations, independently of address selection or execution.
The final column includes the last cycle's increment. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {initialRam : Nat → BitVec 64}

/-- Every RAM-table entry starts at the supplied initial image. -/
theorem ramVal_zero (history : ramValEqInitialPlusPrefixRamInc initialRam witness)
    (address : Fin params.ramSize) :
    witness.RamVal address ⟨0, Nat.two_pow_pos _⟩ = ramInitialValue initialRam address.val := by
  rw [history]
  simp

/-- Between in-domain cycles, each word changes by its selector-weighted increment. -/
theorem ramVal_succ (history : ramValEqInitialPlusPrefixRamInc initialRam witness)
    (address : Fin params.ramSize) (t : Fin params.traceLength)
    (next : t.val + 1 < params.traceLength) :
    witness.RamVal address ⟨t.val + 1, next⟩ =
      witness.RamVal address t + witness.RamRa address t * witness.RamInc t := by
  rw [history address ⟨t.val + 1, next⟩, history address t,
    sum_before_succ (fun cycle => witness.RamRa address cycle * witness.RamInc cycle) t,
    add_assoc]

/-- The last cycle updates into `RamValFinal`, even when there is no padding.
This also covers a one-cycle domain. -/
theorem ramValFinal_eq_last_update
    (history : ramValEqInitialPlusPrefixRamInc initialRam witness)
    (finalHistory : ramValFinalEqInitialPlusRamInc initialRam witness)
    (address : Fin params.ramSize) (t : Fin params.traceLength)
    (last : t.val + 1 = params.traceLength) :
    witness.RamValFinal address =
      witness.RamVal address t + witness.RamRa address t * witness.RamInc t := by
  have sum := sum_before_succ (fun cycle => witness.RamRa address cycle * witness.RamInc cycle) t
  have full : ∀ cycle : Fin params.traceLength, cycle.val < t.val + 1 := by
    intro cycle
    rw [last]
    exact cycle.isLt
  simp only [full, if_true] at sum
  rw [finalHistory address, history address t, sum, add_assoc]

/-- If every remaining increment for a word is zero, its current value equals
the final column. Layer 6 must establish this suffix condition for padding. -/
theorem ramVal_eq_final_of_suffix_zero
    (history : ramValEqInitialPlusPrefixRamInc initialRam witness)
    (finalHistory : ramValFinalEqInitialPlusRamInc initialRam witness)
    (address : Fin params.ramSize) (t : Fin params.traceLength)
    (suffixZero : ∀ cycle : Fin params.traceLength, t.val ≤ cycle.val →
      witness.RamRa address cycle * witness.RamInc cycle = 0) :
    witness.RamVal address t = witness.RamValFinal address := by
  rw [history address t, finalHistory address]
  congr 1
  apply Finset.sum_congr rfl
  intro cycle _
  by_cases before : cycle.val < t.val
  · simp only [before, if_true]
  · simp only [before, if_false, suffixZero cycle (by omega)]

end JoltConstraints.Soundness
