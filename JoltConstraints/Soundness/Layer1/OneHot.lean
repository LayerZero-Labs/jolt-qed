import JoltConstraints.Soundness.Layer0.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

/-- A Boolean sum counts its entries equal to one, in the field. -/
theorem boolean_sum_eq_card {F : Type} [Field F] [DecidableEq F] {ι : Type} [Fintype ι]
    (selector : ι → F) (boolean : ∀ i, selector i * (selector i - 1) = 0) :
    (∑ i, selector i) = ((Finset.univ.filter (fun i => selector i = 1)).card : F) := by
  classical
  calc
    (∑ i, selector i) = ∑ i, if selector i = 1 then (1 : F) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases eq_zero_or_one_of_boolean (boolean i) with zero | one
      · simp [zero]
      · simp [one]
    _ = _ := Finset.sum_boole _ _

/-- Below the characteristic, a Boolean sum of zero has no selected entry. -/
theorem all_zero_of_boolean_sum_zero {F : Type} [Field F] {ι : Type} [Fintype ι]
    (selector : ι → F) (small : Fintype.card ι < ringChar F)
    (boolean : ∀ i, selector i * (selector i - 1) = 0)
    (weight : (∑ i, selector i) = 0) : ∀ i, selector i = 0 := by
  classical
  let selected := Finset.univ.filter (fun i => selector i = 1)
  have bounded : selected.card < ringChar F :=
    lt_of_le_of_lt (Finset.card_filter_le _ _) small
  have count : selected.card = 0 := natCast_injective_below_char bounded
    (by omega) (by simpa only [Nat.cast_zero] using
      (boolean_sum_eq_card selector boolean).symm.trans weight)
  have empty : selected = ∅ := Finset.card_eq_zero.mp count
  intro i
  rcases eq_zero_or_one_of_boolean (boolean i) with zero | one
  · exact zero
  · have member : i ∈ selected := by simp [selected, one]
    rw [empty] at member
    exact False.elim (Finset.notMem_empty i member)

/-- Below the characteristic, a Boolean sum of one selects exactly one entry. -/
theorem existsUnique_of_boolean_sum_one {F : Type} [Field F] {ι : Type} [Fintype ι]
    (selector : ι → F) (small : Fintype.card ι < ringChar F)
    (boolean : ∀ i, selector i * (selector i - 1) = 0)
    (weight : (∑ i, selector i) = 1) : ∃! i, selector i = 1 := by
  classical
  let selected := Finset.univ.filter (fun i => selector i = 1)
  have bounded : selected.card < ringChar F :=
    lt_of_le_of_lt (Finset.card_filter_le _ _) small
  have charNotOne := CharP.ringChar_ne_one (R := F)
  have count : selected.card = 1 := natCast_injective_below_char bounded
    (by omega) (by simpa only [Nat.cast_one] using
      (boolean_sum_eq_card selector boolean).symm.trans weight)
  obtain ⟨chosen, singleton⟩ := Finset.card_eq_one.mp count
  have selected_iff : ∀ i, selector i = 1 ↔ i = chosen := by
    intro i
    have member_iff : i ∈ selected ↔ i = chosen := by simp [singleton]
    simpa [selected] using member_iff
  exact ⟨chosen, (selected_iff chosen).mpr rfl,
    fun i one => (selected_iff i).mp one⟩

/-- A Boolean selector with a unique selected entry is its indicator function. -/
theorem selector_eq_ite {F : Type} [Field F] {ι : Type} [DecidableEq ι]
    (selector : ι → F) (boolean : ∀ i, selector i * (selector i - 1) = 0)
    (chosen : ι) (one : selector chosen = 1)
    (unique : ∀ i, selector i = 1 → i = chosen) :
    ∀ i, selector i = if i = chosen then 1 else 0 := by
  intro i
  by_cases same : i = chosen
  · simp [same, one]
  · rw [if_neg same]
    rcases eq_zero_or_one_of_boolean (boolean i) with zero | isOne
    · exact zero
    · exact False.elim (same (unique i isOne))

/-- A read weighted by a one-hot selector returns the selected value. -/
theorem read_eq_selected {F : Type} [Field F] {ι : Type} [Fintype ι]
    (selector value : ι → F)
    (boolean : ∀ i, selector i * (selector i - 1) = 0)
    (chosen : ι) (one : selector chosen = 1)
    (unique : ∀ i, selector i = 1 → i = chosen) :
    (∑ i, value i * selector i) = value chosen := by
  classical
  simp_rw [selector_eq_ite selector boolean chosen one unique]
  simp

end JoltConstraints.Soundness
