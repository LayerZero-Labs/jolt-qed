import JoltConstraints.Soundness.Layer0.Field
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

/-- A product of Boolean entries is one exactly when every entry is one.
This includes an empty product. -/
theorem boolean_prod_eq_one_iff {F : Type} [Field F] {ι : Type} [Fintype ι]
    (entry : ι → F) (boolean : ∀ i, entry i * (entry i - 1) = 0) :
    (∏ i, entry i) = 1 ↔ ∀ i, entry i = 1 := by
  constructor
  · intro selected i
    rcases eq_zero_or_one_of_boolean (boolean i) with zero | one
    · have productZero : (∏ j, entry j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) zero
      exact False.elim (zero_ne_one (productZero.symm.trans selected))
    · exact one
  · intro allOne
    exact Finset.prod_eq_one (fun i _ => allOne i)

/-- A product of Boolean entries is zero or one, including an empty product. -/
theorem boolean_prod_zero_or_one {F : Type} [Field F] {ι : Type} [Fintype ι]
    (entry : ι → F) (boolean : ∀ i, entry i * (entry i - 1) = 0) :
    (∏ i, entry i) = 0 ∨ (∏ i, entry i) = 1 := by
  classical
  by_cases allOne : ∀ i, entry i = 1
  · exact Or.inr ((boolean_prod_eq_one_iff entry boolean).mpr allOne)
  · push_neg at allOne
    obtain ⟨i, notOne⟩ := allOne
    have zero := (eq_zero_or_one_of_boolean (boolean i)).resolve_right notOne
    exact Or.inl (Finset.prod_eq_zero (Finset.mem_univ i) zero)

/-- A Boolean selector that selects at most one entry is either all zero or
selects exactly one entry. No existence of a selected entry is assumed. -/
theorem zero_or_existsUnique_of_boolean {F : Type} [Field F] {ι : Type}
    (selector : ι → F) (boolean : ∀ i, selector i * (selector i - 1) = 0)
    (unique : ∀ a b, selector a = 1 → selector b = 1 → a = b) :
    (∀ i, selector i = 0) ∨ ∃! i, selector i = 1 := by
  classical
  by_cases selected : ∃ i, selector i = 1
  · obtain ⟨chosen, one⟩ := selected
    exact Or.inr ⟨chosen, one, fun i hi => unique i chosen hi one⟩
  · left
    intro i
    exact (eq_zero_or_one_of_boolean (boolean i)).resolve_right
      (fun one => selected ⟨i, one⟩)

end JoltConstraints.Soundness
