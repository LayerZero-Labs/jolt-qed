import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Fin

/-! Prefix-sum identities shared by register and RAM history proofs. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

/-- Extending a strict prefix through index `t` adds exactly the value at `t`.
This also holds at the last index, where the extended prefix is the whole sum. -/
theorem sum_before_succ {M : Type} [AddCommMonoid M] {n : Nat}
    (value : Fin n → M) (t : Fin n) :
    (∑ i : Fin n, if i.val < t.val + 1 then value i else 0) =
      (∑ i : Fin n, if i.val < t.val then value i else 0) + value t := by
  classical
  have split (i : Fin n) :
      (if i.val < t.val + 1 then value i else 0) =
        (if i.val < t.val then value i else 0) + (if i = t then value i else 0) := by
    by_cases before : i.val < t.val
    · have different : i ≠ t := by
        intro same
        subst i
        exact Nat.lt_irrefl _ before
      simp [before, different, Nat.lt_add_one_of_lt before]
    · by_cases same : i = t
      · subst i
        simp
      · have different : i.val ≠ t.val := fun equal => same (Fin.ext equal)
        have after : ¬ i.val < t.val + 1 := by omega
        simp [before, same, after]
  simp_rw [split]
  rw [Finset.sum_add_distrib]
  simp

end JoltConstraints.Soundness
