import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.SuccPred.Nat
import Batteries.Data.Fin.Fold
import JoltBytecode.MathlibTactics

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The sum over cycles strictly before cycle `n + 1` adds cycle `n` to the
sum strictly before `n`; for example, a prefix of length one contains just cycle zero. -/
theorem prefix_sum_succ
    {F : Type} [Field F] {N : Nat} (f : Fin N → F)
    (n : Nat) (hn : n < N) :
    (∑ i : Fin N, if i.val < n + 1 then f i else 0) =
      (∑ i : Fin N, if i.val < n then f i else 0) + f ⟨n, hn⟩ := by
  classical
  conv_lhs =>
    arg 2
    ext i
    rw [show (if i.val < n + 1 then f i else 0) =
      (if i.val < n then f i else 0) +
        (if i = (⟨n, hn⟩ : Fin N) then f i else 0) by
          by_cases hlt : i.val < n
          · have hneq : i ≠ (⟨n, hn⟩ : Fin N) := by
              intro h
              have hv : i.val = n := by simpa using congrArg Fin.val h
              omega
            simp [hlt, Nat.lt_add_one_of_lt hlt, hneq]
          · by_cases heq : i.val = n
            · have hi : i = ⟨n, hn⟩ := Fin.ext heq
              simp [hi]
            · have hnot : ¬ i.val < n + 1 := by omega
              have hneq : i ≠ (⟨n, hn⟩ : Fin N) := Fin.ne_of_val_ne heq
              simp [hlt, hnot, hneq]]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp


/-- A fold over the first `n` cycles follows any sequence with the same initial
value and transition; for example, a memory replay follows successive state words. -/
theorem prefix_foldl_eq_sequence {α : Type} {N : Nat}
    (step : α → Fin N → α) (state : Nat → α)
    (transition : ∀ i : Fin N, step (state i.val) i = state (i.val + 1))
    (n : Nat) (bound : n ≤ N) :
    (List.finRange n).foldl
      (fun value i => step value ⟨i.val, lt_of_lt_of_le i.isLt bound⟩) (state 0) = state n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Fin.foldl_eq_foldl_finRange, Fin.foldl_succ_last]
    simp only [Fin.val_last, Fin.val_castSucc]
    rw [Fin.foldl_eq_foldl_finRange, ih (by omega)]
    exact transition ⟨n, by omega⟩

/-- A sequence with additive cycle increments equals its initial value plus
its strict prefix sum; for example, cycle three includes increments zero through two. -/
theorem sequence_eq_prefix_sum {F : Type} [Field F] {N : Nat}
    (state : Nat → F) (increment : Fin N → F)
    (transition : ∀ i : Fin N, state (i.val + 1) = state i.val + increment i)
    (n : Nat) (bound : n ≤ N) :
    state n = state 0 + ∑ i : Fin N, if i.val < n then increment i else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [transition ⟨n, by omega⟩, ih (by omega), prefix_sum_succ increment n (by omega)]
    exact add_assoc _ _ _

end JoltConstraints
