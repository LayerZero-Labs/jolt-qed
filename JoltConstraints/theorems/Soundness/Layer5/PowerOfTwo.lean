module

import all Init.Data.Nat.Power2.Basic

/-! A small arithmetic fact about Lean's checked-layout round-up. This module
uses `import all` to inspect the core function's private recursive worker. -/

set_option autoImplicit false

public section

namespace JoltConstraints.Soundness

/-- Rounding a natural number up to the next power of two preserves its size. -/
theorem nextPowerOfTwo_ge (n : Nat) : n ≤ n.nextPowerOfTwo := by
  unfold Nat.nextPowerOfTwo
  exact go 1 (by decide)
where
  go (power : Nat) (positive : 0 < power) : n ≤ Nat.nextPowerOfTwo.go n power positive := by
    rw [Nat.nextPowerOfTwo.go]
    split
    · exact go _ _
    · exact Nat.le_of_not_gt ‹¬power < n›
  termination_by n - power
  decreasing_by simp_wf; apply Nat.nextPowerOfTwo_dec <;> assumption

end JoltConstraints.Soundness
