import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Field.Defs
import JoltConstraints.Constraints.InstructionLookupRa

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Whether Jolt's verifier rejects identity-RAF lookup addresses whose upper
64 bits are all ones (Rust's `CANONICAL_INSTRUCTION_ADDRESS`).
Jolt sets the flag from the `akita` feature, which is also what selects the
128-bit field `p = 2^128 - 1780711455`; the default build uses BN254 and leaves
the check off. The model ties the flag to the field the same way: the check is
on exactly when the characteristic is below `2^128`.
Rust: `crates/jolt-claims/src/protocols/jolt/geometry/instruction.rs`
(`CANONICAL_INSTRUCTION_ADDRESS`) at `c97e9300`; the field is `AkitaField` in
`crates/jolt-akita/src/adapters.rs`. -/
def CanonicalInstructionAddress (F : Type) [Field F] : Prop :=
  ringChar F < 2 ^ 128

/-- 1 when the upper 64 bits of a 128-bit lookup address are all ones, else 0:
the value of Rust's `upper_half_all_ones` at a Boolean address point. For
example, `2^128 - 2^64` gives 1 and `2^128 - 2^64 - 1` gives 0.
Rust: `crates/jolt-claims/src/protocols/jolt/geometry/instruction.rs`
(`upper_half_all_ones`) at `c97e9300`. -/
def upperHalfAllOnes {F : Type} [Field F] (address : Fin (2 ^ 128)) : F :=
  if address.val / 2 ^ 64 = 2 ^ 64 - 1 then 1 else 0

/-- Constraint (63) in `constraints.md`, checked only when
`CanonicalInstructionAddress F` holds:
no identity-RAF cycle selects a lookup address whose upper half is all ones.
Jolt's verifier adds `γ³ · upper_half_all_ones(r_address)` to the `EqRafFlag`
output term, and the input claim has no `γ³` term, so per cycle the weighted
sum below must vanish.
Rust: `crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs#L198-L212`
at `c97e9300`. -/
def instructionAddressCanonical {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  CanonicalInstructionAddress F →
    ∀ t : Fin params.traceLength,
      witness.InstructionRafFlag t *
        ∑ address : Fin (2 ^ 128), instructionLookupRa witness address t *
          upperHalfAllOnes address = 0

/-- An address whose upper half is not all ones lies below `2^128 - 2^64`.
For example, `2^128 - 2^64 - 1` has upper half `2^64 - 2`. -/
theorem lt_of_upperHalfAllOnes_eq_zero {F : Type} [Field F] (address : Fin (2 ^ 128))
    (notAllOnes : (upperHalfAllOnes address : F) = 0) :
    address.val < 2 ^ 128 - 2 ^ 64 := by
  unfold upperHalfAllOnes at notAllOnes
  split at notAllOnes
  · exact absurd notAllOnes one_ne_zero
  · rename_i upper
    have : address.val / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      simp
    by_contra above
    apply upper
    have : 2 ^ 64 - 1 ≤ address.val / 2 ^ 64 := by
      rw [Nat.le_div_iff_mul_le (by positivity)]
      norm_num at above ⊢
      omega
    omega

/-- An address below `2^128 - 2^64` does not have an all-ones upper half. -/
theorem upperHalfAllOnes_eq_zero_of_lt {F : Type} [Field F] (address : Fin (2 ^ 128))
    (below : address.val < 2 ^ 128 - 2 ^ 64) :
    (upperHalfAllOnes address : F) = 0 := by
  unfold upperHalfAllOnes
  split
  · rename_i upper
    have : address.val / 2 ^ 64 < 2 ^ 64 - 1 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      norm_num at below ⊢
      omega
    omega
  · rfl

end JoltConstraints
