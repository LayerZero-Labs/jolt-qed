import JoltConstraints.Constraints.LookupOutputEqInstructionReadRaf

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Deinterleave the left operand: odd bit positions counted from the least
significant bit. Equivalently, use even positions in the MSB-first bit vector.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs#L181-L201 -/
noncomputable def lookupAddressLeft {F : Type} [Field F] (address : Fin (2 ^ 128)) : F :=
  ∑ bit : Fin 64, if address.val.testBit (2 * bit.val + 1) then (2 : F) ^ bit.val else 0

/-- Deinterleave the right operand: even bit positions counted from the least
significant bit. The identity RAF instead uses the entire 128-bit address. -/
noncomputable def lookupAddressRight {F : Type} [Field F] (address : Fin (2 ^ 128)) : F :=
  ∑ bit : Fin 64, if address.val.testBit (2 * bit.val) then (2 : F) ^ bit.val else 0

/-- The low `k` bit pairs of `HonestWitness.interleaveLookupOperands`. -/
private def interleavePrefix (left right : BitVec 64) (k : Nat) : Nat :=
  (List.range k).foldl (fun address bit =>
    address + (if left.getLsbD bit then 2 ^ (2 * bit + 1) else 0) +
      (if right.getLsbD bit then 2 ^ (2 * bit) else 0)) 0

private theorem interleavePrefix_succ (left right : BitVec 64) (k : Nat) :
    interleavePrefix left right (k + 1) =
      2 ^ (2 * k) * ((if left.getLsbD k then 2 else 0) + (if right.getLsbD k then 1 else 0)) +
        interleavePrefix left right k := by
  unfold interleavePrefix
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  split_ifs <;> ring

private theorem interleavePrefix_spec (left right : BitVec 64) (k : Nat) :
    interleavePrefix left right k < 2 ^ (2 * k) ∧
      ∀ j < 2 * k, (interleavePrefix left right k).testBit j =
        if j % 2 = 1 then left.getLsbD (j / 2) else right.getLsbD (j / 2) := by
  induction k with
  | zero => simp [interleavePrefix]
  | succ k ih =>
    obtain ⟨hlt, hbits⟩ := ih
    rw [interleavePrefix_succ]
    have hpow : 2 ^ (2 * (k + 1)) = 2 ^ (2 * k) * 4 := by ring
    refine ⟨?_, ?_⟩
    · rw [hpow]
      split_ifs <;> omega
    · intro j hj
      rw [Nat.testBit_two_pow_mul_add _ hlt]
      by_cases hjk : j < 2 * k
      · simp only [hjk, ↓reduceIte]
        exact hbits j hjk
      · simp only [hjk, ↓reduceIte]
        -- The new pair holds `right` at bit 2k and `left` at bit 2k + 1.
        obtain rfl | rfl : j = 2 * k ∨ j = 2 * k + 1 := by omega
        · have h1 : 2 * k % 2 = 0 := by omega
          have h2 : 2 * k / 2 = k := by omega
          simp only [Nat.sub_self, h1, h2]
          cases left.getLsbD k <;> cases right.getLsbD k <;> decide
        · have h1 : (2 * k + 1) % 2 = 1 := by omega
          have h2 : (2 * k + 1) / 2 = k := by omega
          have h3 : 2 * k + 1 - 2 * k = 1 := by omega
          simp only [h1, h2, h3, ↓reduceIte]
          cases left.getLsbD k <;> cases right.getLsbD k <;> decide

/-- Bit `j` of an interleaved lookup index: odd positions hold `left`, even positions `right`. -/
theorem interleaveLookupOperands_testBit (left right : BitVec 64) {j : Nat} (hj : j < 128) :
    (HonestWitness.interleaveLookupOperands left right).toNat.testBit j =
      if j % 2 = 1 then left.getLsbD (j / 2) else right.getLsbD (j / 2) := by
  have hspec := interleavePrefix_spec left right 64
  change (BitVec.ofNat 128 (interleavePrefix left right 64)).toNat.testBit j = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hspec.1]
  exact hspec.2 j hj

/-- The low `k` bits of `x`, summed as powers of two. -/
theorem sum_testBit_eq_mod (x k : Nat) :
    (∑ i ∈ Finset.range k, if x.testBit i then 2 ^ i else 0) = x % 2 ^ k := by
  induction k with
  | zero => rw [Finset.sum_range_zero, Nat.pow_zero, Nat.mod_one]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h | h <;> simp [h]

/-- A 64-bit value cast into `F` is the sum of its set bits. -/
theorem bitVec_toNat_cast_eq_sum {F : Type} [Field F] (x : BitVec 64) :
    ((x.toNat : Nat) : F) =
      ∑ bit : Fin 64, if x.getLsbD bit.val then (2 : F) ^ bit.val else 0 := by
  have hsum := sum_testBit_eq_mod x.toNat 64
  rw [Nat.mod_eq_of_lt x.isLt] at hsum
  rw [← hsum, Fin.sum_univ_eq_sum_range (fun i => if x.getLsbD i then (2 : F) ^ i else 0)]
  push_cast [Nat.cast_sum, Nat.cast_ite]
  rfl

/-- Deinterleaving the odd bits of an interleaved index recovers its left operand. -/
theorem sum_interleave_odd_bits {F : Type} [Field F] (left right : BitVec 64) :
    (∑ bit : Fin 64,
      if (HonestWitness.interleaveLookupOperands left right).toNat.testBit (2 * bit.val + 1)
      then (2 : F) ^ bit.val else 0) = (left.toNat : F) := by
  rw [bitVec_toNat_cast_eq_sum]
  refine Finset.sum_congr rfl fun bit _ => ?_
  have hj : 2 * bit.val + 1 < 128 := by omega
  have h1 : (2 * bit.val + 1) % 2 = 1 := by omega
  have h2 : (2 * bit.val + 1) / 2 = bit.val := by omega
  simp only [interleaveLookupOperands_testBit left right hj, h1, h2, ↓reduceIte]

/-- Deinterleaving the even bits of an interleaved index recovers its right operand. -/
theorem sum_interleave_even_bits {F : Type} [Field F] (left right : BitVec 64) :
    (∑ bit : Fin 64,
      if (HonestWitness.interleaveLookupOperands left right).toNat.testBit (2 * bit.val)
      then (2 : F) ^ bit.val else 0) = (right.toNat : F) := by
  rw [bitVec_toNat_cast_eq_sum]
  refine Finset.sum_congr rfl fun bit _ => ?_
  have hj : 2 * bit.val < 128 := by omega
  have h1 : 2 * bit.val % 2 = 0 := by omega
  have h2 : 2 * bit.val / 2 = bit.val := by omega
  simp only [interleaveLookupOperands_testBit left right hj, h1, h2, Nat.zero_ne_one,
    ↓reduceIte]

end JoltConstraints
