import JoltBytecode.Inlines.Secp256k1.Advice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Bounds and recombination for Jolt's secp256k1 GLV advice

These proofs concern `rounded_div`, `decompose_scalar` and `decompose_scalar_to_u64s`
in `jolt-inlines/secp256k1/src/glv.rs` at Jolt `a6b6dc717`.
The serialized identity is checked by `decompose_scalar_impl` in
`jolt-inlines/secp256k1/src/sdk.rs` at that same commit.
-/

set_option autoImplicit false

namespace JoltISA.Inlines.Secp256k1

/-- Rounding error of `roundedDiv` for a nonnegative numerator: `n·β - k·c` is at most
`n/2` in absolute value.
Example: `roundedDiv 5 1 3 = 2` has error `1`, and `2 ≤ 3`. -/
theorem roundedDiv_error (k c r : Int) (hk : 0 ≤ k) (hc : 0 ≤ c) (hr : 0 < r) :
    2 * |r * roundedDiv k c r - k * c| ≤ r := by
  have hp := mul_nonneg hk hc
  have hrem0 := Int.tmod_nonneg r hp
  have hrem1 := Int.tmod_lt_of_pos (k * c) hr
  have hdiv := Int.mul_tdiv_add_tmod (k * c) r
  unfold roundedDiv
  dsimp only
  split_ifs with h
  · rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  · rw [abs_of_nonpos (by nlinarith)]
    nlinarith

/-- The GLV split recombines modulo `n`, for every integer `k`.
Example: the split of `1` is `(1, 0)`, which recombines to `1`. -/
theorem glvSplit_recombines (k : Int) :
    ((glvSplit k).1 + (glvLambda : Int) * (glvSplit k).2 - k) % (n : Int) = 0 := by
  have hb : glvB1 ≤ n := by norm_num [glvB1, n]
  have hd1 : (n : Int) ∣ (glvA1 : Int) - (glvLambda : Int) * (glvB1 : Int) := by
    have hd := (Nat.dvd_of_mod_eq_zero glv_lattice.1)
    have hc : (n : Int) ∣ (glvA1 : Int) + (glvLambda : Int) * ((n : Int) - (glvB1 : Int)) := by
      have hc0 : (n : Int) ∣ ((glvA1 + glvLambda * (n - glvB1) : Nat) : Int) := by
        exact_mod_cast hd
      simpa only [Int.natCast_add, Int.natCast_mul, Int.natCast_sub hb] using hc0
    convert dvd_sub hc (dvd_mul_left (n : Int) (glvLambda : Int)) using 1 <;> ring
  have hd2 : (n : Int) ∣ (glvA2 : Int) + (glvLambda : Int) * (glvA1 : Int) := by
    exact_mod_cast Nat.dvd_of_mod_eq_zero glv_lattice.2.1
  apply Int.emod_eq_zero_of_dvd
  have heq : (glvSplit k).1 + (glvLambda : Int) * (glvSplit k).2 - k =
      -roundedDiv k glvA1 n * ((glvA1 : Int) - (glvLambda : Int) * glvB1) -
      roundedDiv k glvB1 n * ((glvA2 : Int) + (glvLambda : Int) * glvA1) := by
    dsimp [glvSplit]
    ring
  rw [heq]
  exact dvd_sub (dvd_mul_of_dvd_right hd1 _) (dvd_mul_of_dvd_right hd2 _)

/-- A weighted sum of two errors of size at most `r/2`, divided by positive `r`,
has twice its absolute value at most the sum of its nonnegative weights.
Example: `r = 2`, `e = f = 1`, `a = b = 3` gives `x = 3` and bound `6`. -/
private theorem weighted_error_bound (r x e f a b : Int)
    (hr : 0 < r) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : 2 * |e| ≤ r) (hf : 2 * |f| ≤ r) (hx : r * x = e * a + f * b) :
    2 * |x| ≤ a + b := by
  have ht : r * |x| ≤ |e| * a + |f| * b := by
    calc
      r * |x| = |r * x| := by rw [abs_mul, abs_of_pos hr]
      _ = |e * a + f * b| := congrArg abs hx
      _ ≤ |e * a| + |f * b| := abs_add_le _ _
      _ = |e| * a + |f| * b := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hea := mul_le_mul_of_nonneg_right he ha
  have hfb := mul_le_mul_of_nonneg_right hf hb
  apply le_of_mul_le_mul_left _ hr
  nlinarith only [ht, hea, hfb]

/-- The analytic bound: for `0 ≤ k < n`, `|k1| ≤ (a1 + a2)/2` and `|k2| ≤ (b1 + a1)/2`.
The same bound holds for every nonnegative `k`.
Example: the split of `0` has both coordinates zero. -/
theorem glvSplit_bound (k : Int) (h0 : 0 ≤ k) :
    2 * |(glvSplit k).1| ≤ (glvA1 + glvA2 : Int) ∧ 2 * |(glvSplit k).2| ≤ (glvB1 + glvA1 : Int) := by
  have hr : (0 : Int) < n := by norm_num [n]
  have ha : (0 : Int) ≤ glvA1 := Int.natCast_nonneg _
  have hb : (0 : Int) ≤ glvB1 := Int.natCast_nonneg _
  have hc : (0 : Int) ≤ glvA2 := Int.natCast_nonneg _
  have hd : (glvA1 : Int) ^ 2 + (glvB1 : Int) * (glvA2 : Int) = n := by
    exact_mod_cast glv_lattice.2.2.1
  have he := roundedDiv_error k glvA1 n h0 ha hr
  have hf := roundedDiv_error k glvB1 n h0 hb hr
  dsimp only [glvSplit]
  generalize roundedDiv k glvA1 n = u at *
  generalize roundedDiv k glvB1 n = v at *
  generalize (glvA1 : Int) = a at *
  generalize (glvB1 : Int) = b at *
  generalize (glvA2 : Int) = c at *
  generalize (n : Int) = r at *
  constructor
  · apply weighted_error_bound r _ (-(r * u - k * a)) (-(r * v - k * b)) a c hr ha hc
    · simpa only [abs_neg] using he
    · simpa only [abs_neg] using hf
    · calc
        r * (k - u * a - v * c) =
            k * (r - (a ^ 2 + b * c)) + (-(r * u - k * a) * a + -(r * v - k * b) * c) := by ring
        _ = _ := by rw [hd]; ring
  · apply weighted_error_bound r _ (r * u - k * a) (-(r * v - k * b)) b a hr hb ha
    · exact he
    · simpa only [abs_neg] using hf
    · ring

/-- Both halves are below `2^128` in absolute value.
Example: splitting `1` gives magnitudes `1` and `0`. -/
theorem glvSplit_small (k : Int) (h0 : 0 ≤ k) :
    (glvSplit k).1.natAbs < 2 ^ 128 ∧ (glvSplit k).2.natAbs < 2 ^ 128 := by
  obtain ⟨h1, h2⟩ := glvSplit_bound k h0
  rw [← Int.natCast_natAbs] at h1 h2
  have h1n : 2 * (glvSplit k).1.natAbs ≤ glvA1 + glvA2 := by exact_mod_cast h1
  have h2n : 2 * (glvSplit k).2.natAbs ≤ glvB1 + glvA1 := by exact_mod_cast h2
  obtain ⟨hb1, hb2⟩ := glv_lattice.2.2.2
  constructor <;> omega

/-- For a nonnegative scalar `to_sign_abs` does not truncate: the sign bit and magnitude
of `decomposeScalar k` give back the untruncated split.
Example: `decomposeScalar 1 = ((false, 1), (false, 0))`. -/
theorem decomposeScalar_exact (k : Int) (h0 : 0 ≤ k) :
    (decomposeScalar k).1.2 = (glvSplit k).1.natAbs ∧
    (decomposeScalar k).2.2 = (glvSplit k).2.natAbs ∧
    (decomposeScalar k).1.1 = decide ((glvSplit k).1 < 0) ∧
    (decomposeScalar k).2.1 = decide ((glvSplit k).2 < 0) := by
  obtain ⟨h1, h2⟩ := glvSplit_small k h0
  simp only [decomposeScalar, toSignAbs, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    and_self]

/-- The signed value of a sign-and-magnitude pair: `-m` when the sign bit is set.
Example: `signedOf (true, 3) = -3`. -/
def signedOf (sm : Bool × Nat) : Int := if sm.1 then -(sm.2 : Int) else (sm.2 : Int)

/-- Recovering an integer from its sign and its untruncated natural magnitude is exact.
Example: the sign and magnitude of `-3` recover `-3`. -/
private theorem signedOf_natAbs (x : Int) : signedOf (decide (x < 0), x.natAbs) = x := by
  unfold signedOf
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [Int.natCast_natAbs, abs_of_neg h, neg_neg]
  · rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]

/-- The identity the SDK checks (`sdk.rs:781-783`): `k ≡ ±k1 ± λ·k2 (mod n)` with the
serialized signs and magnitudes, and both magnitudes below `2^128`.
Example: the serialized split of `1` recombines as `1 + λ·0`. -/
theorem decomposeScalar_correct (k : Int) (h0 : 0 ≤ k) :
    (signedOf (decomposeScalar k).1 + (glvLambda : Int) * signedOf (decomposeScalar k).2 - k)
        % (n : Int) = 0 ∧
    (decomposeScalar k).1.2 < 2 ^ 128 ∧ (decomposeScalar k).2.2 < 2 ^ 128 := by
  obtain ⟨hm1, hm2, hs1, hs2⟩ := decomposeScalar_exact k h0
  have hd1 : (decomposeScalar k).1 = (decide ((glvSplit k).1 < 0), (glvSplit k).1.natAbs) :=
    Prod.ext hs1 hm1
  have hd2 : (decomposeScalar k).2 = (decide ((glvSplit k).2 < 0), (glvSplit k).2.natAbs) :=
    Prod.ext hs2 hm2
  rw [hd1, hd2, signedOf_natAbs, signedOf_natAbs]
  exact ⟨glvSplit_recombines k, glvSplit_small k h0⟩

/-- Two little-endian 64-bit words recover any magnitude below `2^128`.
Example: magnitude `2^64 + 3` has low word `3` and high word `1`. -/
private theorem magnitude_words_exact (m : Nat) (hm : m < 2 ^ 128) :
    (BitVec.ofNat 64 m).toNat + 2 ^ 64 * (BitVec.ofNat 64 (m / 2 ^ 64)).toNat = m := by
  have hhi : m / 2 ^ 64 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhi]
  exact Nat.mod_add_div m (2 ^ 64)

/-- Serializing one sign-and-magnitude pair gives a binary sign word and preserves its
signed value when the magnitude is below `2^128`.
Example: `(true, 3)` serializes to sign word `1` and magnitude words `3, 0`. -/
private theorem signed_words_exact (sm : Bool × Nat) (hm : sm.2 < 2 ^ 128) :
    ((BitVec.ofNat 64 sm.1.toNat).toNat = 0 ∨ (BitVec.ofNat 64 sm.1.toNat).toNat = 1) ∧
    (if (BitVec.ofNat 64 sm.1.toNat).toNat = 1 then -1 else 1) *
      (( (BitVec.ofNat 64 sm.2).toNat +
        2 ^ 64 * (BitVec.ofNat 64 (sm.2 / 2 ^ 64)).toNat : Nat) : Int) = signedOf sm := by
  rw [magnitude_words_exact sm.2 hm]
  cases hs : sm.1 <;> simp [signedOf, hs]

/-- The six words: sign words are `0` or `1`, the magnitudes are `lo + 2^64·hi`, and the
words recombine to `k mod n`.
Example: `decomposeScalarToU64s 1 = #v[0, 1, 0, 0, 0, 0]`. -/
theorem decomposeScalarToU64s_correct (k : Int) (h0 : 0 ≤ k) :
    let v := decomposeScalarToU64s k
    (v[0].toNat = 0 ∨ v[0].toNat = 1) ∧ (v[3].toNat = 0 ∨ v[3].toNat = 1) ∧
    ((if v[0].toNat = 1 then -1 else 1) * ((v[1].toNat + 2 ^ 64 * v[2].toNat : Nat) : Int) +
      (glvLambda : Int) *
        ((if v[3].toNat = 1 then -1 else 1) * ((v[4].toNat + 2 ^ 64 * v[5].toNat : Nat) : Int))
      - k) % (n : Int) = 0 := by
  obtain ⟨hr, hm1, hm2⟩ := decomposeScalar_correct k h0
  obtain ⟨hs1, hv1⟩ := signed_words_exact (decomposeScalar k).1 hm1
  obtain ⟨hs2, hv2⟩ := signed_words_exact (decomposeScalar k).2 hm2
  intro v
  have e0 : v[0] = BitVec.ofNat 64 (decomposeScalar k).1.1.toNat := rfl
  have e1 : v[1] = BitVec.ofNat 64 (decomposeScalar k).1.2 := rfl
  have e2 : v[2] = BitVec.ofNat 64 ((decomposeScalar k).1.2 / 2 ^ 64) := rfl
  have e3 : v[3] = BitVec.ofNat 64 (decomposeScalar k).2.1.toNat := rfl
  have e4 : v[4] = BitVec.ofNat 64 (decomposeScalar k).2.2 := rfl
  have e5 : v[5] = BitVec.ofNat 64 ((decomposeScalar k).2.2 / 2 ^ 64) := rfl
  simp only [e0, e1, e2, e3, e4, e5]
  exact ⟨hs1, hs2, by rw [hv1, hv2]; exact hr⟩

end JoltISA.Inlines.Secp256k1
