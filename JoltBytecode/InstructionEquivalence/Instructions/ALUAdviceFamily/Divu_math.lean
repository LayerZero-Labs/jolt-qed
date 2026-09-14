import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Primitives
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Div_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.DivuProgramBlocks

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Math content for `divuProgram` (advice-verified DIVU)

The DIVU counterpart of `Div_math.lean`. Provides:

* The four **honest-advice guard lemmas** —
  `hguard_div0_of_honest_u`, `hguard_no_overflow_of_honest_u`,
  `hguard_q_times_d_le_dividend_of_honest_u`,
  `hguard_rem_bound_of_honest_u` — showing that each assertion's
  guard is satisfied when the oracle returns the honest quotient
  `sail_div_value dividend divisor true`.
* The **uniqueness lemma** `advice_unique_of_guards_u` — used by
  soundness to pin the advice down to the honest value.

DIVU has 4 guards (DIV had 4, DIVW had 5). It needs no `_of_honest`
analogue for `q`-fits-in-32 / `|rem|`-non-neg / signed-rem
reconstruction since DIVU is unsigned-only.

`sail_div_value … true` (with `is_unsigned = true`) is reused from
`Div_math.lean` rather than restated — it's the same Sail function.
-/

-- ----------------------------------------------------------------------------
-- Unsigned Sail/BitVec/Nat helpers
-- ----------------------------------------------------------------------------

private theorem mod65_toNat_mod64_u (x : Int) :
    (x % 36893488147419103232).toNat % 18446744073709551616
      = (x % 18446744073709551616).toNat := by
  apply Int.ofNat.inj
  simp [Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (36893488147419103232 : Int) ≠ 0)),
        Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (18446744073709551616 : Int) ≠ 0))]

private theorem trunc64_eq_intCast_u (x : Int) :
    to_bits_truncate (l := 64) x = (x : BitVec 64) := by
  apply BitVec.eq_of_toFin_eq
  rw [show to_bits_truncate (l := 64) x
        = BitVec.ofNat 64 ((x % 36893488147419103232).toNat) by
        simp [to_bits_truncate, get_slice_int, BitVec.extractLsb']]
  rw [BitVec.toFin_ofNat, BitVec.toFin_intCast]
  ext
  simpa [Fin.ofNat] using mod65_toNat_mod64_u x

/-- `sail_div_value` returns `-1` in the unsigned divide-by-zero case. -/
private theorem sail_div_value_of_zero_u (dividend divisor : BitVec 64)
    (h : divisor = 0#64) :
    sail_div_value dividend divisor true = (-1 : BitVec 64) := by
  subst h
  unfold sail_div_value
  simp [BitVec.toNatInt]
  decide

/-- Outside divide-by-zero, unsigned Sail division agrees with `BitVec.udiv`. -/
theorem sail_div_value_of_normal_u (dividend divisor : BitVec 64)
    (h_ne : divisor ≠ 0#64) :
    sail_div_value dividend divisor true = dividend / divisor := by
  have hdivNat_ne : divisor.toNat ≠ 0 := by
    intro h
    apply h_ne
    apply BitVec.eq_of_toNat_eq
    simp [h]
  unfold sail_div_value
  simp only [show LeanRV64D.Functions.not true = false from rfl,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, BitVec.toNatInt]
  have hbeq_false : ((Int.ofNat divisor.toNat == 0) = false) := by
    change decide (Int.ofNat divisor.toNat = 0) = false
    apply decide_eq_false
    intro h
    exact hdivNat_ne (Int.ofNat_eq_zero.mp h)
  rw [hbeq_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [trunc64_eq_intCast_u]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_intCast, BitVec.toNat_udiv]
  have htdiv :
      (Int.ofNat dividend.toNat).tdiv (Int.ofNat divisor.toNat)
        = (dividend.toNat / divisor.toNat : Nat) := by
    exact (Int.ofNat_tdiv dividend.toNat divisor.toNat).symm
  rw [Int.emod_eq_of_lt]
  · rw [htdiv]
    exact Int.toNat_natCast _
  · rw [htdiv]
    exact_mod_cast Nat.zero_le (dividend.toNat / divisor.toNat)
  · rw [htdiv]
    have hlt : dividend.toNat / divisor.toNat < 2^64 := by
      exact lt_of_le_of_lt (Nat.div_le_self _ _) dividend.isLt
    exact_mod_cast hlt

/-- If a 64-bit product does not overflow unsigned arithmetic, its BitVec
product has the same `toNat` as the mathematical product. -/
private theorem toNat_mul_of_no_overflow_u {x y : BitVec 64}
    (h : x.toNat * y.toNat < 2^64) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

/-- If `y ≤ x` in unsigned value, 64-bit subtraction agrees with Nat subtraction. -/
private theorem toNat_sub_of_le_u {x y : BitVec 64}
    (h : y.toNat ≤ x.toNat) :
    (x - y).toNat = x.toNat - y.toNat := by
  rw [BitVec.toNat_sub]
  have hrepr :
      2^64 - y.toNat + x.toNat = 2^64 + (x.toNat - y.toNat) := by
    omega
  rw [hrepr, Nat.add_mod_left]
  apply Nat.mod_eq_of_lt
  have hx : x.toNat < 2^64 := x.isLt
  omega

/-- A natural number quotient is unique once `q*b` is below `a` and the
leftover is strictly below `b`. -/
private theorem nat_quotient_unique_of_mul_le_and_sub_lt
    {a b q : Nat} (hb : b ≠ 0)
    (hle : q * b ≤ a)
    (hlt : a - q * b < b) :
    q = a / b := by
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  have hq_le : q ≤ a / b := (Nat.le_div_iff_mul_le hbpos).mpr hle
  have hdiv_le : a / b ≤ q := by
    rw [Nat.div_le_iff_le_mul hbpos]
    omega
  omega

-- ----------------------------------------------------------------------------
-- The four honest-advice guard lemmas
-- ----------------------------------------------------------------------------

/-- **Guard 1 — `VirtualAssertValidDiv0`.**

When the divisor is zero, RV64M DIVU specifies `quotient = u64::MAX`
(i.e. `-1` as a `BitVec 64`). Sail's `execute_DIV ... is_unsigned = true`
implements this in the first branch of `sail_div_value`: if
`rs2_int = 0` it returns `-1`. So under honest advice the conjunction
`divisor = 0 ∧ q ≠ -1` is impossible. -/
theorem hguard_div0_of_honest_u (dividend divisor : BitVec 64) :
    ¬ (divisor = 0#64 ∧
       sail_div_value dividend divisor true ≠ (-1 : BitVec 64)) := by
  rintro ⟨hd, hq⟩
  exact hq (sail_div_value_of_zero_u dividend divisor hd)

/-- **Guard 2 — `VirtualAssertMulUNoOverflow`.**

Under honest advice, `q × divisor` does not overflow 64 bits unsigned.
For non-zero divisor `q = ⌊dividend / divisor⌋`, so
`q * divisor ≤ dividend < 2^64`. For zero divisor `q = -1 = u64::MAX`
and the product wraps to `0` — but Sail's `sail_div_value` returns
`-1` directly, so `q.toNat * divisor.toNat = (2^64 - 1) * 0 = 0 < 2^64`. -/
theorem hguard_no_overflow_of_honest_u (dividend divisor : BitVec 64) :
    (sail_div_value dividend divisor true).toNat * divisor.toNat < 2^64 := by
  by_cases hzero : divisor = 0#64
  · rw [hzero]
    simp
  · rw [sail_div_value_of_normal_u dividend divisor hzero, BitVec.toNat_udiv]
    exact lt_of_le_of_lt (Nat.div_mul_le_self dividend.toNat divisor.toNat)
      dividend.isLt

/-- **Guard 3 — `VirtualAssertLTE` (`q × divisor ≤ dividend`).**

The unsigned division identity: for non-zero divisor,
`q = ⌊dividend / divisor⌋` satisfies `q · divisor ≤ dividend`. For
zero divisor, `q = u64::MAX` but `q × 0 = 0 ≤ dividend` trivially. -/
theorem hguard_q_times_d_le_dividend_of_honest_u (dividend divisor : BitVec 64) :
    let q := sail_div_value dividend divisor true
    (q * divisor).toNat ≤ dividend.toNat := by
  intro q
  by_cases hzero : divisor = 0#64
  · have hq : q = -1#64 := sail_div_value_of_zero_u dividend divisor hzero
    rw [hq, hzero]
    simp
  · have hq : q = dividend / divisor := sail_div_value_of_normal_u dividend divisor hzero
    have hprod_lt : (dividend.toNat / divisor.toNat) * divisor.toNat < 2^64 :=
      lt_of_le_of_lt (Nat.div_mul_le_self dividend.toNat divisor.toNat)
        dividend.isLt
    rw [hq, BitVec.toNat_mul, BitVec.toNat_udiv, Nat.mod_eq_of_lt hprod_lt]
    exact Nat.div_mul_le_self dividend.toNat divisor.toNat

/-- **Guard 4 — `VirtualAssertValidUnsignedRemainder`.**

The unsigned remainder `dividend − q*divisor` is strictly less than
the divisor — the standard division identity. The Rust short-circuit
on `divisor = 0` is captured by the left disjunct. -/
theorem hguard_rem_bound_of_honest_u (dividend divisor : BitVec 64) :
    let q := sail_div_value dividend divisor true
    divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat := by
  intro q
  by_cases hzero : divisor = 0#64
  · exact Or.inl hzero
  · right
    have hq : q = dividend / divisor := sail_div_value_of_normal_u dividend divisor hzero
    have hdivNat_ne : divisor.toNat ≠ 0 := by
      intro h
      apply hzero
      apply BitVec.eq_of_toNat_eq
      simp [h]
    have hprod_lt : (dividend.toNat / divisor.toNat) * divisor.toNat < 2^64 :=
      lt_of_le_of_lt (Nat.div_mul_le_self dividend.toNat divisor.toNat)
        dividend.isLt
    have hprod_toNat :
        ((dividend / divisor) * divisor).toNat =
          (dividend.toNat / divisor.toNat) * divisor.toNat := by
      rw [BitVec.toNat_mul, BitVec.toNat_udiv, Nat.mod_eq_of_lt hprod_lt]
    have hprod_le :
        ((dividend / divisor) * divisor).toNat ≤ dividend.toNat := by
      rw [hprod_toNat]
      exact Nat.div_mul_le_self dividend.toNat divisor.toNat
    rw [hq, toNat_sub_of_le_u hprod_le, hprod_toNat]
    rw [Nat.mul_comm (dividend.toNat / divisor.toNat) divisor.toNat,
      ← Nat.mod_eq_sub_mul_div]
    exact Nat.mod_lt dividend.toNat (Nat.pos_of_ne_zero hdivNat_ne)

-- ----------------------------------------------------------------------------
-- Soundness uniqueness
-- ----------------------------------------------------------------------------

/-- **Soundness uniqueness.** If the four guards hold for some advice
`q`, then `q` is the unique honest value `sail_div_value dividend
divisor true`.

DIVU analogue of `advice_unique_of_guards` from `Div_math.lean`, but
with four unsigned guards (DIV's signed product needs `mulhs`-equation,
DIVU's unsigned product needs no-overflow). The proof plan splits on
`divisor = 0` (forces `q = -1` from guard 1) and the normal case
(unsigned uniqueness of truncating quotient with `0 ≤ rem < divisor`,
where `rem := dividend − q × divisor`). -/
theorem advice_unique_of_guards_u
    (dividend divisor q : BitVec 64)
    (h1 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)))
    (h2 : q.toNat * divisor.toNat < 2^64)
    (h3 : (q * divisor).toNat ≤ dividend.toNat)
    (h4 : divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat) :
    q = sail_div_value dividend divisor true := by
  by_cases hzero : divisor = 0#64
  · have hq : q = -1 := by
      by_contra hne
      exact h1 ⟨hzero, hne⟩
    rw [sail_div_value_of_zero_u dividend divisor hzero, hq]
  · have hdivNat_ne : divisor.toNat ≠ 0 := by
      intro h
      apply hzero
      apply BitVec.eq_of_toNat_eq
      simp [h]
    have hprod_toNat : (q * divisor).toNat = q.toNat * divisor.toNat :=
      toNat_mul_of_no_overflow_u h2
    have hprod_le : q.toNat * divisor.toNat ≤ dividend.toNat := by
      rw [← hprod_toNat]
      exact h3
    have hrem_lt : (dividend - q * divisor).toNat < divisor.toNat := by
      rcases h4 with hd | hr
      · exact (hzero hd).elim
      · exact hr
    have hsub_nat :
        dividend.toNat - q.toNat * divisor.toNat < divisor.toNat := by
      rw [← hprod_toNat]
      rw [← toNat_sub_of_le_u h3]
      exact hrem_lt
    have hq_nat : q.toNat = dividend.toNat / divisor.toNat :=
      nat_quotient_unique_of_mul_le_and_sub_lt hdivNat_ne hprod_le hsub_nat
    rw [sail_div_value_of_normal_u dividend divisor hzero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv]
    exact hq_nat

end
