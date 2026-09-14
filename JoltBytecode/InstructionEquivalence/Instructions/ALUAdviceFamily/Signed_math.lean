import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divu_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Remu_math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Arithmetic for the one-advice signed DIV/REM expansions

Rust verifies signed division by reducing it to unsigned division of operand
magnitudes. These lemmas connect that construction to the existing unsigned
guard proofs.
-/

/-- Magnitude of a quotient represented with the sign convention used by the
Rust `DIV` expansion. -/
def signedQuotientMagnitude
    (dividend divisor quotient : BitVec 64) : BitVec 64 :=
  jolt_virtual_negate_if_value (dividend ^^^ divisor) quotient

theorem bv_abs_ne_zero {x : BitVec 64} (h : x ≠ 0#64) :
    bv_abs x ≠ 0#64 := by
  unfold bv_abs
  by_cases hsign : x.msb = true
  · rw [if_pos hsign]
    exact fun hneg => h (BitVec.neg_eq_zero_iff.mp hneg)
  · rw [if_neg hsign]
    exact h

theorem bv_abs_neg (x : BitVec 64) : bv_abs (-x) = bv_abs x := by
  by_cases hzero : x = 0#64
  · simp [hzero, bv_abs]
  by_cases hmin : x = BitVec.intMin 64
  · simp [hmin, bv_abs]
  have hneg := BitVec.msb_neg_of_ne_intMin_of_ne_zero hmin hzero
  unfold bv_abs
  by_cases hx : x.msb = true
  · have hn : (-x).msb = false := by simp [hneg, hx]
    rw [if_pos hx, if_neg (by simp [hn])]
  · have hx' : x.msb = false := by simpa using hx
    have hn : (-x).msb = true := by simp [hneg, hx']
    rw [if_neg hx, if_pos hn, neg_neg]

theorem negate_if_injective (sign : BitVec 64) :
    Function.Injective (jolt_virtual_negate_if_value sign) := by
  intro x y h
  change (if sign.msb then -x else x) = (if sign.msb then -y else y) at h
  by_cases hsign : sign.msb = true
  · simp only [hsign, ↓reduceIte] at h
    have := congrArg Neg.neg h
    simpa only [neg_neg] using this
  · simpa only [hsign, Bool.false_eq_true, ↓reduceIte] using h

/-- Applying Rust's quotient-sign correction to `sdiv` exposes the unsigned
quotient of the two operand magnitudes. -/
theorem negate_if_xor_sdiv (x y : BitVec 64) :
    signedQuotientMagnitude x y (BitVec.sdiv x y) =
      bv_abs x / bv_abs y := by
  unfold signedQuotientMagnitude jolt_virtual_negate_if_value bv_abs
  rw [BitVec.sdiv_eq]
  by_cases hx : x.msb <;> by_cases hy : y.msb <;>
    simp [hx, hy]

private theorem bv_abs_udiv_bv_abs (x y : BitVec 64) :
    bv_abs (bv_abs x / bv_abs y) = bv_abs x / bv_abs y := by
  change BitVec.abs (BitVec.abs x / BitVec.abs y) =
    BitVec.abs x / BitVec.abs y
  rw [BitVec.abs_eq]
  by_cases hq : (BitVec.abs x / BitVec.abs y).msb = true
  · rw [if_pos hq]
    rw [BitVec.msb_udiv] at hq
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨hx, hy⟩ := hq
    rw [BitVec.msb_abs] at hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    rw [hx.1, BitVec.abs_intMin, hy, BitVec.udiv_one, BitVec.neg_intMin]
  · rw [if_neg hq]

/-- The ordinary absolute value of a signed quotient is the same unsigned
magnitude used by the `REM` expansion. -/
theorem bv_abs_sdiv (x y : BitVec 64) :
    bv_abs (BitVec.sdiv x y) = bv_abs x / bv_abs y := by
  have hsigned := negate_if_xor_sdiv x y
  unfold signedQuotientMagnitude jolt_virtual_negate_if_value at hsigned
  by_cases hsign : (x ^^^ y).msb = true
  · rw [if_pos hsign] at hsigned
    rw [← bv_abs_neg (BitVec.sdiv x y), hsigned]
    exact bv_abs_udiv_bv_abs x y
  · rw [if_neg hsign] at hsigned
    rw [hsigned]
    exact bv_abs_udiv_bv_abs x y

/-- Negating a magnitude according to its original value's sign recovers the
original bit-vector. -/
theorem negate_if_bv_abs (x : BitVec 64) :
    jolt_virtual_negate_if_value x (bv_abs x) = x := by
  unfold jolt_virtual_negate_if_value bv_abs
  by_cases hsign : x.msb = true
  · rw [if_pos hsign, if_pos hsign, neg_neg]
  · rw [if_neg hsign, if_neg hsign]

/-- Sign-correcting the unsigned remainder of the operand magnitudes gives
`srem`. -/
theorem negate_if_umod_bv_abs (x y : BitVec 64) :
    jolt_virtual_negate_if_value x (bv_abs x % bv_abs y) =
      BitVec.srem x y := by
  unfold jolt_virtual_negate_if_value bv_abs
  rw [BitVec.srem_eq]
  by_cases hx : x.msb <;> by_cases hy : y.msb <;>
    simp [hx, hy]

/-- With a nonzero divisor, Rust's sign-corrected quotient advice is exactly
the honest unsigned quotient of operand magnitudes. -/
theorem honest_signed_quotient_magnitude (dividend divisor : BitVec 64)
    (hdivisor : divisor ≠ 0#64) :
    signedQuotientMagnitude dividend divisor
        (sail_div_value dividend divisor false) =
      sail_div_value (bv_abs dividend) (bv_abs divisor) true := by
  rw [sail_div_value_eq_sdiv_of_ne dividend divisor hdivisor,
    negate_if_xor_sdiv,
    sail_div_value_of_normal_u (bv_abs dividend) (bv_abs divisor)
      (bv_abs_ne_zero hdivisor)]

/-- The one advice word used by signed `REM` is the honest unsigned quotient
of operand magnitudes. -/
theorem rem_advice_value_eq_unsigned_quotient
    (dividend divisor : BitVec 64) (hdivisor : divisor ≠ 0#64) :
    rem_advice_value dividend divisor =
      sail_div_value (bv_abs dividend) (bv_abs divisor) true := by
  unfold rem_advice_value
  rw [if_neg hdivisor, sail_div_value_eq_sdiv_of_ne dividend divisor hdivisor,
    bv_abs_sdiv,
    sail_div_value_of_normal_u (bv_abs dividend) (bv_abs divisor)
      (bv_abs_ne_zero hdivisor)]

theorem hguard_div0_of_honest_signed (dividend divisor : BitVec 64) :
    ¬ (divisor = 0#64 ∧
      sail_div_value dividend divisor false ≠ (-1 : BitVec 64)) := by
  rintro ⟨hzero, hquotient⟩
  exact hquotient (sail_div_value_of_zero dividend divisor hzero)

theorem hguard_no_overflow_of_honest_signed
    (dividend divisor : BitVec 64) :
    let q := sail_div_value dividend divisor false
    let qMagnitude := signedQuotientMagnitude dividend divisor q
    qMagnitude.toNat * (bv_abs divisor).toNat < 2^64 := by
  intro q qMagnitude
  by_cases hzero : divisor = 0#64
  · subst divisor
    simp [bv_abs]
  · rw [show qMagnitude =
        sail_div_value (bv_abs dividend) (bv_abs divisor) true from
      honest_signed_quotient_magnitude dividend divisor hzero]
    exact hguard_no_overflow_of_honest_u
      (bv_abs dividend) (bv_abs divisor)

theorem hguard_product_lte_of_honest_signed
    (dividend divisor : BitVec 64) :
    let q := sail_div_value dividend divisor false
    let qMagnitude := signedQuotientMagnitude dividend divisor q
    (qMagnitude * bv_abs divisor).toNat ≤ (bv_abs dividend).toNat := by
  intro q qMagnitude
  by_cases hzero : divisor = 0#64
  · subst divisor
    simp [bv_abs]
  · rw [show qMagnitude =
        sail_div_value (bv_abs dividend) (bv_abs divisor) true from
      honest_signed_quotient_magnitude dividend divisor hzero]
    exact hguard_q_times_d_le_dividend_of_honest_u
      (bv_abs dividend) (bv_abs divisor)

theorem hguard_remainder_bound_of_honest_signed
    (dividend divisor : BitVec 64) :
    let q := sail_div_value dividend divisor false
    let qMagnitude := signedQuotientMagnitude dividend divisor q
    bv_abs divisor = 0#64 ∨
      (bv_abs dividend - qMagnitude * bv_abs divisor).toNat <
        (bv_abs divisor).toNat := by
  intro q qMagnitude
  by_cases hzero : divisor = 0#64
  · left
    simp [hzero, bv_abs]
  · rw [show qMagnitude =
        sail_div_value (bv_abs dividend) (bv_abs divisor) true from
      honest_signed_quotient_magnitude dividend divisor hzero]
    exact hguard_rem_bound_of_honest_u
      (bv_abs dividend) (bv_abs divisor)

/-- The four assertion guards in the new signed `DIV` expansion uniquely pin
the single advice word to Sail's quotient. -/
theorem signed_quotient_eq_of_guards
    (dividend divisor quotient : BitVec 64)
    (hdiv0 : ¬ (divisor = 0#64 ∧ quotient ≠ (-1 : BitVec 64)))
    (hoverflow :
      (signedQuotientMagnitude dividend divisor quotient).toNat *
        (bv_abs divisor).toNat < 2^64)
    (hlte :
      (signedQuotientMagnitude dividend divisor quotient * bv_abs divisor).toNat ≤
        (bv_abs dividend).toNat)
    (hremainder :
      bv_abs divisor = 0#64 ∨
        (bv_abs dividend -
          signedQuotientMagnitude dividend divisor quotient *
            bv_abs divisor).toNat < (bv_abs divisor).toNat) :
    quotient = sail_div_value dividend divisor false := by
  by_cases hzero : divisor = 0#64
  · have hquotient : quotient = -1 := by
      by_contra hne
      exact hdiv0 ⟨hzero, hne⟩
    rw [hquotient, sail_div_value_of_zero dividend divisor hzero]
  · have habs_ne : bv_abs divisor ≠ 0#64 := bv_abs_ne_zero hzero
    have hdiv0_unsigned :
        ¬ (bv_abs divisor = 0#64 ∧
          signedQuotientMagnitude dividend divisor quotient ≠
            (-1 : BitVec 64)) := by
      rintro ⟨h, _⟩
      exact habs_ne h
    have hunique := advice_unique_of_guards_u
      (bv_abs dividend) (bv_abs divisor)
      (signedQuotientMagnitude dividend divisor quotient)
      hdiv0_unsigned hoverflow hlte hremainder
    have hhonest := honest_signed_quotient_magnitude dividend divisor hzero
    apply negate_if_injective (dividend ^^^ divisor)
    exact hunique.trans hhonest.symm

theorem hguard_no_overflow_of_honest_rem
    (dividend divisor : BitVec 64) :
    (rem_advice_value dividend divisor).toNat *
      (bv_abs divisor).toNat < 2^64 := by
  by_cases hzero : divisor = 0#64
  · subst divisor
    simp [rem_advice_value, bv_abs]
  · rw [rem_advice_value_eq_unsigned_quotient dividend divisor hzero]
    exact hguard_no_overflow_of_honest_u
      (bv_abs dividend) (bv_abs divisor)

theorem hguard_product_lte_of_honest_rem
    (dividend divisor : BitVec 64) :
    (rem_advice_value dividend divisor * bv_abs divisor).toNat ≤
      (bv_abs dividend).toNat := by
  by_cases hzero : divisor = 0#64
  · subst divisor
    simp [rem_advice_value, bv_abs]
  · rw [rem_advice_value_eq_unsigned_quotient dividend divisor hzero]
    exact hguard_q_times_d_le_dividend_of_honest_u
      (bv_abs dividend) (bv_abs divisor)

theorem hguard_remainder_bound_of_honest_rem
    (dividend divisor : BitVec 64) :
    bv_abs divisor = 0#64 ∨
      (bv_abs dividend - rem_advice_value dividend divisor *
        bv_abs divisor).toNat < (bv_abs divisor).toNat := by
  by_cases hzero : divisor = 0#64
  · left
    simp [hzero, bv_abs]
  · rw [rem_advice_value_eq_unsigned_quotient dividend divisor hzero]
    exact hguard_rem_bound_of_honest_u
      (bv_abs dividend) (bv_abs divisor)

/-- The verification guards force the magnitude remainder to become Sail's
signed remainder after Rust's final sign correction. -/
theorem signed_remainder_eq_of_guards
    (dividend divisor quotientMagnitude : BitVec 64)
    (hoverflow : quotientMagnitude.toNat * (bv_abs divisor).toNat < 2^64)
    (hlte :
      (quotientMagnitude * bv_abs divisor).toNat ≤ (bv_abs dividend).toNat)
    (hremainder :
      bv_abs divisor = 0#64 ∨
        (bv_abs dividend - quotientMagnitude * bv_abs divisor).toNat <
          (bv_abs divisor).toNat) :
    jolt_virtual_negate_if_value dividend
        (bv_abs dividend - quotientMagnitude * bv_abs divisor) =
      sail_rem_value dividend divisor false := by
  have hunsigned := remainder_eq_sail_rem_of_guards_u
    (bv_abs dividend) (bv_abs divisor) quotientMagnitude
    hoverflow hlte hremainder
  rw [hunsigned]
  by_cases hzero : divisor = 0#64
  · have habs_zero : bv_abs divisor = 0#64 := by simp [hzero, bv_abs]
    rw [sail_rem_value_of_zero_remu (bv_abs dividend) (bv_abs divisor)
      habs_zero]
    rw [negate_if_bv_abs]
    exact (sail_rem_value_of_zero dividend divisor hzero).symm
  · rw [sail_rem_value_of_normal_remu (bv_abs dividend) (bv_abs divisor)
      (bv_abs_ne_zero hzero)]
    rw [negate_if_umod_bv_abs]
    exact (sail_rem_value_eq_srem dividend divisor).symm

end
