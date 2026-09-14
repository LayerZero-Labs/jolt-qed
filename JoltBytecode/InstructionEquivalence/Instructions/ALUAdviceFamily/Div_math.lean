import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Primitives
import Mathlib

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Architectural DIV/REM values

These definitions transcribe the pure values written by Sail. The old
arithmetic lemmas for the former two-advice signed expansion were removed when
Rust changed that expansion to its one-advice magnitude construction.
-/

/-- The pure 64-bit value written by execute_DIV. -/
def sail_div_value
    (rs1_bits rs2_bits : BitVec 64)
    (is_unsigned : Bool) : BitVec 64 :=
  let rs1_int :=
    if is_unsigned then BitVec.toNatInt rs1_bits else BitVec.toInt rs1_bits
  let rs2_int :=
    if is_unsigned then BitVec.toNatInt rs2_bits else BitVec.toInt rs2_bits
  let quotient :=
    if (rs2_int == 0) then -1 else Int.tdiv rs1_int rs2_int
  let quotient :=
    if LeanRV64D.Functions.not is_unsigned &&
        (quotient ≥b (2 ^i (LeanRV64D.Functions.xlen -i 1)))
    then -(2 ^i (LeanRV64D.Functions.xlen -i 1))
    else quotient
  to_bits_truncate (l := 64) quotient

/-- The pure 64-bit value written by execute_REM. -/
def sail_rem_value
    (rs1_bits rs2_bits : BitVec 64)
    (is_unsigned : Bool) : BitVec 64 :=
  let rs1_int :=
    if is_unsigned then BitVec.toNatInt rs1_bits else BitVec.toInt rs1_bits
  let rs2_int :=
    if is_unsigned then BitVec.toNatInt rs2_bits else BitVec.toInt rs2_bits
  let remainder :=
    if (rs2_int == 0) then rs1_int else Int.tmod rs1_int rs2_int
  to_bits_truncate (l := 64) remainder

/-- Absolute value of a signed 64-bit bit-vector. -/
def bv_abs (x : BitVec 64) : BitVec 64 :=
  if x.msb then -x else x

/-- The single advice word emitted by Rust for `REM`.

Rust uses zero advice on division by zero; otherwise it supplies the unsigned
magnitude of the signed quotient. -/
def rem_advice_value
    (dividend divisor : BitVec 64) : BitVec 64 :=
  if divisor = 0#64 then 0
  else bv_abs (sail_div_value dividend divisor false)

private theorem mod65_toNat_mod64 (x : Int) :
    (x % 36893488147419103232).toNat % 18446744073709551616 =
      (x % 18446744073709551616).toNat := by
  apply Int.ofNat.inj
  simp [Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (36893488147419103232 : Int) ≠ 0)),
        Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (18446744073709551616 : Int) ≠ 0))]

private theorem trunc64_eq_intCast (x : Int) :
    to_bits_truncate (l := 64) x = (x : BitVec 64) := by
  apply BitVec.eq_of_toFin_eq
  rw [show to_bits_truncate (l := 64) x =
        BitVec.ofNat 64 ((x % 36893488147419103232).toNat) by
        simp [to_bits_truncate, get_slice_int, BitVec.extractLsb']]
  rw [BitVec.toFin_ofNat, BitVec.toFin_intCast]
  ext
  simpa [Fin.ofNat] using mod65_toNat_mod64 x

/-- Signed division by zero produces the architectural all-ones result. -/
theorem sail_div_value_of_zero (dividend divisor : BitVec 64)
    (h : divisor = 0#64) :
    sail_div_value dividend divisor false = (-1 : BitVec 64) := by
  subst divisor
  unfold sail_div_value
  simp
  decide

/-- The signed overflow pair produces `INT_MIN`. -/
theorem sail_div_value_of_overflow (dividend divisor : BitVec 64)
    (h : dividend = (1 : BitVec 64) <<< 63 ∧ divisor = -1) :
    sail_div_value dividend divisor false = (1 : BitVec 64) <<< 63 := by
  obtain ⟨rfl, rfl⟩ := h
  decide

/-- Outside division by zero and the overflow pair, Sail agrees with
`BitVec.sdiv`. -/
theorem sail_div_value_of_normal (dividend divisor : BitVec 64)
    (h_ne : divisor ≠ 0#64)
    (h_no_overflow :
      ¬ (dividend = (1 : BitVec 64) <<< 63 ∧ divisor = -1)) :
    sail_div_value dividend divisor false = BitVec.sdiv dividend divisor := by
  have hdivInt : divisor.toInt ≠ 0 := by
    intro h
    apply h_ne
    apply BitVec.eq_of_toInt_eq
    simpa using h
  have hne_pair :
      dividend ≠ BitVec.intMin 64 ∨ divisor ≠ -1#64 := by
    by_cases ha : dividend = BitVec.intMin 64
    · right
      intro hb
      apply h_no_overflow
      exact ⟨by simpa using ha, by simpa using hb⟩
    · exact Or.inl ha
  have hsdivInt :
      (BitVec.sdiv dividend divisor).toInt =
        dividend.toInt.tdiv divisor.toInt :=
    BitVec.toInt_sdiv_of_ne_or_ne dividend divisor hne_pair
  have hquotient_lt : dividend.toInt.tdiv divisor.toInt < 2^63 := by
    rw [← hsdivInt]
    simpa using @BitVec.toInt_lt 64 (BitVec.sdiv dividend divisor)
  unfold sail_div_value
  simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq, hdivInt,
    show LeanRV64D.Functions.not false = true from rfl, Bool.true_and]
  have hge_false :
      (dividend.toInt.tdiv divisor.toInt ≥b
        2 ^ ((LeanRV64D.Functions.xlen : Int) - 1)) = false := by
    show decide _ = false
    apply decide_eq_false
    push_neg
    simpa using hquotient_lt
  rw [hge_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [trunc64_eq_intCast, ← hsdivInt]
  exact BitVec.ofInt_toInt

/-- For every nonzero divisor, Sail's signed quotient is `BitVec.sdiv`;
the overflow case is included because both sides wrap to `INT_MIN`. -/
theorem sail_div_value_eq_sdiv_of_ne (dividend divisor : BitVec 64)
    (h_ne : divisor ≠ 0#64) :
    sail_div_value dividend divisor false = BitVec.sdiv dividend divisor := by
  by_cases h_overflow :
      dividend = (1 : BitVec 64) <<< 63 ∧ divisor = -1
  · obtain ⟨rfl, rfl⟩ := h_overflow
    rw [sail_div_value_of_overflow]
    · simpa only [show ((1 : BitVec 64) <<< 63) = BitVec.intMin 64 by decide]
        using BitVec.intMin_sdiv_neg_one (w := 64)
    · exact ⟨rfl, rfl⟩
  · exact sail_div_value_of_normal dividend divisor h_ne h_overflow

/-- Signed remainder by zero returns the dividend. -/
theorem sail_rem_value_of_zero (dividend divisor : BitVec 64)
    (h : divisor = 0#64) :
    sail_rem_value dividend divisor false = dividend := by
  subst divisor
  unfold sail_rem_value
  simp only [BitVec.toInt_zero, beq_iff_eq]
  rw [trunc64_eq_intCast]
  exact BitVec.ofInt_toInt

/-- For a nonzero divisor, Sail's signed remainder is `BitVec.srem`. -/
theorem sail_rem_value_of_normal (dividend divisor : BitVec 64)
    (h_ne : divisor ≠ 0#64) :
    sail_rem_value dividend divisor false = BitVec.srem dividend divisor := by
  have hdivInt : divisor.toInt ≠ 0 := by
    intro h
    apply h_ne
    apply BitVec.eq_of_toInt_eq
    simpa using h
  unfold sail_rem_value
  simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq, hdivInt]
  rw [trunc64_eq_intCast, ← BitVec.toInt_srem]
  exact BitVec.ofInt_toInt

/-- Sail's signed remainder agrees with `BitVec.srem`, including division by
zero. -/
theorem sail_rem_value_eq_srem (dividend divisor : BitVec 64) :
    sail_rem_value dividend divisor false = BitVec.srem dividend divisor := by
  by_cases hzero : divisor = 0#64
  · rw [sail_rem_value_of_zero dividend divisor hzero, hzero,
      BitVec.srem_zero]
  · exact sail_rem_value_of_normal dividend divisor hzero

end
