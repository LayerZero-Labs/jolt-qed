import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divu_math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Math content for `remuProgram`

REMU receives quotient advice, computes the remainder inline as
`dividend - quotient * divisor`, and writes that remainder.  The guards
do not need to make the raw quotient advice public; they only need to
force the computed remainder to equal Sail's unsigned REM result.
-/

private theorem mod65_toNat_mod64_remu (x : Int) :
    (x % 36893488147419103232).toNat % 18446744073709551616
      = (x % 18446744073709551616).toNat := by
  apply Int.ofNat.inj
  simp [Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (36893488147419103232 : Int) ≠ 0)),
        Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (18446744073709551616 : Int) ≠ 0))]

private theorem trunc64_eq_intCast_remu (x : Int) :
    to_bits_truncate (l := 64) x = (x : BitVec 64) := by
  apply BitVec.eq_of_toFin_eq
  rw [show to_bits_truncate (l := 64) x
        = BitVec.ofNat 64 ((x % 36893488147419103232).toNat) by
        simp [to_bits_truncate, get_slice_int, BitVec.extractLsb']]
  rw [BitVec.toFin_ofNat, BitVec.toFin_intCast]
  ext
  simpa [Fin.ofNat] using mod65_toNat_mod64_remu x

private theorem toNat_mul_of_no_overflow_remu {x y : BitVec 64}
    (h : x.toNat * y.toNat < 2^64) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

private theorem toNat_sub_of_le_remu {x y : BitVec 64}
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

private theorem sail_div_value_of_normal_remu (dividend divisor : BitVec 64)
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
  rw [trunc64_eq_intCast_remu]
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

theorem sail_rem_value_of_zero_remu (dividend divisor : BitVec 64)
    (h : divisor = 0#64) :
    sail_rem_value dividend divisor true = dividend := by
  subst h
  unfold sail_rem_value
  simp only [BitVec.toNatInt, BitVec.toNat_zero, beq_iff_eq, ↓reduceIte]
  rw [if_pos (show Int.ofNat 0 = 0 from rfl)]
  rw [trunc64_eq_intCast_remu]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_intCast]
  rw [Int.emod_eq_of_lt]
  · exact Int.toNat_natCast _
  · exact Int.natCast_nonneg dividend.toNat
  · exact Int.ofNat_lt.mpr dividend.isLt

theorem sail_rem_value_of_normal_remu (dividend divisor : BitVec 64)
    (h_ne : divisor ≠ 0#64) :
    sail_rem_value dividend divisor true = dividend % divisor := by
  have hdivNat_ne : divisor.toNat ≠ 0 := by
    intro h
    apply h_ne
    apply BitVec.eq_of_toNat_eq
    simp [h]
  unfold sail_rem_value
  simp only [BitVec.toNatInt, beq_iff_eq, ↓reduceIte]
  have hbeq_false : ¬ Int.ofNat divisor.toNat = 0 := by
    intro h
    exact hdivNat_ne (Int.ofNat_eq_zero.mp h)
  rw [if_neg hbeq_false]
  rw [trunc64_eq_intCast_remu]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_intCast, BitVec.toNat_umod]
  have htmod :
      (Int.ofNat dividend.toNat).tmod (Int.ofNat divisor.toNat)
        = (dividend.toNat % divisor.toNat : Nat) := by
    exact (Int.ofNat_tmod dividend.toNat divisor.toNat).symm
  rw [Int.emod_eq_of_lt]
  · rw [htmod]
    exact Int.toNat_natCast _
  · rw [htmod]
    exact_mod_cast Nat.zero_le (dividend.toNat % divisor.toNat)
  · rw [htmod]
    have hlt : dividend.toNat % divisor.toNat < 2^64 := by
      exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero hdivNat_ne))
        (Nat.le_of_lt divisor.isLt)
    exact_mod_cast hlt

private theorem urem_eq_sub_udiv_mul (dividend divisor : BitVec 64)
    (h_ne : divisor ≠ 0#64) :
    dividend - (dividend / divisor) * divisor = dividend % divisor := by
  have hdivNat_ne : divisor.toNat ≠ 0 := by
    intro h
    apply h_ne
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
  apply BitVec.eq_of_toNat_eq
  rw [toNat_sub_of_le_remu hprod_le, hprod_toNat, BitVec.toNat_umod]
  rw [Nat.mul_comm (dividend.toNat / divisor.toNat) divisor.toNat,
    ← Nat.mod_eq_sub_mul_div]

/-- The REMU guards force the inline-computed remainder to be Sail REMU. -/
theorem remainder_eq_sail_rem_of_guards_u
    (dividend divisor q : BitVec 64)
    (h1 : q.toNat * divisor.toNat < 2^64)
    (h2 : (q * divisor).toNat ≤ dividend.toNat)
    (h3 : divisor = 0#64 ∨ (dividend - q * divisor).toNat < divisor.toNat) :
    dividend - q * divisor = sail_rem_value dividend divisor true := by
  by_cases hzero : divisor = 0#64
  · rw [hzero, BitVec.mul_zero, BitVec.sub_zero]
    exact (sail_rem_value_of_zero_remu dividend (0#64) rfl).symm
  · have hdiv0 : ¬ (divisor = 0#64 ∧ q ≠ (-1 : BitVec 64)) := by
      rintro ⟨hd, _⟩
      exact hzero hd
    have hq : q = sail_div_value dividend divisor true :=
      advice_unique_of_guards_u dividend divisor q hdiv0 h1 h2 h3
    rw [hq, sail_div_value_of_normal_remu dividend divisor hzero,
      sail_rem_value_of_normal_remu dividend divisor hzero]
    exact urem_eq_sub_udiv_mul dividend divisor hzero

end
