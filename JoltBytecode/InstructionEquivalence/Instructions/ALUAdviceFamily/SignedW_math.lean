import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Signed_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divw_math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-- A 32-bit value represented canonically in a 64-bit register. -/
def signExtend32 (x : BitVec 32) : BitVec 64 :=
  sign_extend (m := 64) x

/-- The signed low word of an RV64 source register. This is exactly the value
computed by Rust's initial `VirtualSignExtendWord` rows. -/
def signedWordValue (x : BitVec 64) : BitVec 64 :=
  signExtend32 (Sail.BitVec.extractLsb x 31 0)

private theorem mod33_toNat_mod32_signedw (x : Int) :
    (x % 8589934592).toNat % 4294967296 =
      (x % 4294967296).toNat := by
  apply Int.ofNat.inj
  simp [Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (8589934592 : Int) ≠ 0)),
        Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (4294967296 : Int) ≠ 0))]

private theorem trunc32_eq_intCast_signedw (x : Int) :
    to_bits_truncate (l := 32) x = (x : BitVec 32) := by
  apply BitVec.eq_of_toFin_eq
  rw [show to_bits_truncate (l := 32) x =
      BitVec.ofNat 32 ((x % 8589934592).toNat) by
    simp [to_bits_truncate, get_slice_int, BitVec.extractLsb']]
  rw [BitVec.toFin_ofNat, BitVec.toFin_intCast]
  ext
  simpa [Fin.ofNat] using mod33_toNat_mod32_signedw x

private theorem extractLsb_signExtend32 (x : BitVec 32) :
    Sail.BitVec.extractLsb (signExtend32 x) 31 0 = x := by
  unfold signExtend32 sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb, BitVec.getLsbD_signExtend]
  have hi32 : i < 32 := by omega
  have hi64 : i < 64 := by omega
  simp [hi32, hi64]

theorem signExtend32_extract_roundtrip (x : BitVec 32) :
    signExtend32 (Sail.BitVec.extractLsb (signExtend32 x) 31 0) =
      signExtend32 x := by
  rw [extractLsb_signExtend32]

private theorem extractLsb31_eq_setWidth32 (x : BitVec 64) :
    Sail.BitVec.extractLsb x 31 0 = x.setWidth 32 := by
  unfold Sail.BitVec.extractLsb
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb]
  simp

/-- The Sail expression used by the execution lemma and the pure value used
by `VirtualSignExtendWord` are the same word sign-extension. -/
theorem sign_extend_word_eq_jolt_virtual (x : BitVec 64) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0) =
      jolt_virtual_sign_extend_word_value x := by
  unfold jolt_virtual_sign_extend_word_value sign_extend Sail.BitVec.signExtend
  rw [extractLsb31_eq_setWidth32]

theorem signExtend32_toInt (x : BitVec 32) :
    (signExtend32 x).toInt = x.toInt := by
  unfold signExtend32 sign_extend Sail.BitVec.signExtend
  rw [BitVec.toInt_signExtend]
  have hlo : -(2^31 : Int) ≤ x.toInt := by
    simpa using @BitVec.le_toInt 32 x
  have hhi : x.toInt < 2^31 := by
    simpa using @BitVec.toInt_lt 32 x
  apply Int.bmod_eq_of_le
  · show -(((2^32 : Nat) : Int) / 2) ≤ x.toInt
    have h : (((2^32 : Nat) : Int) / 2) = (2^31 : Int) := by decide
    rw [h]
    exact hlo
  · show x.toInt < ((((2^32 : Nat) : Int) + 1) / 2)
    have h : ((((2^32 : Nat) : Int) + 1) / 2) = (2^31 : Int) := by decide
    rw [h]
    exact hhi

theorem signExtend32_eq_zero_iff (x : BitVec 32) :
    signExtend32 x = 0#64 ↔ x = 0#32 := by
  constructor
  · intro h
    have hlow := congrArg
      (fun z : BitVec 64 => Sail.BitVec.extractLsb z 31 0) h
    simpa only [extractLsb_signExtend32] using hlow
  · intro h
    subst x
    decide

theorem signedWordValue_eq_zero_iff (x : BitVec 64) :
    signedWordValue x = 0#64 ↔
      Sail.BitVec.extractLsb x 31 0 = 0#32 := by
  exact signExtend32_eq_zero_iff _

private theorem signExtend32_ne_intMin64 (x : BitVec 32) :
    signExtend32 x ≠ BitVec.intMin 64 := by
  intro h
  have htoInt := congrArg BitVec.toInt h
  rw [signExtend32_toInt] at htoInt
  have hlo : -(2^31 : Int) ≤ x.toInt := by
    simpa using @BitVec.le_toInt 32 x
  have hmin : (BitVec.intMin 64).toInt = -(2^63 : Int) := by decide
  rw [hmin] at htoInt
  omega

theorem signExtend32_sdiv (x y : BitVec 32)
    (hnoOverflow : ¬ (x = BitVec.intMin 32 ∧ y = -1#32)) :
    signExtend32 (BitVec.sdiv x y) =
      BitVec.sdiv (signExtend32 x) (signExtend32 y) := by
  have hpair32 : x ≠ BitVec.intMin 32 ∨ y ≠ -1#32 := by
    by_cases hx : x = BitVec.intMin 32
    · exact Or.inr (fun hy => hnoOverflow ⟨hx, hy⟩)
    · exact Or.inl hx
  have hpair64 :
      signExtend32 x ≠ BitVec.intMin 64 ∨ signExtend32 y ≠ -1#64 :=
    Or.inl (signExtend32_ne_intMin64 x)
  apply BitVec.eq_of_toInt_eq
  rw [signExtend32_toInt,
    BitVec.toInt_sdiv_of_ne_or_ne x y hpair32,
    BitVec.toInt_sdiv_of_ne_or_ne (signExtend32 x) (signExtend32 y) hpair64,
    signExtend32_toInt, signExtend32_toInt]

theorem signExtend32_srem (x y : BitVec 32) :
    signExtend32 (BitVec.srem x y) =
      BitVec.srem (signExtend32 x) (signExtend32 y) := by
  apply BitVec.eq_of_toInt_eq
  rw [signExtend32_toInt, BitVec.toInt_srem, BitVec.toInt_srem,
    signExtend32_toInt, signExtend32_toInt]

theorem sail_divw_value_of_zero_signedw (dividend divisor : BitVec 64)
    (h : Sail.BitVec.extractLsb divisor 31 0 = 0#32) :
    sail_divw_value dividend divisor false = (-1 : BitVec 64) := by
  unfold sail_divw_value
  simp only [h, Bool.false_eq_true, ↓reduceIte, BitVec.toInt_zero,
    show ((0 : Int) == 0) = true from rfl,
    show LeanRV64D.Functions.not false = true from rfl, Bool.true_and,
    show ((-1 : Int) ≥b (2 ^i (31 : Int))) = false from by decide]
  decide

theorem sail_divw_value_of_overflow_signedw (dividend divisor : BitVec 64)
    (hsd : Sail.BitVec.extractLsb dividend 31 0 = BitVec.intMin 32)
    (hsv : Sail.BitVec.extractLsb divisor 31 0 = -1#32) :
    sail_divw_value dividend divisor false = signExtend32 (BitVec.intMin 32) := by
  unfold sail_divw_value
  simp only [hsd, hsv, Bool.false_eq_true, ↓reduceIte,
    show (BitVec.toInt (-1#32) == (0 : Int)) = false from by decide,
    show LeanRV64D.Functions.not false = true from rfl, Bool.true_and,
    show (Int.tdiv (BitVec.toInt (BitVec.intMin 32)) (BitVec.toInt (-1#32))
      ≥b (2 ^i (31 : Int))) = true from by decide]
  decide

theorem sail_divw_value_of_normal_signedw (dividend divisor : BitVec 64)
    (hne : Sail.BitVec.extractLsb divisor 31 0 ≠ 0#32)
    (hnoOverflow :
      ¬ (Sail.BitVec.extractLsb dividend 31 0 = BitVec.intMin 32 ∧
        Sail.BitVec.extractLsb divisor 31 0 = -1#32)) :
    sail_divw_value dividend divisor false =
      signExtend32
        (BitVec.sdiv (Sail.BitVec.extractLsb dividend 31 0)
          (Sail.BitVec.extractLsb divisor 31 0)) := by
  set x := Sail.BitVec.extractLsb dividend 31 0 with hx
  set y := Sail.BitVec.extractLsb divisor 31 0 with hy
  have hyInt : y.toInt ≠ 0 := by
    intro h
    apply hne
    exact BitVec.eq_of_toInt_eq (by simpa only [hy] using h)
  have hpair : x ≠ BitVec.intMin 32 ∨ y ≠ (-1 : BitVec 32) := by
    by_cases hxmin : x = BitVec.intMin 32
    · exact Or.inr (fun hyneg => hnoOverflow ⟨hxmin, hyneg⟩)
    · exact Or.inl hxmin
  have hsdivInt :
      (BitVec.sdiv x y).toInt = Int.tdiv x.toInt y.toInt :=
    BitVec.toInt_sdiv_of_ne_or_ne x y hpair
  have hquotientLt : Int.tdiv x.toInt y.toInt < 2^31 := by
    rw [← hsdivInt]
    simpa using @BitVec.toInt_lt 32 (BitVec.sdiv x y)
  unfold sail_divw_value signExtend32
  rw [← hx, ← hy]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hzeroFalse : (y.toInt == (0 : Int)) = false :=
    decide_eq_false hyInt
  simp only [hzeroFalse]
  have hgeFalse :
      (Int.tdiv x.toInt y.toInt ≥b (2 ^i (31 : Int))) = false := by
    show decide _ = false
    apply decide_eq_false
    push_neg
    simpa using hquotientLt
  simp only [show LeanRV64D.Functions.not false = true from rfl,
    Bool.true_and, hgeFalse, Bool.false_eq_true, ↓reduceIte]
  rw [trunc32_eq_intCast_signedw, ← hsdivInt]
  congr 1
  exact BitVec.ofInt_toInt

theorem divw_advice_value_eq_sail_div_signed_words
    (dividend divisor : BitVec 64) :
    divw_advice_value dividend divisor =
      sail_div_value (signedWordValue dividend) (signedWordValue divisor) false := by
  by_cases hzero : Sail.BitVec.extractLsb divisor 31 0 = 0#32
  · have hwordZero : signedWordValue divisor = 0#64 :=
      (signedWordValue_eq_zero_iff divisor).2 hzero
    have hadvice : divw_advice_value dividend divisor = (-1 : BitVec 64) := by
      unfold divw_advice_value
      rw [if_pos hzero]
    rw [hadvice, sail_div_value_of_zero _ _ hwordZero]
  · have hwordNe : signedWordValue divisor ≠ 0#64 :=
      fun h => hzero ((signedWordValue_eq_zero_iff divisor).1 h)
    by_cases hoverflow :
        Sail.BitVec.extractLsb dividend 31 0 = BitVec.intMin 32 ∧
          Sail.BitVec.extractLsb divisor 31 0 = (-1 : BitVec 32)
    · obtain ⟨hdividend, hdivisor⟩ := hoverflow
      have hadvice :
          divw_advice_value dividend divisor = (1 : BitVec 64) <<< 31 := by
        unfold divw_advice_value
        rw [if_neg hzero, if_pos ⟨hdividend, hdivisor⟩]
      rw [hadvice, sail_div_value_eq_sdiv_of_ne _ _ hwordNe]
      unfold signedWordValue
      rw [hdividend, hdivisor]
      decide
    · have hadvice :
          divw_advice_value dividend divisor =
            sail_divw_value dividend divisor false := by
        unfold divw_advice_value
        rw [if_neg hzero, if_neg hoverflow]
      rw [hadvice,
        sail_divw_value_of_normal_signedw dividend divisor hzero hoverflow,
        sail_div_value_eq_sdiv_of_ne _ _ hwordNe]
      exact signExtend32_sdiv _ _ hoverflow

theorem sign_extend_divw_advice_value (dividend divisor : BitVec 64) :
    jolt_virtual_sign_extend_word_value (divw_advice_value dividend divisor) =
      sail_divw_value dividend divisor false := by
  unfold jolt_virtual_sign_extend_word_value
  by_cases hzero : Sail.BitVec.extractLsb divisor 31 0 = 0#32
  · have hadvice : divw_advice_value dividend divisor = (-1 : BitVec 64) := by
      unfold divw_advice_value
      rw [if_pos hzero]
    rw [hadvice, sail_divw_value_of_zero_signedw dividend divisor hzero]
    decide
  · by_cases hoverflow :
        Sail.BitVec.extractLsb dividend 31 0 = BitVec.intMin 32 ∧
          Sail.BitVec.extractLsb divisor 31 0 = (-1 : BitVec 32)
    · obtain ⟨hdividend, hdivisor⟩ := hoverflow
      have hadvice :
          divw_advice_value dividend divisor = (1 : BitVec 64) <<< 31 := by
        unfold divw_advice_value
        rw [if_neg hzero, if_pos ⟨hdividend, hdivisor⟩]
      rw [hadvice,
        sail_divw_value_of_overflow_signedw dividend divisor hdividend hdivisor]
      decide
    · have hadvice :
          divw_advice_value dividend divisor =
            sail_divw_value dividend divisor false := by
        unfold divw_advice_value
        rw [if_neg hzero, if_neg hoverflow]
      rw [hadvice,
        sail_divw_value_of_normal_signedw dividend divisor hzero hoverflow]
      exact signExtend32_extract_roundtrip _

theorem sail_remw_value_of_zero_signedw (dividend divisor : BitVec 64)
    (h : Sail.BitVec.extractLsb divisor 31 0 = 0#32) :
    sail_remw_value dividend divisor false = signedWordValue dividend := by
  unfold sail_remw_value signedWordValue
  simp only [h, Bool.false_eq_true, ↓reduceIte, BitVec.toInt_zero,
    show ((0 : Int) == 0) = true from rfl]
  rw [trunc32_eq_intCast_signedw]
  exact congrArg signExtend32 BitVec.ofInt_toInt

theorem sail_remw_value_of_normal_signedw (dividend divisor : BitVec 64)
    (hne : Sail.BitVec.extractLsb divisor 31 0 ≠ 0#32) :
    sail_remw_value dividend divisor false =
      signExtend32
        (BitVec.srem (Sail.BitVec.extractLsb dividend 31 0)
          (Sail.BitVec.extractLsb divisor 31 0)) := by
  let x := Sail.BitVec.extractLsb dividend 31 0
  let y := Sail.BitVec.extractLsb divisor 31 0
  have hyInt : y.toInt ≠ 0 := by
    intro h
    apply hne
    exact BitVec.eq_of_toInt_eq (by simpa only [y] using h)
  unfold sail_remw_value
  change sign_extend (m := 64) (to_bits_truncate (l := 32)
    (if decide (y.toInt = 0) then x.toInt else Int.tmod x.toInt y.toInt)) = _
  rw [decide_eq_false hyInt]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [trunc32_eq_intCast_signedw, ← BitVec.toInt_srem]
  exact congrArg signExtend32 BitVec.ofInt_toInt

theorem sail_remw_value_eq_sail_rem_signed_words
    (dividend divisor : BitVec 64) :
    sail_remw_value dividend divisor false =
      sail_rem_value (signedWordValue dividend) (signedWordValue divisor) false := by
  by_cases hzero : Sail.BitVec.extractLsb divisor 31 0 = 0#32
  · have hwordZero : signedWordValue divisor = 0#64 :=
      (signedWordValue_eq_zero_iff divisor).2 hzero
    rw [sail_remw_value_of_zero_signedw dividend divisor hzero,
      sail_rem_value_of_zero _ _ hwordZero]
  · have hwordNe : signedWordValue divisor ≠ 0#64 :=
      fun h => hzero ((signedWordValue_eq_zero_iff divisor).1 h)
    rw [sail_remw_value_of_normal_signedw dividend divisor hzero,
      sail_rem_value_of_normal _ _ hwordNe]
    exact signExtend32_srem _ _

theorem bv_abs_sail_divw_eq_signed_words
    (dividend divisor : BitVec 64) :
    bv_abs (sail_divw_value dividend divisor false) =
      bv_abs (sail_div_value
        (signedWordValue dividend) (signedWordValue divisor) false) := by
  by_cases hzero : Sail.BitVec.extractLsb divisor 31 0 = 0#32
  · have hwordZero : signedWordValue divisor = 0#64 :=
      (signedWordValue_eq_zero_iff divisor).2 hzero
    rw [sail_divw_value_of_zero_signedw dividend divisor hzero,
      sail_div_value_of_zero _ _ hwordZero]
  · by_cases hoverflow :
        Sail.BitVec.extractLsb dividend 31 0 = BitVec.intMin 32 ∧
          Sail.BitVec.extractLsb divisor 31 0 = (-1 : BitVec 32)
    · obtain ⟨hdividend, hdivisor⟩ := hoverflow
      have hwordNe : signedWordValue divisor ≠ 0#64 :=
        fun h => hzero ((signedWordValue_eq_zero_iff divisor).1 h)
      rw [sail_divw_value_of_overflow_signedw dividend divisor
          hdividend hdivisor,
        sail_div_value_eq_sdiv_of_ne _ _ hwordNe]
      unfold signedWordValue
      rw [hdividend, hdivisor]
      decide
    · have hadvice :
          divw_advice_value dividend divisor =
            sail_divw_value dividend divisor false := by
        unfold divw_advice_value
        rw [if_neg hzero, if_neg hoverflow]
      rw [← hadvice, divw_advice_value_eq_sail_div_signed_words]

theorem remw_advice_value_eq_rem_signed_words
    (dividend divisor : BitVec 64) :
    remw_advice_value dividend divisor =
      rem_advice_value (signedWordValue dividend) (signedWordValue divisor) := by
  by_cases hzero : Sail.BitVec.extractLsb divisor 31 0 = 0#32
  · have hwordZero : signedWordValue divisor = 0#64 :=
      (signedWordValue_eq_zero_iff divisor).2 hzero
    unfold remw_advice_value rem_advice_value
    rw [if_pos hzero, if_pos hwordZero]
  · have hwordNe : signedWordValue divisor ≠ 0#64 :=
      fun h => hzero ((signedWordValue_eq_zero_iff divisor).1 h)
    unfold remw_advice_value rem_advice_value
    rw [if_neg hzero, if_neg hwordNe,
      bv_abs_sail_divw_eq_signed_words]

end
