import JoltBytecode.InstructionEquivalence.ProofSupport.BundleLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess
import JoltBytecode.InstructionEquivalence.ProofSupport.Basic
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Primitives
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Div_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divw_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.DivuwProgramBlocks

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Math content for `divuwProgram` (advice-verified DIVUW)

The DIVUW counterpart of `Div_math.lean` / `Divu_math.lean` /
`Divw_math.lean`. Provides:

* The honest-advice value `sail_divuw_advice` — the u32 quotient
  zero-extended into a 64-bit BitVec. After sign-extension this equals
  `sail_divw_value dividend divisor true` (the value Sail writes to
  `rd`).
* Four **honest-advice guard lemmas** corresponding to the four
  asserts in `divuwProgram`'s inline sequence.
* The **writeback-value soundness lemma**
  `sext_advice_eq_sail_divw_value_of_guards_uw`.
* The **sign-extension round-trip** lemma
  `sext_advice_eq_sail_divw_value` — used by `divuwProgram_concrete`'s
  writeback step to convert the post-state's `sext(q)` into
  `sail_divw_value`.
-/

-- ----------------------------------------------------------------------------
-- Honest advice value
-- ----------------------------------------------------------------------------

/-- The honest oracle quotient for DIVUW: the unsigned 32-bit quotient
of `(dividend low 32 bits) / (divisor low 32 bits)`, zero-extended to
64 bits. Equals `u32::MAX` (zero-extended to `0x00000000FFFFFFFF`) when
the divisor is zero. After sign-extension this becomes
`sail_divw_value dividend divisor true`. -/
def sail_divuw_advice (dividend divisor : BitVec 64) : BitVec 64 :=
  zero_extend (m := 64)
    (Sail.BitVec.extractLsb (sail_divw_value dividend divisor true) 31 0)

-- ----------------------------------------------------------------------------
-- Local unsigned 32-bit helpers
-- ----------------------------------------------------------------------------

private theorem mod33_toNat_mod32_uw (x : Int) :
    (x % 8589934592).toNat % 4294967296
      = (x % 4294967296).toNat := by
  apply Int.ofNat.inj
  simp [Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (8589934592 : Int) ≠ 0)),
        Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (4294967296 : Int) ≠ 0))]

private theorem trunc32_eq_intCast_uw (x : Int) :
    to_bits_truncate (l := 32) x = (x : BitVec 32) := by
  apply BitVec.eq_of_toFin_eq
  rw [show to_bits_truncate (l := 32) x
        = BitVec.ofNat 32 ((x % 8589934592).toNat) by
        simp [to_bits_truncate, get_slice_int, BitVec.extractLsb']]
  rw [BitVec.toFin_ofNat, BitVec.toFin_intCast]
  ext
  simpa [Fin.ofNat] using mod33_toNat_mod32_uw x

private lemma zeroExtend32_64_toNat_uw (x : BitVec 32) :
    (zero_extend (m := 64) x).toNat = x.toNat := by
  unfold zero_extend Sail.BitVec.zeroExtend
  rw [BitVec.toNat_setWidth]
  apply Nat.mod_eq_of_lt
  have hx := x.isLt
  omega

private lemma extractLsb_zeroExtend_32_64_uw (x : BitVec 32) :
    Sail.BitVec.extractLsb (zero_extend (m := 64) x) 31 0 = x := by
  unfold zero_extend Sail.BitVec.zeroExtend Sail.BitVec.extractLsb
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi32_bool : (i <b 32) = true := by
    simpa only [Nat.blt_eq, decide_eq_true_eq] using hi
  have hi64_bool : (i <b 64) = true := by
    have : i < 64 := by omega
    simpa only [Nat.blt_eq, decide_eq_true_eq] using this
  simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_setWidth, Nat.reduceSub,
    Nat.reduceAdd, hi32_bool, hi64_bool, Bool.true_and, Nat.zero_add]

private lemma extractLsb_signExtend_32_64_uw (x : BitVec 32) :
    Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0 = x := by
  unfold sign_extend Sail.BitVec.signExtend Sail.BitVec.extractLsb
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi32_bool : (i <b 32) = true := by
    simpa only [Nat.blt_eq, decide_eq_true_eq] using hi
  have hi64_bool : (i <b 64) = true := by
    have : i < 64 := by omega
    simpa only [Nat.blt_eq, decide_eq_true_eq] using this
  simp (disch := omega) only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_signExtend,
    Nat.reduceSub, Nat.reduceAdd, hi32_bool, hi64_bool, Bool.true_and, Nat.zero_add,
    if_pos]

private lemma eq_zero_of_zeroExtend32_eq_zero_uw (x : BitVec 32)
    (h : zero_extend (m := 64) x = 0#64) : x = 0#32 := by
  have hx := congrArg (fun z : BitVec 64 => Sail.BitVec.extractLsb z 31 0) h
  change Sail.BitVec.extractLsb (zero_extend (m := 64) x) 31 0 =
    Sail.BitVec.extractLsb (0#64) 31 0 at hx
  rw [extractLsb_zeroExtend_32_64_uw] at hx
  simpa using hx

private theorem intCast_tdiv_eq_udiv32_uw (x y : BitVec 32) :
    ((Int.ofNat x.toNat).tdiv (Int.ofNat y.toNat) : BitVec 32) = x / y := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_intCast, BitVec.toNat_udiv]
  have htdiv :
      (Int.ofNat x.toNat).tdiv (Int.ofNat y.toNat)
        = (x.toNat / y.toNat : Nat) := by
    exact (Int.ofNat_tdiv x.toNat y.toNat).symm
  rw [Int.emod_eq_of_lt]
  · rw [htdiv]
    exact Int.toNat_natCast _
  · rw [htdiv]
    exact_mod_cast Nat.zero_le (x.toNat / y.toNat)
  · rw [htdiv]
    have hlt : x.toNat / y.toNat < 2^32 := by
      exact lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
    exact_mod_cast hlt

private theorem sail_divuw_advice_of_zero (dividend divisor : BitVec 64)
    (hzero : Sail.BitVec.extractLsb divisor 31 0 = 0#32) :
    sail_divuw_advice dividend divisor =
      zero_extend (m := 64) (-1#32 : BitVec 32) := by
  unfold sail_divuw_advice sail_divw_value
  simp only [hzero, ↓reduceIte, BitVec.toNatInt, BitVec.toNat_zero,
    show LeanRV64D.Functions.not true = false from rfl, Bool.false_and]
  rw [show ((Int.ofNat 0 == 0) = true) from rfl]
  simp only [↓reduceIte]
  rw [trunc32_eq_intCast_uw, extractLsb_signExtend_32_64_uw]
  rfl

private theorem sail_divuw_advice_of_normal (dividend divisor : BitVec 64)
    (hne : Sail.BitVec.extractLsb divisor 31 0 ≠ 0#32) :
    sail_divuw_advice dividend divisor =
      zero_extend (m := 64)
        (Sail.BitVec.extractLsb dividend 31 0 /
         Sail.BitVec.extractLsb divisor 31 0) := by
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  have hyNat_ne : y32.toNat ≠ 0 := by
    intro h
    apply hne
    apply BitVec.eq_of_toNat_eq
    simp [h]
  unfold sail_divuw_advice sail_divw_value
  rw [← hx32, ← hy32]
  simp only [show LeanRV64D.Functions.not true = false from rfl, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, BitVec.toNatInt]
  have hzero_false : ((Int.ofNat y32.toNat == 0) = false) := by
    change decide (Int.ofNat y32.toNat = 0) = false
    apply decide_eq_false
    intro h
    exact hyNat_ne (Int.ofNat_eq_zero.mp h)
  simp only [hzero_false, Bool.false_eq_true, ↓reduceIte]
  rw [trunc32_eq_intCast_uw, extractLsb_signExtend_32_64_uw,
    intCast_tdiv_eq_udiv32_uw]

private theorem signExtend_extract_sail_divuw_advice_of_zero
    (dividend divisor : BitVec 64)
    (hzero : Sail.BitVec.extractLsb divisor 31 0 = 0#32) :
    sign_extend (m := 64)
        (Sail.BitVec.extractLsb (sail_divuw_advice dividend divisor) 31 0)
      = (-1 : BitVec 64) := by
  rw [sail_divuw_advice_of_zero dividend divisor hzero,
    extractLsb_zeroExtend_32_64_uw]
  unfold sign_extend Sail.BitVec.signExtend
  decide

private theorem sail_divuw_advice_toNat_lt_u32 (dividend divisor : BitVec 64) :
    (sail_divuw_advice dividend divisor).toNat < 2^32 := by
  unfold sail_divuw_advice
  rw [zeroExtend32_64_toNat_uw]
  exact (Sail.BitVec.extractLsb (sail_divw_value dividend divisor true) 31 0).isLt

private theorem zeroExtend_extractLsb_toNat_lt_u32 (x : BitVec 64) :
    (zero_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)).toNat < 2^32 := by
  rw [zeroExtend32_64_toNat_uw]
  exact (Sail.BitVec.extractLsb x 31 0).isLt

private theorem toNat_mul_of_no_overflow_uw {x y : BitVec 64}
    (h : x.toNat * y.toNat < 2^64) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

private theorem toNat_sub_of_le_uw {x y : BitVec 64}
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

private theorem zeroExtend32_mul_toNat_uw (x y : BitVec 32) :
    (zero_extend (m := 64) x * zero_extend (m := 64) y).toNat =
      x.toNat * y.toNat := by
  apply toNat_mul_of_no_overflow_uw
  rw [zeroExtend32_64_toNat_uw, zeroExtend32_64_toNat_uw]
  have hx : x.toNat < 2^32 := x.isLt
  have hy : y.toNat < 2^32 := y.isLt
  nlinarith

private theorem nat_quotient_unique_of_mul_le_and_sub_lt_uw
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
-- Sign-extension round-trip
-- ----------------------------------------------------------------------------

/-- The honest advice round-trips through `sign_extend ∘ extractLsb 31 0`
to give `sail_divw_value`. Used by `divuwProgram_concrete`'s writeback
step. -/
theorem sext_advice_eq_sail_divw_value (dividend divisor : BitVec 64) :
    sign_extend (m := 64)
        (Sail.BitVec.extractLsb (sail_divuw_advice dividend divisor) 31 0)
      = sail_divw_value dividend divisor true := by
  unfold sail_divuw_advice sail_divw_value
  rw [extractLsb_zeroExtend_32_64_uw]
  rw [extractLsb_signExtend_32_64_uw]

-- ----------------------------------------------------------------------------
-- Honest-advice guards
-- ----------------------------------------------------------------------------

/-- **Guard 1 — `VirtualAssertMulUNoOverflow v2 v1`.**

`q × zext_divisor` doesn't overflow 64 bits unsigned: `q` is a u32 (so
`q.toNat < 2^32`) and `zext_divisor.toNat < 2^32`, hence the product is
< `2^64`. -/
theorem hguard_no_overflow_of_honest_uw (dividend divisor : BitVec 64) :
    let q  := sail_divuw_advice dividend divisor
    let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
    q.toNat * zv.toNat < 2^64 := by
  intro q zv
  have hq : q.toNat < 2^32 := sail_divuw_advice_toNat_lt_u32 dividend divisor
  have hzv : zv.toNat < 2^32 := zeroExtend_extractLsb_toNat_lt_u32 divisor
  nlinarith

/-- **Guard 2 — `VirtualAssertLTE v3 v0`.**

The unsigned division identity: for non-zero divisor,
`q × zext_divisor ≤ zext_dividend`. For zero divisor `q = u32::MAX`
but `q × 0 = 0 ≤ zext_dividend`. -/
theorem hguard_q_times_d_le_dividend_of_honest_uw (dividend divisor : BitVec 64) :
    let q  := sail_divuw_advice dividend divisor
    let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
    let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
    (q * zv).toNat ≤ zd.toNat := by
  intro q zd zv
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  by_cases hzero : y32 = 0#32
  · have hzv : zv = 0#64 := by
      change zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) = 0#64
      rw [← hy32, hzero]
      unfold zero_extend Sail.BitVec.zeroExtend
      decide
    rw [hzv, BitVec.mul_zero]
    simp
  · have hq : q = zero_extend (m := 64) (x32 / y32) := by
      change sail_divuw_advice dividend divisor = zero_extend (m := 64) (x32 / y32)
      rw [sail_divuw_advice_of_normal dividend divisor (by
        intro h
        exact hzero (by rw [hy32]; exact h)), ← hx32, ← hy32]
    rw [hq]
    have hmul :
        (zero_extend (m := 64) (x32 / y32) *
          zero_extend (m := 64) y32).toNat =
          (x32.toNat / y32.toNat) * y32.toNat := by
      rw [zeroExtend32_mul_toNat_uw, BitVec.toNat_udiv]
    rw [show zd = zero_extend (m := 64) x32 by rw [hx32],
      show zv = zero_extend (m := 64) y32 by rw [hy32],
      hmul, zeroExtend32_64_toNat_uw]
    exact Nat.div_mul_le_self x32.toNat y32.toNat

/-- **Guard 3 — `VirtualAssertValidUnsignedRemainder v3 v1`.**

Either `zext_divisor = 0` (vacuous) or
`(zext_dividend − q × zext_divisor).toNat < zext_divisor.toNat`. -/
theorem hguard_rem_bound_of_honest_uw (dividend divisor : BitVec 64) :
    let q  := sail_divuw_advice dividend divisor
    let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
    let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
    zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat := by
  intro q zd zv
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  by_cases hzero : y32 = 0#32
  · left
    change zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) = 0#64
    rw [← hy32, hzero]
    unfold zero_extend Sail.BitVec.zeroExtend
    decide
  · right
    have hyNat_ne : y32.toNat ≠ 0 := by
      intro h
      apply hzero
      apply BitVec.eq_of_toNat_eq
      simp [h]
    have hq : q = zero_extend (m := 64) (x32 / y32) := by
      change sail_divuw_advice dividend divisor = zero_extend (m := 64) (x32 / y32)
      rw [sail_divuw_advice_of_normal dividend divisor (by
        intro h
        exact hzero (by rw [hy32]; exact h)), ← hx32, ← hy32]
    have hzd : zd = zero_extend (m := 64) x32 := by rw [hx32]
    have hzv : zv = zero_extend (m := 64) y32 := by rw [hy32]
    have hmul :
        (zero_extend (m := 64) (x32 / y32) *
          zero_extend (m := 64) y32).toNat =
          (x32.toNat / y32.toNat) * y32.toNat := by
      rw [zeroExtend32_mul_toNat_uw, BitVec.toNat_udiv]
    have hprod_le :
        (zero_extend (m := 64) (x32 / y32) *
          zero_extend (m := 64) y32).toNat ≤
          (zero_extend (m := 64) x32).toNat := by
      rw [hmul, zeroExtend32_64_toNat_uw]
      exact Nat.div_mul_le_self x32.toNat y32.toNat
    rw [hq, hzd, hzv, toNat_sub_of_le_uw hprod_le, hmul,
      zeroExtend32_64_toNat_uw, zeroExtend32_64_toNat_uw]
    rw [Nat.mul_comm (x32.toNat / y32.toNat) y32.toNat,
      ← Nat.mod_eq_sub_mul_div]
    exact Nat.mod_lt x32.toNat (Nat.pos_of_ne_zero hyNat_ne)

/-- **Guard 4 — `VirtualAssertValidDiv0 v1 v3` (on sign-extended quotient).**

When the (zero-extended) divisor is zero, the spec forces
`q = u32::MAX`, whose sign-extension to 64 bits is `-1`. -/
theorem hguard_div0_of_honest_uw (dividend divisor : BitVec 64) :
    let q  := sail_divuw_advice dividend divisor
    let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
    ¬ (zv = 0#64 ∧
       sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ≠ (-1 : BitVec 64)) := by
  intro q zv
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  by_cases hzero : y32 = 0#32
  · rintro ⟨_, hq⟩
    exact hq (signExtend_extract_sail_divuw_advice_of_zero dividend divisor
      (by rw [← hy32]; exact hzero))
  · rintro ⟨hzv, _⟩
    apply hzero
    apply eq_zero_of_zeroExtend32_eq_zero_uw y32
    change zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) = 0#64 at hzv
    rw [← hy32] at hzv
    exact hzv

-- ----------------------------------------------------------------------------
-- Soundness of the writeback value
-- ----------------------------------------------------------------------------

private theorem advice_eq_honest_of_guards_uw_of_nonzero
    (dividend divisor q : BitVec 64)
    (hnez : Sail.BitVec.extractLsb divisor 31 0 ≠ 0#32)
    (h1 : q.toNat *
            (zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)).toNat
          < 2^64)
    (h2 :
      let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
      let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
      (q * zv).toNat ≤ zd.toNat)
    (h3 :
      let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
      let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
      zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat)
    :
    q = sail_divuw_advice dividend divisor := by
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  have hy_ne : y32 ≠ 0#32 := by
    intro h
    exact hnez h
  have hyNat_ne : y32.toNat ≠ 0 := by
    intro h
    apply hy_ne
    apply BitVec.eq_of_toNat_eq
    simp [h]
  let zd := zero_extend (m := 64) x32
  let zv := zero_extend (m := 64) y32
  have hzd_orig :
      zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) = zd := by
    rw [← hx32]
  have hzv_orig :
      zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) = zv := by
    rw [← hy32]
  have hprod_toNat : (q * zv).toNat = q.toNat * zv.toNat := by
    apply toNat_mul_of_no_overflow_uw
    rw [← hzv_orig]
    exact h1
  have hprod_le : q.toNat * zv.toNat ≤ zd.toNat := by
    rw [← hprod_toNat]
    rw [← hzd_orig, ← hzv_orig]
    exact h2
  have hrem_lt : (zd - q * zv).toNat < zv.toNat := by
    have h3' := h3
    rw [hzd_orig, hzv_orig] at h3'
    rcases h3' with hz | hlt
    · exfalso
      apply hy_ne
      apply eq_zero_of_zeroExtend32_eq_zero_uw y32
      exact hz
    · exact hlt
  have hsub_nat : zd.toNat - q.toNat * zv.toNat < zv.toNat := by
    rw [← hprod_toNat]
    rw [← toNat_sub_of_le_uw]
    · exact hrem_lt
    · rw [hprod_toNat]
      exact hprod_le
  have hq_nat : q.toNat = x32.toNat / y32.toNat := by
    have hquot :=
      nat_quotient_unique_of_mul_le_and_sub_lt_uw
        (a := zd.toNat) (b := zv.toNat) (q := q.toNat)
        (by rw [zeroExtend32_64_toNat_uw]; exact hyNat_ne)
        hprod_le hsub_nat
    rw [zeroExtend32_64_toNat_uw, zeroExtend32_64_toNat_uw] at hquot
    exact hquot
  have hhonest :
      sail_divuw_advice dividend divisor =
        zero_extend (m := 64) (x32 / y32) := by
    rw [sail_divuw_advice_of_normal dividend divisor hnez, ← hx32, ← hy32]
  rw [hhonest]
  apply BitVec.eq_of_toNat_eq
  rw [zeroExtend32_64_toNat_uw, BitVec.toNat_udiv]
  exact hq_nat

/-- **Writeback-value soundness.** If the four DIVUW guards hold for
some raw 64-bit advice `q`, then the value written after the
`SignExtendWord` phase is exactly Sail's DIVUW result. This is the right
DIVUW soundness shape: raw advice is not unique in the divisor-zero case,
but its low 32 bits still sign-extend to the architectural result. -/
theorem sext_advice_eq_sail_divw_value_of_guards_uw
    (dividend divisor q : BitVec 64)
    (h1 : q.toNat *
            (zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)).toNat
          < 2^64)
    (h2 :
      let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
      let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
      (q * zv).toNat ≤ zd.toNat)
    (h3 :
      let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
      let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
      zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat)
    (h4 :
      let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
      ¬ (zv = 0#64 ∧
         sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) ≠ (-1 : BitVec 64))) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) =
      sail_divw_value dividend divisor true := by
  by_cases hzero : Sail.BitVec.extractLsb divisor 31 0 = 0#32
  · have hzv : zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0) = 0#64 := by
      rw [hzero]
      unfold zero_extend Sail.BitVec.zeroExtend
      decide
    have hsext_q :
        sign_extend (m := 64) (Sail.BitVec.extractLsb q 31 0) =
          (-1 : BitVec 64) := by
      by_contra hne
      exact h4 ⟨hzv, hne⟩
    have hsail : sail_divw_value dividend divisor true = (-1 : BitVec 64) := by
      have hhonest := signExtend_extract_sail_divuw_advice_of_zero dividend divisor hzero
      rw [sext_advice_eq_sail_divw_value dividend divisor] at hhonest
      exact hhonest
    rw [hsext_q, hsail]
  · have hq :
        q = sail_divuw_advice dividend divisor :=
      advice_eq_honest_of_guards_uw_of_nonzero dividend divisor q hzero h1 h2 h3
    rw [hq]
    exact sext_advice_eq_sail_divw_value dividend divisor

end
