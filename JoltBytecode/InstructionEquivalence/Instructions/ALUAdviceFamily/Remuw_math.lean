import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Divuw_math
import JoltBytecode.InstructionEquivalence.Instructions.ALUAdviceFamily.Remu_math

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# Math content for `remuwProgram`

REMUW is REMU over the low 32-bit unsigned operands, followed by
sign-extension of the low 32-bit remainder.
-/

private theorem mod33_toNat_mod32_remuw (x : Int) :
    (x % 8589934592).toNat % 4294967296
      = (x % 4294967296).toNat := by
  apply Int.ofNat.inj
  simp [Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (8589934592 : Int) ≠ 0)),
        Int.toNat_of_nonneg
          (Int.emod_nonneg _ (by norm_num : (4294967296 : Int) ≠ 0))]

private theorem trunc32_eq_intCast_remuw (x : Int) :
    to_bits_truncate (l := 32) x = (x : BitVec 32) := by
  apply BitVec.eq_of_toFin_eq
  rw [show to_bits_truncate (l := 32) x
        = BitVec.ofNat 32 ((x % 8589934592).toNat) by
        simp [to_bits_truncate, get_slice_int, BitVec.extractLsb']]
  rw [BitVec.toFin_ofNat, BitVec.toFin_intCast]
  ext
  simpa [Fin.ofNat] using mod33_toNat_mod32_remuw x

private lemma zeroExtend32_64_toNat_remuw (x : BitVec 32) :
    (zero_extend (m := 64) x).toNat = x.toNat := by
  unfold zero_extend Sail.BitVec.zeroExtend
  rw [BitVec.toNat_setWidth]
  apply Nat.mod_eq_of_lt
  have hx := x.isLt
  omega

private lemma extractLsb_zeroExtend_32_64_remuw (x : BitVec 32) :
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

private theorem trunc32_of_toNat_remuw (x : BitVec 32) :
    to_bits_truncate (l := 32) (Int.ofNat x.toNat) = x := by
  rw [trunc32_eq_intCast_remuw]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_intCast]
  rw [Int.emod_eq_of_lt]
  · exact Int.toNat_natCast _
  · exact Int.natCast_nonneg x.toNat
  · exact Int.ofNat_lt.mpr x.isLt

private theorem trunc32_tmod_eq_umod_remuw (x y : BitVec 32)
    (hy : y ≠ 0#32) :
    to_bits_truncate (l := 32)
        ((Int.ofNat x.toNat).tmod (Int.ofNat y.toNat)) =
      x % y := by
  have hyNat_ne : y.toNat ≠ 0 := by
    intro h
    apply hy
    apply BitVec.eq_of_toNat_eq
    simp [h]
  rw [trunc32_eq_intCast_remuw]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_intCast, BitVec.toNat_umod]
  have htmod :
      (Int.ofNat x.toNat).tmod (Int.ofNat y.toNat)
        = (x.toNat % y.toNat : Nat) := by
    exact (Int.ofNat_tmod x.toNat y.toNat).symm
  rw [Int.emod_eq_of_lt]
  · rw [htmod]
    exact Int.toNat_natCast _
  · rw [htmod]
    exact Int.natCast_nonneg (x.toNat % y.toNat)
  · rw [htmod]
    have hlt : x.toNat % y.toNat < 2^32 := by
      exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero hyNat_ne))
        (Nat.le_of_lt y.isLt)
    exact Int.ofNat_lt.mpr hlt

private theorem sail_remw_value_of_zero_uw (dividend divisor : BitVec 64)
    (hzero : Sail.BitVec.extractLsb divisor 31 0 = 0#32) :
    sail_remw_value dividend divisor true =
      sign_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0) := by
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  unfold sail_remw_value
  rw [← hx32, hzero]
  simp only [BitVec.toNatInt, BitVec.toNat_zero, beq_iff_eq, ↓reduceIte]
  rw [if_pos (show Int.ofNat 0 = 0 from rfl)]
  rw [trunc32_of_toNat_remuw x32]

private theorem sail_remw_value_of_normal_uw (dividend divisor : BitVec 64)
    (hnez : Sail.BitVec.extractLsb divisor 31 0 ≠ 0#32) :
    sail_remw_value dividend divisor true =
      sign_extend (m := 64)
        (Sail.BitVec.extractLsb dividend 31 0 %
         Sail.BitVec.extractLsb divisor 31 0) := by
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  have hy_ne : y32 ≠ 0#32 := by
    intro h
    exact hnez (by rw [hy32]; exact h)
  have hyNat_ne : y32.toNat ≠ 0 := by
    intro h
    apply hy_ne
    apply BitVec.eq_of_toNat_eq
    simp [h]
  unfold sail_remw_value
  rw [← hx32, ← hy32]
  simp only [BitVec.toNatInt, beq_iff_eq, ↓reduceIte]
  have hbeq_false : ¬ Int.ofNat y32.toNat = 0 := by
    intro h
    exact hyNat_ne (Int.ofNat_eq_zero.mp h)
  rw [if_neg hbeq_false]
  rw [trunc32_tmod_eq_umod_remuw x32 y32 hy_ne]

private lemma zeroExtend32_eq_zero_iff_remuw (x : BitVec 32) :
    zero_extend (m := 64) x = 0#64 ↔ x = 0#32 := by
  constructor
  · intro h
    have hx := congrArg (fun z : BitVec 64 => Sail.BitVec.extractLsb z 31 0) h
    change Sail.BitVec.extractLsb (zero_extend (m := 64) x) 31 0 =
      Sail.BitVec.extractLsb (0#64) 31 0 at hx
    rw [extractLsb_zeroExtend_32_64_remuw] at hx
    simpa using hx
  · intro h
    rw [h]
    unfold zero_extend Sail.BitVec.zeroExtend
    decide

/-- The 64-bit REMU result over zero-extended low words sign-extends to
Sail's REMUW result. -/
theorem signExtend_extract_sail_rem_value_zext_eq_sail_remw_uw
    (dividend divisor : BitVec 64) :
    let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
    let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
    sign_extend (m := 64)
        (Sail.BitVec.extractLsb (sail_rem_value zd zv true) 31 0)
      = sail_remw_value dividend divisor true := by
  intro zd zv
  set x32 := Sail.BitVec.extractLsb dividend 31 0 with hx32
  set y32 := Sail.BitVec.extractLsb divisor 31 0 with hy32
  have hzd : zd = zero_extend (m := 64) x32 := by
    unfold zd
    rw [← hx32]
  have hzv : zv = zero_extend (m := 64) y32 := by
    unfold zv
    rw [← hy32]
  by_cases hzero : y32 = 0#32
  · have hzv_zero : zv = 0#64 := by
      rw [hzv, hzero]
      unfold zero_extend Sail.BitVec.zeroExtend
      decide
    have hrem : sail_rem_value zd zv true = zd :=
      sail_rem_value_of_zero_remu zd zv hzv_zero
    have hsail : sail_remw_value dividend divisor true =
        sign_extend (m := 64) x32 := by
      rw [sail_remw_value_of_zero_uw dividend divisor (by rw [← hy32]; exact hzero),
        ← hx32]
    rw [hrem, hsail, hzd, extractLsb_zeroExtend_32_64_remuw]
  · have hzv_ne : zv ≠ 0#64 := by
      intro hz
      apply hzero
      rw [← zeroExtend32_eq_zero_iff_remuw y32]
      rw [← hzv]
      exact hz
    have hrem : sail_rem_value zd zv true = zd % zv :=
      sail_rem_value_of_normal_remu zd zv hzv_ne
    have hsail : sail_remw_value dividend divisor true =
        sign_extend (m := 64) (x32 % y32) := by
      rw [sail_remw_value_of_normal_uw dividend divisor (by
        intro h
        exact hzero (by rw [hy32]; exact h)), ← hx32, ← hy32]
    have hmod_zext : zd % zv = zero_extend (m := 64) (x32 % y32) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_umod, hzd, hzv, zeroExtend32_64_toNat_remuw,
        zeroExtend32_64_toNat_remuw, zeroExtend32_64_toNat_remuw, BitVec.toNat_umod]
    rw [hrem, hsail, hmod_zext, extractLsb_zeroExtend_32_64_remuw]

theorem signExtend_remainder_eq_sail_remw_of_guards_uw
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
      zv = 0#64 ∨ (zd - q * zv).toNat < zv.toNat) :
    let zd := zero_extend (m := 64) (Sail.BitVec.extractLsb dividend 31 0)
    let zv := zero_extend (m := 64) (Sail.BitVec.extractLsb divisor 31 0)
    sign_extend (m := 64)
        (Sail.BitVec.extractLsb (zd - q * zv) 31 0)
      = sail_remw_value dividend divisor true := by
  intro zd zv
  have hrem64 : zd - q * zv = sail_rem_value zd zv true :=
    remainder_eq_sail_rem_of_guards_u zd zv q h1 h2 h3
  rw [hrem64]
  exact signExtend_extract_sail_rem_value_zext_eq_sail_remw_uw dividend divisor

end
