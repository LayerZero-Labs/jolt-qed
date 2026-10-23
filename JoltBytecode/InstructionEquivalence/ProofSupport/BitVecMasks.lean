import Mathlib.Data.BitVec
import Mathlib.Tactic

/-! Bit-mask identities shared by bytecode equivalence and constraint completeness. -/

set_option autoImplicit false

namespace BitVec

/-- Keeping the low `n` bits and restoring width `w` equals masking by `n` ones.
For example, keeping eight bits of an RV64 value masks it with `0xff`. -/
theorem setWidth_setWidth_eq_and_mask {w : Nat} (x : BitVec w) (n : Nat) :
    (x.setWidth n).setWidth w = x &&& (BitVec.allOnes n).setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, Bool.and_comm]

/-- Clearing positions selected by `mask` preserves `x` when those bits are zero.
For example, an eight-byte-aligned address is unchanged by masking with `~~~7`. -/
theorem and_not_eq_self_of_and_eq_zero {w : Nat} (x mask : BitVec w) (h : x &&& mask = 0) :
    x &&& ~~~mask = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbit := congrArg (fun v : BitVec w => v.getLsbD i) h
  simp only [getLsbD_and] at hbit
  simp only [getLsbD_and, getLsbD_not, hi, decide_true, Bool.true_and]
  cases hx : x.getLsbD i <;> simp_all

/-- A shifted mask reads the same natural-number bits at any width that contains them.
`bound` confines the mask to `bits` low bits; `fits` retains those bits after shifting.
For example, shifting by two and masking with one reads bit two at widths 64 and 128. -/
theorem ofNat_ushiftRight_and_toNat (n mask shift bits width : Nat)
    (bound : mask < 2 ^ bits) (fits : bits + shift ≤ width) :
    ((BitVec.ofNat width n >>> shift) &&& BitVec.ofNat width mask).toNat =
      (n >>> shift) &&& mask := by
  have maskFits : mask < 2 ^ width :=
    bound.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [toNat_and, toNat_ushiftRight, toNat_ofNat, Nat.mod_eq_of_lt maskFits]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
  by_cases hm : mask.testBit i = true
  · have ib : i < bits := by
      by_contra hn
      have := Nat.testBit_lt_two_pow
        (bound.trans_le (Nat.pow_le_pow_right (by decide) (by omega : bits ≤ i)))
      simp_all
    simp [hm, show shift + i < width by omega]
  · simp [hm]

/-- A zero low-bit mask certifies alignment at another width.
`hw` ensures the modulus fits, and `hv` ensures all tested bits survive.
For example, a zero mask `3` at width 64 implies remainder zero modulo four at width 128. -/
theorem ofNat_umod_pow2_eq_zero_of_low_mask {w v : Nat} (n bits : Nat)
    (hw : bits < w) (hv : bits ≤ v)
    (h : BitVec.ofNat v n &&& BitVec.ofNat v (2 ^ bits - 1) = 0) :
    BitVec.ofNat w n % BitVec.ofNat w (2 ^ bits) = 0 := by
  have maskFits : 2 ^ bits - 1 < 2 ^ bits := by have := Nat.two_pow_pos bits; omega
  have low := congrArg BitVec.toNat h
  have masked := ofNat_ushiftRight_and_toNat n (2 ^ bits - 1) 0 bits v maskFits (by omega)
  simp only [BitVec.ushiftRight_zero, Nat.shiftRight_zero,
    Nat.and_two_pow_sub_one_eq_mod] at masked
  rw [masked] at low
  change n % 2 ^ bits = 0 at low
  apply BitVec.eq_of_toNat_eq
  change (n % 2 ^ w) % (2 ^ bits % 2 ^ w) = 0
  rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hw),
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hw.le)]
  exact low

/-- Truncating and restoring a masked, shifted value preserves every selected bit.
`bound` confines `mask` to `bits` low bits, and `fits` keeps them within width `v`.
For example, masking by seven after a zero shift agrees at widths 64 and 128. -/
theorem ushiftRight_and_setWidth {w v : Nat} (x : BitVec w)
    (mask shift bits : Nat) (bound : mask < 2 ^ bits)
    (fits : bits + shift ≤ v) (wide : v ≤ w) :
    (x >>> shift) &&& BitVec.ofNat w mask =
      ((x.setWidth v >>> shift) &&& BitVec.ofNat v mask).setWidth w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le wide]
  have large := ofNat_ushiftRight_and_toNat x.toNat mask shift bits w bound (fits.trans wide)
  have small := ofNat_ushiftRight_and_toNat x.toNat mask shift bits v bound fits
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using large.trans small.symm

end BitVec
