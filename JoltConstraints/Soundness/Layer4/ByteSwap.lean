import JoltConstraints.lookup_table
import JoltBytecode.JoltISA.Values

/-! Byte-reversal identities shared by soundness and completeness. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions

private theorem append32_eq_add (hi lo : BitVec 32) :
    hi +++ lo = lo.setWidth 64 + (hi.setWidth 64 <<< 32) := by
  apply BitVec.eq_of_toNat_eq
  have hhi := hi.isLt
  have hlo := lo.isLt
  have sumLt : hi.toNat * 2 ^ 32 + lo.toNat < 2 ^ 64 := by omega
  simp only [BitVec.toNat_append, BitVec.toNat_add,
    BitVec.toNat_setWidth_of_le (by norm_num : 32 ≤ 64),
    BitVec.toNat_shiftLeft]
  rw [← Nat.shiftLeft_add_eq_or_of_lt hlo]
  simp only [Nat.shiftLeft_eq]
  omega

/-- Reverse each 32-bit half of `v` separately, then concatenate the results.
For example, bytes `01 02 03 04 05 06 07 08` become `04 03 02 01 08 07 06 05`. -/
theorem rev8w_eq_kernel (v : BitVec 64) :
    rev8w v = swapBytes32 (v.extractLsb 63 32) +++ swapBytes32 (v.extractLsb 31 0) := by
  simp only [rev8w]
  rw [show v.setWidth 32 = v.extractLsb 31 0 by rfl]
  rw [show (v >>> 32).setWidth 32 = v.extractLsb 63 32 by rfl]
  exact (append32_eq_add _ _).symm

/-- Sail's `rev8` agrees with the table's `swapBytes32` on 32-bit words.
For example, both send `0x01020304` to `0x04030201`. -/
theorem rev8_32_kernel (x : BitVec 32) : rev8 x = swapBytes32 x := by
  unfold rev8
  simp only [Id.run]
  change IntRange.forIn' _ _ _ >>= _ = _
  unfold IntRange.forIn'
  simp only [Sail.BitVec.length, BitVec.length, Nat.cast_ofNat]
  iterate 5
    rw [IntRange.forIn'.loop]
    simp (config := { decide := true }) only [Membership.mem, dite_true, dite_false, pure_bind,
      bind_pure, Int.reduceAdd, Int.reduceSub, Int.reduceToNat]
  change BitVec.updateSubrange _ _ _ _ = _
  simp only [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Sail.BitVec.extractLsb,
    zeros, swapBytes32, Nat.reduceSub, Nat.reduceAdd]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  intro hi
  interval_cases i <;> simp (config := { decide := true }) at *

end JoltConstraints.Soundness
