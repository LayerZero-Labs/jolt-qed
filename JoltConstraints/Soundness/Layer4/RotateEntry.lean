import JoltConstraints.Soundness.Layer4.Interleave

/-! Pure XOR-rotation identities, shared with completeness. -/

set_option autoImplicit false

namespace JoltConstraints

open TraceWitness Sail PreSail LeanRV64D.Functions

variable {F : Type} [Field F]

/-- Sail right rotation is the union of its two shifted pieces when the shift fits. -/
theorem rotater_eq {n : Nat} (z : BitVec n) (s : Nat) (hs : s ≤ n) :
    rotater z s = (z >>> s) ||| (z <<< (n - s)) := by
  unfold rotater
  have : (Sail.BitVec.length z -i (s : Int)) = ((n - s : Nat) : Int) := by
    simp only [Sail.BitVec.length]; omega
  rw [this]
  rfl

/-- Rotating a 64-bit word left once moves bit 63 into bit zero. -/
theorem rotatel_one (z : BitVec 64) : rotatel z 1 = (z <<< 1) ||| (z >>> 63) := rfl

/-- Each result bit XORs the left bit with the preceding bit of the right word, wrapping at zero. -/
theorem xorRotL1_getLsbD (x y : BitVec 64) (i : Nat) (hi : i < 64) :
    (x ^^^ ((y <<< 1) ||| (y >>> 63))).getLsbD i = (x.getLsbD i != y.getLsbD ((i + 63) % 64)) := by
  change (x ^^^ y.rotateLeft 1).getLsbD i = _
  by_cases zero : i = 0
  · subst i
    simp [bne]
  · have index : (i + 63) % 64 = i - 1 := by omega
    have previous : i - 1 < 64 := by omega
    simp [hi, zero, index, previous, bne]

/-- VirtualXORROTL1 XORs the left word with the right word rotated left once. -/
theorem xorRotL1_entry (l r : BitVec 64) :
    virtualXorRotL1TableEntry (F := F) (interleaveLookupOperands l r).toFin =
      ((jolt_virtual_xorrotl1_value l r).toNat : F) := by
  rw [jolt_virtual_xorrotl1_value, rotatel_one, bitVec_toNat_cast_eq_sum]
  unfold virtualXorRotL1TableEntry
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [BitVec.val_toFin, interleave_testBit_odd l r i i.isLt,
    interleave_testBit_even l r _ (Nat.mod_lt _ (by omega)), xorRotL1_getLsbD l r i i.isLt]

private theorem rotate_wide {width : Nat} (x : BitVec width) (rotation : Nat)
    (fits : width ≤ 128) :
    ((x.setWidth 128 >>> rotation) ||| (x.setWidth 128 <<< (width - rotation))).setWidth width =
      (x >>> rotation) ||| (x <<< (width - rotation)) := by
  rw [BitVec.setWidth_or, ← BitVec.setWidth_ushiftRight fits,
    BitVec.setWidth_shiftLeft_of_le fits]
  simp only [BitVec.setWidth_setWidth_of_le _ fits, BitVec.setWidth_eq]

private theorem mask32 (x : BitVec 64) :
    x &&& 0xFFFF_FFFF#64 = (x.setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  change x.toNat &&& (2 ^ 32 - 1) = (x.toNat % 2 ^ 32) % 2 ^ 64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact (Nat.mod_eq_of_lt (by
    have := Nat.mod_lt x.toNat (by decide : 0 < 2 ^ 32)
    omega)).symm

/-- Each supported 64-bit XOR-rotate table agrees with its instruction value. -/
theorem xorRot_entry (r : Nat) (hr : r = 32 ∨ r = 24 ∨ r = 16 ∨ r = 63) (l y : BitVec 64) :
    virtualXorRotTableEntry (F := F) r (interleaveLookupOperands l y).toFin =
      ((jolt_virtual_xorrot_value r l y).toNat : F) := by
  have hr64 : r < 64 := by omega
  have mask : ((1#128 <<< 64) - 1).setWidth 64 = BitVec.allOnes 64 := by decide
  simp only [virtualXorRotTableEntry, uninterleave_interleave, jolt_virtual_xorrot_value,
    rotater_eq _ r hr64.le, Nat.mod_eq_of_lt hr64, mask, BitVec.and_allOnes,
    rotate_wide _ _ (by decide : 64 ≤ 128)]

/-- Each supported W XOR-rotate table rotates 32 bits and zero-extends the result. -/
theorem xorRotW_entry (r : Nat)
    (hr : r = 16 ∨ r = 12 ∨ r = 8 ∨ r = 7 ∨ r = 22 ∨ r = 19 ∨ r = 6) (l y : BitVec 64) :
    virtualXorRotWTableEntry (F := F) r (interleaveLookupOperands l y).toFin =
      ((jolt_virtual_xorrotw_value r l y).toNat : F) := by
  have hr32 : r < 32 := by omega
  have mask : ((1#128 <<< 32) - 1).setWidth 64 = 0xFFFF_FFFF#64 := by decide
  simp only [virtualXorRotWTableEntry, uninterleave_interleave, jolt_virtual_xorrotw_value,
    rotater_eq _ r hr32.le, Nat.mod_eq_of_lt hr32, mask, BitVec.setWidth_and,
    BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128),
    BitVec.setWidth_eq, mask32, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
    zero_extend, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
  simp only [BitVec.setWidth_setWidth (by omega : ¬ (64 < 32 ∧ 64 < 128))]
  rw [← BitVec.setWidth_xor, rotate_wide _ _ (by decide : 32 ≤ 128)]
  rfl

end JoltConstraints
