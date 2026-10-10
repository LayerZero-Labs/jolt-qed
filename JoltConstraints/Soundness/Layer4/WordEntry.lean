import JoltConstraints.Soundness.Layer4.RangeCheckEntry
import JoltConstraints.Soundness.Layer4.ShiftEntry

/-! Pure word, alignment and mask table identities shared with completeness. -/

set_option autoImplicit false

namespace JoltConstraints

variable {F : Type} [Field F]

private theorem low32_value (v : BitVec 128) :
    (v % (1#128 <<< 32)).setWidth 64 = (v.setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_umod]
  rfl

private theorem signExtend32_value (x : BitVec 32) :
    x.signExtend 64 =
      if x.msb then x.setWidth 64 ||| (((1#64 <<< 32) - 1) <<< 32)
      else x.setWidth 64 := by
  have mask : (((1#64 <<< 32) - 1) <<< 32) =
      ~~~((BitVec.allOnes 32).setWidth 64) := by decide
  rw [mask]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases low : i < 32 <;> cases sign : x.msb <;>
    simp only [sign, Bool.false_eq_true, ↓reduceIte,
      BitVec.getLsbD_signExtend, BitVec.getLsbD_or, BitVec.getLsbD_not,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, hi, low,
      decide_true, decide_false, Bool.true_and, Bool.and_true,
      Bool.not_true, Bool.not_false, Bool.or_true, Bool.or_false]
  exact (BitVec.getLsbD_of_ge x i (by omega)).symm

/-- SignExtendWord sign-extends the low 32 address bits. -/
theorem signExtendWord_entry (v : BitVec 128) :
    signExtendWordTableEntry (F := F) v.toFin =
      (((v.setWidth 32).signExtend 64).toNat : F) := by
  simp only [signExtendWordTableEntry, BitVec.ofFin_toFin, low32_value]
  rw [ShiftTables.bit_word, BitVec.getLsbD_setWidth]
  have sign : (v.setWidth 32).getLsbD 31 = (v.setWidth 32).msb :=
    (BitVec.msb_eq_getLsbD_last _).symm
  rw [sign, signExtend32_value]
  cases (v.setWidth 32).msb <;> simp

/-- UpperWord returns the quotient by 2^64 of an address below 2^128. -/
theorem upperWord_entry (n : Nat) (hn : n < 2 ^ 128) :
    upperWordTableEntry (F := F) (BitVec.ofNat 128 n).toFin =
      ((BitVec.ofNat 64 (n / 2 ^ 64)).toNat : F) := by
  unfold upperWordTableEntry
  simp only [BitVec.ofFin_toFin]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hn]

/-- LowerHalfWord zero-extends the low 32 address bits. -/
theorem lowerHalfWord_entry (v : BitVec 128) :
    lowerHalfWordTableEntry (F := F) v.toFin = (((v.setWidth 32).setWidth 64).toNat : F) := by
  simp only [lowerHalfWordTableEntry, BitVec.ofFin_toFin, low32_value]

/-- RangeCheckAligned takes the low 64 bits and clears bit zero. -/
theorem rangeCheckAligned_entry (v : BitVec 128) :
    rangeCheckAlignedTableEntry (F := F) v.toFin =
      ((v.setWidth 64 &&& ~~~1#64).toNat : F) := by
  unfold rangeCheckAlignedTableEntry
  have h : (v &&& ((1#128 <<< 64) - 1)).setWidth 64 = v.setWidth 64 := by
    have mask : (((1#128 <<< 64) - 1).setWidth 64) = BitVec.allOnes 64 := by decide
    simp only [BitVec.setWidth_and, mask, BitVec.and_allOnes]
  simp only [BitVec.ofFin_toFin, h]

/-- AlignAddr takes the low 64 bits and clears the three lowest bits. -/
theorem alignAddr_entry (v : BitVec 128) :
    alignAddrTableEntry (F := F) v.toFin =
      ((v.setWidth 64 &&& ~~~7#64).toNat : F) := by
  unfold alignAddrTableEntry
  have h : (v &&& ((1#128 <<< 64) - 1)).setWidth 64 = v.setWidth 64 := by
    have mask : (((1#128 <<< 64) - 1).setWidth 64) = BitVec.allOnes 64 := by decide
    simp only [BitVec.setWidth_and, mask, BitVec.and_allOnes]
  simp only [BitVec.ofFin_toFin, h]

/-- An exactly encoded modulus gives the same remainder as natural-number division. -/
theorem umod_toNat (v : BitVec 128) (m : Nat) (hm : m < 2 ^ 128) :
    (v % BitVec.ofNat 128 m).toNat = v.toNat % m := by
  simp only [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm]

/-- Pow2 sets the bit indexed by the address modulo 64. -/
theorem pow2_entry (v : BitVec 128) :
    pow2TableEntry (F := F) v.toFin = ((BitVec.ofNat 64 (2 ^ (v.toNat % 64))).toNat : F) := by
  unfold pow2TableEntry
  simp only [BitVec.ofFin_toFin, one_shiftLeft_eq]
  rw [show (64 : BitVec 128) = BitVec.ofNat 128 64 from rfl, umod_toNat _ _ (by norm_num)]

/-- Pow2W sets the bit indexed by the address modulo 32. -/
theorem pow2W_entry (v : BitVec 128) :
    pow2WTableEntry (F := F) v.toFin = ((BitVec.ofNat 64 (2 ^ (v.toNat % 32))).toNat : F) := by
  unfold pow2WTableEntry
  simp only [BitVec.ofFin_toFin, one_shiftLeft_eq]
  rw [show (32 : BitVec 128) = BitVec.ofNat 128 32 from rfl, umod_toNat _ _ (by norm_num)]

/-- The concrete 128-bit mask computation gives the expected 64-bit word. -/
theorem shiftRightBitmask_value (s : Nat) (hs : s < 64) :
    ((1#128 <<< (64 - s)) - 1).setWidth 64 <<< s =
      BitVec.ofNat 64 (((1 <<< (64 - s)) - 1) <<< s) := by
  interval_cases s <;> decide

/-- ShiftRightBitmask sets exactly the bits at or above the address modulo 64. -/
theorem shiftRightBitmask_entry (v : BitVec 128) :
    shiftRightBitmaskTableEntry (F := F) v.toFin =
      ((BitVec.ofNat 64 (((1 <<< (64 - v.toNat % 64)) - 1) <<< (v.toNat % 64))).toNat : F) := by
  unfold shiftRightBitmaskTableEntry
  simp only [BitVec.ofFin_toFin]
  rw [show (64 : BitVec 128) = BitVec.ofNat 128 64 from rfl, umod_toNat _ _ (by norm_num),
    shiftRightBitmask_value _ (Nat.mod_lt _ (by norm_num))]

/-- The concrete W mask computation gives the expected low-32-bit mask. -/
theorem shiftRightBitmaskW_value (s : Nat) (hs : s < 32) :
    ((1#128 <<< 32) - (1#128 <<< s)).setWidth 64 = BitVec.ofNat 64 (2 ^ 32 - 2 ^ s) := by
  interval_cases s <;> decide

/-- ShiftRightBitmaskW sets the bits from the address modulo 32 through bit 31. -/
theorem shiftRightBitmaskW_entry (v : BitVec 128) :
    shiftRightBitmaskWTableEntry (F := F) v.toFin =
      ((BitVec.ofNat 64 (2 ^ 32 - 2 ^ (v.toNat % 32))).toNat : F) := by
  unfold shiftRightBitmaskWTableEntry
  simp only [BitVec.ofFin_toFin]
  rw [show (32 : BitVec 128) = BitVec.ofNat 128 32 from rfl, umod_toNat _ _ (by norm_num),
    shiftRightBitmaskW_value _ (Nat.mod_lt _ (by norm_num))]

end JoltConstraints
