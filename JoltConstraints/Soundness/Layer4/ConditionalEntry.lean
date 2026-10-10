import JoltConstraints.Soundness.Layer4.Interleave

/-! Pure conditional, assertion and store-lane table identities. -/

set_option autoImplicit false

namespace JoltConstraints

open TraceWitness

variable {F : Type} [Field F]

/-- ValidDiv0 requires an all-ones quotient when the divisor is zero. -/
theorem validDiv0_entry (l r : BitVec 64) :
    validDiv0TableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if l = 0 ∧ r ≠ -1 then 0 else 1 := by
  have hmax : ((1#128 <<< 64) - 1).setWidth 64 = (-1 : BitVec 64) := by decide
  simp only [validDiv0TableEntry, uninterleave_interleave, hmax]
  split_ifs <;> simp_all

/-- A remainder is accepted when the divisor is zero or the remainder is smaller. -/
theorem validUnsignedRemainder_entry (l r : BitVec 64) :
    validUnsignedRemainderTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if r = 0 ∨ l < r then 1 else 0 := by
  simp only [validUnsignedRemainderTableEntry, uninterleave_interleave]

/-- SignMask fills the result with the left operand's sign bit. -/
theorem signMask_entry (l r : BitVec 64) :
    signMaskTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      ((if l.msb then (-1 : BitVec 64) else 0).toNat : F) := by
  unfold signMaskTableEntry
  have hbit : (interleaveLookupOperands l r &&& 1#128 <<< 127 ≠ 0) = (l.msb = true) := by
    have h127 := interleave_testBit_odd l r 63 (by omega)
    have hiff : ∀ v : BitVec 128, (v &&& 1#128 <<< 127 ≠ 0) ↔ v.getLsbD 127 = true := by
      intro v
      rw [← BitVec.twoPow_eq, BitVec.and_twoPow]
      cases v.getLsbD 127 <;> decide
    rw [hiff, BitVec.getLsbD, h127, BitVec.msb_eq_getLsbD_last]
  have hones : ((1#128 <<< 64) - 1).setWidth 64 = (-1 : BitVec 64) := by decide
  simp only [BitVec.ofFin_toFin, hbit, hones]
  split <;> simp

/-- VirtualNegateIf negates the right word exactly when the left word is negative. -/
theorem negateIf_entry (l r : BitVec 64) :
    virtualNegateIfTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      ((if l.msb then -r else r).toNat : F) := by
  have hmask : ((1#128 <<< 64) - 1).setWidth 64 = BitVec.allOnes 64 := by decide
  simp only [virtualNegateIfTableEntry, uninterleave_interleave, hmask, BitVec.and_allOnes]
  have hsign : (l &&& 1#64 <<< 63 = 0) ↔ l.msb = false := by
    rw [← BitVec.twoPow_eq, BitVec.and_twoPow, BitVec.msb_eq_getLsbD_last]
    cases l.getLsbD 63 <;> decide
  by_cases hm : l.msb
  · have : ¬ (l &&& 1#64 <<< 63 = 0) := by rw [hsign, hm]; simp
    simp only [this, hm, ↓reduceIte]
  · have : l &&& 1#64 <<< 63 = 0 := by rw [hsign]; simpa using hm
    simp only [this, hm, ↓reduceIte, Bool.false_eq_true]

/-- ShiftDataB places the low byte in the lane selected by the address. -/
theorem shiftDataB_entry (l r : BitVec 64) :
    shiftDataBTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      ((jolt_virtual_shift_data_b_value l r).toNat : F) := by
  have hm : ((1#128 <<< 8) - 1).setWidth 64 = (0xFF : BitVec 64) := by decide
  simp only [shiftDataBTableEntry, uninterleave_interleave, hm, jolt_virtual_shift_data_b_value]

/-- ShiftDataH places the low halfword in the selected aligned lane. -/
theorem shiftDataH_entry (l r : BitVec 64) :
    shiftDataHTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      ((jolt_virtual_shift_data_h_value l r).toNat : F) := by
  have hm : ((1#128 <<< 16) - 1).setWidth 64 = (0xFFFF : BitVec 64) := by decide
  simp only [shiftDataHTableEntry, uninterleave_interleave, hm, jolt_virtual_shift_data_h_value]

/-- ShiftDataW places the low 32-bit word in the selected aligned lane. -/
theorem shiftDataW_entry (l r : BitVec 64) :
    shiftDataWTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      ((jolt_virtual_shift_data_w_value l r).toNat : F) := by
  have hm : ((1#128 <<< 32) - 1).setWidth 64 = (0xFFFF_FFFF : BitVec 64) := by decide
  simp only [shiftDataWTableEntry, uninterleave_interleave, hm, jolt_virtual_shift_data_w_value]

end JoltConstraints
