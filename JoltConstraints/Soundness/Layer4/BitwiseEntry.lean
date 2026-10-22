import JoltConstraints.Soundness.Layer4.Interleave

/-! Bitwise table identities shared with completeness.
These identities hold for arbitrary words and require no execution trace. -/

set_option autoImplicit false

namespace JoltConstraints

open TraceWitness

variable {F : Type} [Field F]

/-- The And table computes bitwise conjunction of the two words. -/
theorem and_entry (l r : BitVec 64) :
    andTableEntry (F := F) (interleaveLookupOperands l r).toFin = ((l &&& r).toNat : F) := by
  rw [bitVec_toNat_cast_eq_sum]
  unfold andTableEntry
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [BitVec.val_toFin, interleave_testBit_odd l r i i.isLt,
    interleave_testBit_even l r i i.isLt, BitVec.getLsbD_and]

/-- The Or table computes bitwise disjunction of the two words. -/
theorem or_entry (l r : BitVec 64) :
    orTableEntry (F := F) (interleaveLookupOperands l r).toFin = ((l ||| r).toNat : F) := by
  rw [bitVec_toNat_cast_eq_sum]
  unfold orTableEntry
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [BitVec.val_toFin, interleave_testBit_odd l r i i.isLt,
    interleave_testBit_even l r i i.isLt, BitVec.getLsbD_or]

/-- The Xor table computes bitwise exclusive-or of the two words. -/
theorem xor_entry (l r : BitVec 64) :
    xorTableEntry (F := F) (interleaveLookupOperands l r).toFin = ((l ^^^ r).toNat : F) := by
  rw [bitVec_toNat_cast_eq_sum]
  unfold xorTableEntry
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [BitVec.val_toFin, interleave_testBit_odd l r i i.isLt,
    interleave_testBit_even l r i i.isLt, BitVec.getLsbD_xor, bne]

/-- The Andn table conjoins the left word with the complement of the right word. -/
theorem andn_entry (l r : BitVec 64) :
    andnTableEntry (F := F) (interleaveLookupOperands l r).toFin = ((l &&& ~~~r).toNat : F) := by
  simp only [andnTableEntry, uninterleave_interleave]

end JoltConstraints
