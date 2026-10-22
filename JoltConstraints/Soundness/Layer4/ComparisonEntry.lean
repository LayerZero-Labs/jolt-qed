import JoltConstraints.Soundness.Layer4.Interleave

/-! Comparison table identities shared with completeness. BitVec order is unsigned; signed comparisons use toInt.
These identities hold for arbitrary words and require no execution trace. -/

set_option autoImplicit false

namespace JoltConstraints

open TraceWitness

variable {F : Type} [Field F]

/-- The Equal table returns one exactly when the two words are equal. -/
theorem equal_entry (l r : BitVec 64) :
    equalTableEntry (F := F) (interleaveLookupOperands l r).toFin = if l = r then 1 else 0 := by
  simp only [equalTableEntry, uninterleave_interleave]

/-- The NotEqual table returns one exactly when the two words differ. -/
theorem notEqual_entry (l r : BitVec 64) :
    notEqualTableEntry (F := F) (interleaveLookupOperands l r).toFin = if l ≠ r then 1 else 0 := by
  simp only [notEqualTableEntry, uninterleave_interleave]

/-- The unsigned less-than table compares the words as natural numbers. -/
theorem unsignedLessThan_entry (l r : BitVec 64) :
    unsignedLessThanTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if l < r then 1 else 0 := by
  simp only [unsignedLessThanTableEntry, uninterleave_interleave]

/-- The unsigned less-than-or-equal table compares the words as natural numbers. -/
theorem unsignedLessThanEqual_entry (l r : BitVec 64) :
    unsignedLessThanEqualTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if l ≤ r then 1 else 0 := by
  simp only [unsignedLessThanEqualTableEntry, uninterleave_interleave]

/-- The unsigned greater-than-or-equal table compares the words as natural numbers. -/
theorem unsignedGreaterThanEqual_entry (l r : BitVec 64) :
    unsignedGreaterThanEqualTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if l ≥ r then 1 else 0 := by
  simp only [unsignedGreaterThanEqualTableEntry, uninterleave_interleave]

/-- The signed less-than table compares the words as signed integers. -/
theorem signedLessThan_entry (l r : BitVec 64) :
    signedLessThanTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if l.toInt < r.toInt then 1 else 0 := by
  simp only [signedLessThanTableEntry, uninterleave_interleave]

/-- The signed greater-than-or-equal table compares the words as signed integers. -/
theorem signedGreaterThanEqual_entry (l r : BitVec 64) :
    signedGreaterThanEqualTableEntry (F := F) (interleaveLookupOperands l r).toFin =
      if l.toInt ≥ r.toInt then 1 else 0 := by
  simp only [signedGreaterThanEqualTableEntry, uninterleave_interleave]

end JoltConstraints
