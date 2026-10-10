import JoltConstraints.lookup_table

/-! A pure table identity shared with the completeness proof. It does not
assume an honest trace or an instruction execution. -/

set_option autoImplicit false

namespace JoltConstraints

/-- RangeCheck returns the low 64 bits of the 128-bit lookup address. -/
theorem rangeCheck_entry {F : Type} [Field F] (v : BitVec 128) :
    rangeCheckTableEntry (F := F) v.toFin = ((v.setWidth 64).toNat : F) := by
  have mask : (((1#128 <<< 64) - 1).setWidth 64) = BitVec.allOnes 64 := by decide
  simp only [rangeCheckTableEntry, BitVec.ofFin_toFin, BitVec.setWidth_and, mask,
    BitVec.and_allOnes]

end JoltConstraints
