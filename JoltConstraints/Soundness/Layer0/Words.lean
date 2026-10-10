import JoltConstraints.Soundness.Layer0.Field
import Mathlib.Data.BitVec

set_option autoImplicit false

namespace JoltConstraints.Soundness

/-- A characteristic above `2^127` covers the entire 64-bit word range. -/
theorem two_pow_64_lt_char {F : Type} [Field F]
    (charAbove2pow127 : 2 ^ 127 < ringChar F) : 2 ^ 64 < ringChar F :=
  lt_of_le_of_lt
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 64 ≤ 127)) charAbove2pow127

/-- A machine word's natural-number value is below the characteristic. -/
theorem word_toNat_lt_char {F : Type} [Field F]
    (charAbove2pow127 : 2 ^ 127 < ringChar F) (word : BitVec 64) :
    word.toNat < ringChar F :=
  lt_trans word.isLt (two_pow_64_lt_char charAbove2pow127)

/-- Equality of field encodings gives equality of 64-bit machine words.
The bounds needed for cast injectivity follow from the word type and `charAbove2pow127`. -/
theorem word_eq_of_field_eq {F : Type} [Field F]
    (charAbove2pow127 : 2 ^ 127 < ringChar F) {a b : BitVec 64}
    (same : (a.toNat : F) = (b.toNat : F)) : a = b :=
  BitVec.eq_of_toNat_eq (natCast_injective_below_char
    (word_toNat_lt_char charAbove2pow127 a) (word_toNat_lt_char charAbove2pow127 b) same)

end JoltConstraints.Soundness
