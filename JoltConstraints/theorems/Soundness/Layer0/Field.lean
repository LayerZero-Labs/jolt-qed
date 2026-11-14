import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.Defs

set_option autoImplicit false

namespace JoltConstraints.Soundness

/-- The full lookup-address bound implies the weaker bound used for words and chunks. -/
theorem two_pow_127_lt_char {F : Type} [Field F]
    (charAbove2pow128 : 2 ^ 128 < ringChar F) : 2 ^ 127 < ringChar F :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 127 ≤ 128))
    charAbove2pow128

/-- Natural numbers below the characteristic have distinct field encodings. -/
theorem natCast_injective_below_char {F : Type} [Field F] {a b : Nat}
    (ha : a < ringChar F) (hb : b < ringChar F)
    (same : (a : F) = (b : F)) : a = b :=
  CharP.natCast_injOn_Iio F (ringChar F) ha hb same

/-- For any field element, the Booleanity equation forces zero or one. -/
theorem eq_zero_or_one_of_boolean {F : Type} [Field F] {value : F}
    (boolean : value * (value - 1) = 0) : value = 0 ∨ value = 1 := by
  simpa only [sub_eq_zero] using (mul_eq_zero.mp boolean)

end JoltConstraints.Soundness
