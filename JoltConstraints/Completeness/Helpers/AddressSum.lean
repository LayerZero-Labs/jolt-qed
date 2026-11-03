import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Algebra.Field.Defs

set_option autoImplicit false

namespace JoltConstraints

/-- Encoding an integer that lies between zero and `2^width` preserves its
field value; for example, encoding 8 in either 64 or 128 bits still gives 8.
Jolt's prover casts these unsigned lookup words into the field in
`crates/jolt-witness/src/witnesses/operands.rs` (`RightLookupOperand::to_field`)
at `c6703570`. -/
theorem encodedInt_cast {F : Type} [Field F] (width : Nat) (value : Int)
    (nonneg : 0 ≤ value) (below : value < 2 ^ width) :
    ((BitVec.ofInt width value).toNat : F) = (value : F) := by
  have exactValue : ((BitVec.ofInt width value).toNat : Int) = value := by
    rw [BitVec.toNat_ofInt, Nat.cast_pow, Nat.cast_ofNat,
      Int.emod_eq_of_lt nonneg below, Int.toNat_of_nonneg nonneg]
  simpa only [Int.cast_natCast] using congrArg (fun z : Int => (z : F)) exactValue

end JoltConstraints
