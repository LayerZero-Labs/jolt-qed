import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import JoltConstraints.translation.Constraints.InstructionLookupRa

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Deinterleave the left operand: odd bit positions counted from the least
significant bit. Equivalently, use even positions in the MSB-first bit vector.
Rust: https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs -/
noncomputable def lookupAddressLeft {F : Type} [Field F] (address : Fin (2 ^ 128)) : F :=
  ∑ bit : Fin 64, if address.val.testBit (2 * bit.val + 1) then (2 : F) ^ bit.val else 0

/-- Deinterleave the right operand: even bit positions counted from the least
significant bit. The identity RAF instead uses the entire 128-bit address. -/
noncomputable def lookupAddressRight {F : Type} [Field F] (address : Fin (2 ^ 128)) : F :=
  ∑ bit : Fin 64, if address.val.testBit (2 * bit.val) then (2 : F) ^ bit.val else 0

end JoltConstraints
