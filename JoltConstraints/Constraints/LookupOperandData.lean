import JoltConstraints.Constraints.LookupOutputEqInstructionReadRaf

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Deinterleave the left operand: odd bit positions counted from the least
significant bit. Equivalently, use even positions in the MSB-first bit vector.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs#L181-L201 -/
noncomputable def lookupAddressLeft {F : Type} [Field F] (address : Fin (2 ^ 128)) : F :=
  ∑ bit : Fin 64, if address.val.testBit (2 * bit.val + 1) then (2 : F) ^ bit.val else 0

/-- Deinterleave the right operand: even bit positions counted from the least
significant bit. The identity RAF instead uses the entire 128-bit address. -/
noncomputable def lookupAddressRight {F : Type} [Field F] (address : Fin (2 ^ 128)) : F :=
  ∑ bit : Fin 64, if address.val.testBit (2 * bit.val) then (2 : F) ^ bit.val else 0

end JoltConstraints
