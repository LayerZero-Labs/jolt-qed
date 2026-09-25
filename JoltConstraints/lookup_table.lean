import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fintype.Fin
import JoltConstraints.witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The AND table at a Boolean address:

  And(address) = ∑_{i=0}^{63} 2ⁱ · address[2i+1] · address[2i].

Bits are numbered from the least significant end. The left operand occupies
odd positions and the right operand occupies even positions. A result bit is
set exactly when both corresponding operand bits are set.
Rust: crates/jolt-lookup-tables/src/tables/and.rs. -/
noncomputable def andTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  ∑ i : Fin 64,
    if address.val.testBit (2 * i.val + 1) && address.val.testBit (2 * i.val) then
      (2 : F) ^ i.val
    else 0

/-- The OR table at a Boolean address:

  Or(address) = ∑_{i=0}^{63} 2ⁱ · (aᵢ + bᵢ − aᵢ bᵢ),

where aᵢ = address[2i+1] and bᵢ = address[2i], counting from the least
significant bit. A result bit is set when either operand bit is set.
Rust: crates/jolt-lookup-tables/src/tables/or.rs. -/
noncomputable def orTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  ∑ i : Fin 64,
    if address.val.testBit (2 * i.val + 1) || address.val.testBit (2 * i.val) then
      (2 : F) ^ i.val
    else 0

/-- The XOR table at a Boolean address:

  Xor(address) = ∑_{i=0}^{63} 2ⁱ · (aᵢ + bᵢ − 2 aᵢ bᵢ),

where aᵢ = address[2i+1] and bᵢ = address[2i], counting from the least
significant bit. A result bit is set when exactly one operand bit is set.
Rust: crates/jolt-lookup-tables/src/tables/xor.rs. -/
noncomputable def xorTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  ∑ i : Fin 64,
    if address.val.testBit (2 * i.val + 1) != address.val.testBit (2 * i.val) then
      (2 : F) ^ i.val
    else 0

/-- XOR with the right operand rotated left once, at a Boolean address:

  VirtualXORROTL1(address) = ∑ᵢ 2ⁱ · (a[i] XOR b[(i+63) mod 64]).

Here aᵢ = address[2i+1] and bᵢ = address[2i], counting from the least
significant bit. In particular, result bit zero uses the right operand's bit 63.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-lookup-tables/src/tables/virtual_xor_rotl1.rs -/
noncomputable def virtualXorRotL1TableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  ∑ i : Fin 64,
    if address.val.testBit (2 * i.val + 1) !=
        address.val.testBit (2 * ((i.val + 63) % 64)) then
      (2 : F) ^ i.val
    else 0

/-- `Table_q(x)` from constraint (39) in `constraints.md`: the fixed table's
field value at the 128-bit Boolean address `x`. AND, OR, XOR, and VirtualXORROTL1
are implemented; the remaining tables are placeholders. -/
noncomputable def lookupTableEntry {F : Type} [Field F]
    (table : LookupTableKind) (address : Fin (2 ^ 128)) : F :=
  match table with
  | .And => andTableEntry address
  | .Or => orTableEntry address
  | .Xor => xorTableEntry address
  | .VirtualXORROTL1 => virtualXorRotL1TableEntry address
  | _ => by sorry

end JoltConstraints
