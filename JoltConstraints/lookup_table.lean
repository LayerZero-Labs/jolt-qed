import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fintype.Fin
import JoltConstraints.witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Split a 128-bit lookup address into its two interleaved 64-bit operands
`(x, y)`. Counting from the least significant end, `x` takes the odd bits and
`y` takes the even bits. Mirrors the Rust bit trick line by line: mask out one
operand's bits, repeatedly close the gaps between them, then truncate to 64 bits.
Rust: crates/jolt-lookup-tables/src/interleave.rs::uninterleave_bits. -/
def uninterleave (address : Fin (2 ^ 128)) : BitVec 64 × BitVec 64 :=
  let val := BitVec.ofFin address
  let xBits := (val >>> 1) &&& 0x5555_5555_5555_5555_5555_5555_5555_5555#128
  let yBits := val &&& 0x5555_5555_5555_5555_5555_5555_5555_5555#128

  let xBits := (xBits ||| (xBits >>> 1)) &&& 0x3333_3333_3333_3333_3333_3333_3333_3333#128
  let xBits := (xBits ||| (xBits >>> 2)) &&& 0x0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0F#128
  let xBits := (xBits ||| (xBits >>> 4)) &&& 0x00FF_00FF_00FF_00FF_00FF_00FF_00FF_00FF#128
  let xBits := (xBits ||| (xBits >>> 8)) &&& 0x0000_FFFF_0000_FFFF_0000_FFFF_0000_FFFF#128
  let xBits := (xBits ||| (xBits >>> 16)) &&& 0x0000_0000_FFFF_FFFF_0000_0000_FFFF_FFFF#128
  let xBits := (xBits ||| (xBits >>> 32)) &&& 0x0000_0000_0000_0000_FFFF_FFFF_FFFF_FFFF#128

  let yBits := (yBits ||| (yBits >>> 1)) &&& 0x3333_3333_3333_3333_3333_3333_3333_3333#128
  let yBits := (yBits ||| (yBits >>> 2)) &&& 0x0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0F_0F0F#128
  let yBits := (yBits ||| (yBits >>> 4)) &&& 0x00FF_00FF_00FF_00FF_00FF_00FF_00FF_00FF#128
  let yBits := (yBits ||| (yBits >>> 8)) &&& 0x0000_FFFF_0000_FFFF_0000_FFFF_0000_FFFF#128
  let yBits := (yBits ||| (yBits >>> 16)) &&& 0x0000_0000_FFFF_FFFF_0000_0000_FFFF_FFFF#128
  let yBits := (yBits ||| (yBits >>> 32)) &&& 0x0000_0000_0000_0000_FFFF_FFFF_FFFF_FFFF#128

  (xBits.setWidth 64, yBits.setWidth 64)

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

/-- The ANDN table: `x & !y` on the uninterleaved operands.
Rust: crates/jolt-lookup-tables/src/tables/andn.rs. -/
noncomputable def andnTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  ((x &&& ~~~y).toNat : F)

/-- The EQUAL table: `1` if the operands are equal, otherwise `0`.
Rust: crates/jolt-lookup-tables/src/tables/equal.rs. -/
noncomputable def equalTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  if x = y then 1 else 0

/-- The NOT_EQUAL table: `1` if the operands differ, otherwise `0`.
Rust: crates/jolt-lookup-tables/src/tables/not_equal.rs. -/
noncomputable def notEqualTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  if x ≠ y then 1 else 0

/-- The UNSIGNED_LESS_THAN table. `BitVec` order is unsigned, like Rust's `u64`.
Rust: crates/jolt-lookup-tables/src/tables/unsigned_less_than.rs. -/
noncomputable def unsignedLessThanTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  if x < y then 1 else 0

/-- The UNSIGNED_LESS_THAN_EQUAL table.
Rust: crates/jolt-lookup-tables/src/tables/unsigned_less_than_equal.rs. -/
noncomputable def unsignedLessThanEqualTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  if x ≤ y then 1 else 0

/-- The UNSIGNED_GREATER_THAN_EQUAL table.
Rust: crates/jolt-lookup-tables/src/tables/unsigned_greater_than_equal.rs. -/
noncomputable def unsignedGreaterThanEqualTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  if x ≥ y then 1 else 0

/-- The SIGNED_LESS_THAN table. Rust first sign-extends the low `XLEN` bits;
with `XLEN = 64` the shift is zero, so `x as i64` is just `x.toInt`.
Rust: crates/jolt-lookup-tables/src/tables/signed_less_than.rs. -/
noncomputable def signedLessThanTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  if x.toInt < y.toInt then 1 else 0

/-- The SIGNED_GREATER_THAN_EQUAL table, with the same sign handling as
`signedLessThanTableEntry`.
Rust: crates/jolt-lookup-tables/src/tables/signed_greater_than_equal.rs. -/
noncomputable def signedGreaterThanEqualTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  if x.toInt ≥ y.toInt then 1 else 0

/-- The RANGE_CHECK table: the low 64 bits of the address.
Rust: crates/jolt-lookup-tables/src/tables/range_check.rs. -/
noncomputable def rangeCheckTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  (((index &&& ((1#128 <<< 64) - 1)).setWidth 64).toNat : F)

/-- The RANGE_CHECK_ALIGNED table: the low 64 bits with bit 0 cleared.
Rust: crates/jolt-lookup-tables/src/tables/range_check_aligned.rs. -/
noncomputable def rangeCheckAlignedTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  (((index &&& ((1#128 <<< 64) - 1)).setWidth 64 &&& ~~~1#64).toNat : F)

/-- The ALIGN_ADDR table: the low 64 bits with bits 0–2 cleared.
Rust: crates/jolt-lookup-tables/src/tables/align_addr.rs. -/
noncomputable def alignAddrTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  (((index &&& ((1#128 <<< 64) - 1)).setWidth 64 &&& ~~~7#64).toNat : F)

/-- The UPPER_WORD table: the high 64 bits of the address.
Rust: crates/jolt-lookup-tables/src/tables/upper_word.rs. -/
noncomputable def upperWordTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  (((index >>> 64).setWidth 64).toNat : F)

/-- The LOWER_HALF_WORD table: the low 32 bits of the address.
Rust: crates/jolt-lookup-tables/src/tables/lower_half_word.rs. -/
noncomputable def lowerHalfWordTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  (((index % (1#128 <<< 32)).setWidth 64).toNat : F)

/-- The SIGN_MASK table: all 64 ones if address bit 127 is set, otherwise `0`.
Rust: crates/jolt-lookup-tables/src/tables/sign_mask.rs. -/
noncomputable def signMaskTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  let signBit := 1#128 <<< 127
  if index &&& signBit ≠ 0 then ((((1#128 <<< 64) - 1).setWidth 64).toNat : F) else 0

/-- The SIGN_EXTEND_WORD table: sign-extend the low 32 bits to 64 bits.
Rust: crates/jolt-lookup-tables/src/tables/sign_extend_word.rs. -/
noncomputable def signExtendWordTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  let lowerHalf := (index % (1#128 <<< 32)).setWidth 64
  let signBit := (lowerHalf >>> 31) &&& 1
  if signBit = 1 then
    ((lowerHalf ||| (((1#64 <<< 32) - 1) <<< 32)).toNat : F)
  else
    (lowerHalf.toNat : F)

/-- The POW2 table: `2 ^ (index mod 64)`.
Rust: crates/jolt-lookup-tables/src/tables/pow2.rs. -/
noncomputable def pow2TableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  ((1#64 <<< (index % 64).toNat).toNat : F)

/-- The POW2_W table: `2 ^ (index mod 32)`.
Rust: crates/jolt-lookup-tables/src/tables/pow2_w.rs. -/
noncomputable def pow2WTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  ((1#64 <<< (index % 32).toNat).toNat : F)

/-- The SHIFT_RIGHT_BITMASK table: ones in bits `shift` through 63, where
`shift = index mod 64`.
Rust: crates/jolt-lookup-tables/src/tables/shift_right_bitmask.rs. -/
noncomputable def shiftRightBitmaskTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  let shift := (index % 64).toNat
  let ones := ((1#128 <<< (64 - shift)) - 1).setWidth 64
  ((ones <<< shift).toNat : F)

/-- The SHIFT_RIGHT_BITMASK_W table: ones in bits `shift` through 31, where
`shift = index mod 32`.
Rust: crates/jolt-lookup-tables/src/tables/shift_right_bitmask_w.rs. -/
noncomputable def shiftRightBitmaskWTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  let shift := (index % 32).toNat
  ((((1#128 <<< 32) - (1#128 <<< shift)).setWidth 64).toNat : F)

/-- The HALFWORD_ALIGNMENT table: `1` if the address is a multiple of 2.
Rust: crates/jolt-lookup-tables/src/tables/halfword_alignment.rs. -/
noncomputable def halfwordAlignmentTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  if index % 2 = 0 then 1 else 0

/-- The WORD_ALIGNMENT table: `1` if the address is a multiple of 4.
Rust: crates/jolt-lookup-tables/src/tables/word_alignment.rs. -/
noncomputable def wordAlignmentTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  if index % 4 = 0 then 1 else 0

/-- The MULU_NO_OVERFLOW table: `1` if the high 64 bits of the address are zero.
Rust: crates/jolt-lookup-tables/src/tables/mulu_no_overflow.rs. -/
noncomputable def mulUNoOverflowTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  let upperBits := index >>> 64
  if upperBits = 0 then 1 else 0

/-- The VALID_DIV0 table: when the divisor is zero the quotient must be all
ones (`u64::MAX`); any nonzero divisor is accepted.
Rust: crates/jolt-lookup-tables/src/tables/valid_div0.rs. -/
noncomputable def validDiv0TableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (divisor, quotient) := uninterleave address
  if divisor = 0 then
    let maxVal := ((1#128 <<< 64) - 1).setWidth 64
    if quotient = maxVal then 1 else 0
  else
    1

/-- The VALID_UNSIGNED_REMAINDER table: `1` if the divisor is zero or the
remainder is below the divisor (unsigned).
Rust: crates/jolt-lookup-tables/src/tables/valid_unsigned_remainder.rs. -/
noncomputable def validUnsignedRemainderTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (remainder, divisor) := uninterleave address
  if divisor = 0 ∨ remainder < divisor then 1 else 0

/-- `Table_q(x)` from constraint (39) in `constraints.md`: the fixed table's
field value at the 128-bit Boolean address `x`. Tables not implemented yet
fall through to the placeholder. -/
noncomputable def lookupTableEntry {F : Type} [Field F]
    (table : LookupTableKind) (address : Fin (2 ^ 128)) : F :=
  match table with
  | .RangeCheck => rangeCheckTableEntry address
  | .RangeCheckAligned => rangeCheckAlignedTableEntry address
  | .And => andTableEntry address
  | .Andn => andnTableEntry address
  | .Or => orTableEntry address
  | .Xor => xorTableEntry address
  | .VirtualXORROTL1 => virtualXorRotL1TableEntry address
  | .Equal => equalTableEntry address
  | .SignedGreaterThanEqual => signedGreaterThanEqualTableEntry address
  | .UnsignedGreaterThanEqual => unsignedGreaterThanEqualTableEntry address
  | .NotEqual => notEqualTableEntry address
  | .SignedLessThan => signedLessThanTableEntry address
  | .UnsignedLessThan => unsignedLessThanTableEntry address
  | .SignMask => signMaskTableEntry address
  | .UpperWord => upperWordTableEntry address
  | .UnsignedLessThanEqual => unsignedLessThanEqualTableEntry address
  | .ValidUnsignedRemainder => validUnsignedRemainderTableEntry address
  | .ValidDiv0 => validDiv0TableEntry address
  | .HalfwordAlignment => halfwordAlignmentTableEntry address
  | .WordAlignment => wordAlignmentTableEntry address
  | .LowerHalfWord => lowerHalfWordTableEntry address
  | .SignExtendWord => signExtendWordTableEntry address
  | .Pow2 => pow2TableEntry address
  | .Pow2W => pow2WTableEntry address
  | .ShiftRightBitmask => shiftRightBitmaskTableEntry address
  | .MulUNoOverflow => mulUNoOverflowTableEntry address
  | .ShiftRightBitmaskW => shiftRightBitmaskWTableEntry address
  | .AlignAddr => alignAddrTableEntry address
  | _ => by sorry

end JoltConstraints
