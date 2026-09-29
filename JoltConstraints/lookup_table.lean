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

/-- The VIRTUAL_NEGATE_IF table: `value`, negated (mod 2⁶⁴) when the sign bit
of `signSource` is set.
Rust: crates/jolt-lookup-tables/src/tables/virtual_negate_if.rs. -/
noncomputable def virtualNegateIfTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (signSource, value) := uninterleave address
  let mask := ((1#128 <<< 64) - 1).setWidth 64
  let value := value &&& mask
  if signSource &&& (1#64 <<< 63) = 0 then
    (value.toNat : F)
  else
    ((-value &&& mask).toNat : F)

/-- The VIRTUAL_XOR_ROT tables: `x ^ y` rotated right by `rotation` bits.
`VirtualXORROT32`, `24`, `16` and `63` are this table at those rotations.
Rust: crates/jolt-lookup-tables/src/tables/virtual_xor_rot.rs::VirtualXORROTTable. -/
noncomputable def virtualXorRotTableEntry {F : Type} [Field F]
    (rotation : Nat) (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  let xorResult := x ^^^ y
  let r := rotation % 64
  let mask := ((1#128 <<< 64) - 1).setWidth 64
  let v := (xorResult &&& mask).setWidth 128
  ((((v >>> r) ||| (v <<< (64 - r))).setWidth 64 &&& mask).toNat : F)

/-- The VIRTUAL_XOR_ROTW tables: the low 32 bits of `x ^ y`, rotated right
within 32 bits by `rotation`. `VirtualXORROTW16`, `12`, `8`, `7`, `22`, `19`
and `6` are this table at those rotations.
Rust: crates/jolt-lookup-tables/src/tables/virtual_xor_rotw.rs::VirtualXORROTWTable. -/
noncomputable def virtualXorRotWTableEntry {F : Type} [Field F]
    (rotation : Nat) (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  let r := rotation % 32
  let halfMask := ((1#128 <<< 32) - 1).setWidth 64
  let xorResult := ((x.setWidth 128 ^^^ y.setWidth 128) &&& halfMask.setWidth 128).setWidth 64
  let v := xorResult.setWidth 128
  ((((v >>> r) ||| (v <<< (32 - r))).setWidth 64 &&& halfMask).toNat : F)

/-- The SHIFT_DATA_B table: the low byte of `x`, shifted left by
`8 * (y & 7)` bits.
Rust: crates/jolt-lookup-tables/src/tables/shift_data_b.rs. -/
noncomputable def shiftDataBTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  let lane := x &&& ((1#128 <<< 8) - 1).setWidth 64
  ((lane <<< (8 * (y &&& 7).toNat)).toNat : F)

/-- The SHIFT_DATA_H table: the low halfword of `x`, shifted left by
`8 * (y & 6)` bits.
Rust: crates/jolt-lookup-tables/src/tables/shift_data_h.rs. -/
noncomputable def shiftDataHTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  let lane := x &&& ((1#128 <<< 16) - 1).setWidth 64
  ((lane <<< (8 * (y &&& 6).toNat)).toNat : F)

/-- The SHIFT_DATA_W table: the low word of `x`, shifted left by
`8 * (y & 4)` bits.
Rust: crates/jolt-lookup-tables/src/tables/shift_data_w.rs. -/
noncomputable def shiftDataWTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  let lane := x &&& ((1#128 <<< 32) - 1).setWidth 64
  ((lane <<< (8 * (y &&& 4).toNat)).toNat : F)

/-- The WINDOW_MASK_B table: a one-byte mask shifted left by
`8 * (index & 7)` bits.
Rust: crates/jolt-lookup-tables/src/tables/window_mask_b.rs. -/
noncomputable def windowMaskBTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  let mask := ((1#128 <<< 8) - 1).setWidth 64
  let offset := (index &&& 7).toNat
  ((mask <<< (8 * offset)).toNat : F)

/-- The WINDOW_MASK_H table: a two-byte mask shifted left by
`8 * (index & 6)` bits.
Rust: crates/jolt-lookup-tables/src/tables/window_mask_h.rs. -/
noncomputable def windowMaskHTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  let mask := ((1#128 <<< 16) - 1).setWidth 64
  let offset := (index &&& 6).toNat
  ((mask <<< (8 * offset)).toNat : F)

/-- The WINDOW_MASK_W table: a four-byte mask, shifted left by 32 bits when
address bit 2 is set.
Rust: crates/jolt-lookup-tables/src/tables/window_mask_w.rs. -/
noncomputable def windowMaskWTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  let mask := ((1#128 <<< 32) - 1).setWidth 64
  let bit2 := ((index >>> 2) &&& 1).toNat
  ((mask <<< (32 * bit2)).toNat : F)

/-- Rust's `u32::swap_bytes`: reverse the byte order of a 32-bit word. -/
def swapBytes32 (w : BitVec 32) : BitVec 32 :=
  ((w &&& 0xFF) <<< 24) ||| ((w &&& 0xFF00) <<< 8) ||| ((w >>> 8) &&& 0xFF00) ||| (w >>> 24)

/-- Reverse the bytes within each 32-bit half of a 64-bit word.
Rust: crates/jolt-lookup-tables/src/tables/virtual_rev8w.rs::rev8w. -/
def rev8w (v : BitVec 64) : BitVec 64 :=
  let lo := swapBytes32 (v.setWidth 32)
  let hi := swapBytes32 ((v >>> 32).setWidth 32)
  lo.setWidth 64 + (hi.setWidth 64 <<< 32)

/-- The VIRTUAL_REV8W table: `rev8w` of the low 64 bits of the address.
Rust: crates/jolt-lookup-tables/src/tables/virtual_rev8w.rs. -/
noncomputable def virtualRev8WTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let index := BitVec.ofFin address
  ((rev8w (index.setWidth 64)).toNat : F)

/-- The VIRTUAL_SRL table. Rust reads each operand most significant bit first
with `LookupBits::pop_msb`, which here is bit `i` for `i = 63, …, 0`.
Rust: crates/jolt-lookup-tables/src/tables/virtual_srl.rs. -/
noncomputable def virtualSRLTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  let entry := Id.run do
    let mut entry : BitVec 64 := 0
    for i in (List.range 64).reverse do
      let xI := (x >>> i) &&& 1
      let yI := (y >>> i) &&& 1
      entry := entry * (1 + yI)
      entry := entry + xI * yI
    return entry
  (entry.toNat : F)

/-- The VIRTUAL_SRA table. The loop's `i`-th `pop_msb` reads bit `63 - i`, and
Rust's `leading_ones() != 0` holds exactly when the top bit of `x` is set.
Rust: crates/jolt-lookup-tables/src/tables/virtual_sra.rs. -/
noncomputable def virtualSRATableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  let signBit : BitVec 64 := if x.msb then 1 else 0
  let (entry, signExtension) := Id.run do
    let mut entry : BitVec 64 := 0
    let mut signExtension : BitVec 64 := 0
    for i in List.range 64 do
      let xI := (x >>> (63 - i)) &&& 1
      let yI := (y >>> (63 - i)) &&& 1
      entry := entry * (1 + yI)
      entry := entry + xI * yI
      if i ≠ 0 then
        signExtension := signExtension + (1#64 <<< i) * (1 - yI)
    return (entry, signExtension)
  ((entry + signBit * signExtension).toNat : F)

/-- The VIRTUAL_SRLW table. Rust first pops and discards the top 32 bits of
each operand, so the loop reads bits 31, …, 0 and the sign bit is bit 31.
Rust: crates/jolt-lookup-tables/src/tables/virtual_srlw.rs. -/
noncomputable def virtualSRLWTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  let signBit : BitVec 64 := if x.getLsbD 31 then 1 else 0
  let (entry, y0) := Id.run do
    let mut entry : BitVec 64 := 0
    let mut y0 : BitVec 64 := 0
    for i in (List.range 32).reverse do
      let xI := (x >>> i) &&& 1
      let yI := (y >>> i) &&& 1
      entry := entry * (1 + yI) + xI * yI
      y0 := yI
    return (entry, y0)
  let extension := ((1#128 <<< 64) - (1#128 <<< 32)).setWidth 64
  ((entry + signBit * y0 * extension).toNat : F)

/-- The VIRTUAL_SRAW table. As in `virtualSRLWTableEntry` the top 32 bits are
discarded first; the loop's `i`-th `pop_msb` then reads bit `31 - i`.
Rust: crates/jolt-lookup-tables/src/tables/virtual_sraw.rs. -/
noncomputable def virtualSRAWTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  let signBit : BitVec 64 := if x.getLsbD 31 then 1 else 0
  let (entry, signExtension) := Id.run do
    let mut entry : BitVec 64 := 0
    let mut signExtension : BitVec 64 := ((1#128 <<< 64) - (1#128 <<< 32)).setWidth 64
    for i in List.range 32 do
      let xI := (x >>> (31 - i)) &&& 1
      let yI := (y >>> (31 - i)) &&& 1
      entry := entry * (1 + yI) + xI * yI
      if i ≠ 0 then
        signExtension := signExtension + (1#64 <<< i) * (1 - yI)
    return (entry, signExtension)
  ((entry + signBit * signExtension).toNat : F)

/-- The VIRTUAL_ROTR table. `prodOnePlusY` is a `u128` in Rust and is
truncated to 64 bits where it is used.
Rust: crates/jolt-lookup-tables/src/tables/virtual_rotr.rs. -/
noncomputable def virtualROTRTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (xBits, yBits) := uninterleave address
  let (firstSum, secondSum) := Id.run do
    let mut prodOnePlusY : BitVec 128 := 1
    let mut firstSum : BitVec 64 := 0
    let mut secondSum : BitVec 64 := 0
    for i in (List.range 64).reverse do
      let x := (xBits >>> i) &&& 1
      let y := (yBits >>> i) &&& 1
      firstSum := firstSum * (1 + y)
      firstSum := firstSum + x * y
      secondSum :=
        secondSum + x * ((1 - y.setWidth 128) * prodOnePlusY).setWidth 64 * (1#64 <<< i)
      prodOnePlusY := prodOnePlusY * (1 + y.setWidth 128)
    return (firstSum, secondSum)
  ((firstSum + secondSum).toNat : F)

/-- The VIRTUAL_ROTRW table: the `virtualROTRTableEntry` loop over bits
31, …, 0 only (Rust's `(0..XLEN).rev().skip(XLEN / 2)`), with every
accumulator a `u64`.
Rust: crates/jolt-lookup-tables/src/tables/virtual_rotrw.rs. -/
noncomputable def virtualROTRWTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (xBits, yBits) := uninterleave address
  let (firstSum, secondSum) := Id.run do
    let mut prodOnePlusY : BitVec 64 := 1
    let mut firstSum : BitVec 64 := 0
    let mut secondSum : BitVec 64 := 0
    for i in (List.range 64).reverse.drop 32 do
      let x := (xBits >>> i) &&& 1
      let y := (yBits >>> i) &&& 1
      firstSum := firstSum * (1 + y)
      firstSum := firstSum + x * y
      secondSum := secondSum + x * (1 - y) * prodOnePlusY * (1#64 <<< i)
      prodOnePlusY := prodOnePlusY * (1 + y)
    return (firstSum, secondSum)
  ((firstSum + secondSum).toNat : F)

/-- Parallel bit extract: pack `x`'s bits at `y`'s set positions toward bit 0,
preserving their order.
Rust: crates/jolt-lookup-tables/src/tables/suffixes/pext.rs::pext. -/
def pext (x y : BitVec 64) : BitVec 64 := Id.run do
  if y = 0 then
    return 0
  let tz := y.ctz.toNat
  let normalized := y >>> tz
  if normalized &&& (normalized + 1) = 0 then
    -- Contiguous mask: extract is a shift plus truncate.
    return (x >>> tz) &&& normalized
  -- General mask: gather one bit per set position, lowest first. Rust loops
  -- `while bits != 0`; each pass clears one set bit, so 64 passes suffice.
  let mut bits := y
  let mut out : BitVec 64 := 0
  let mut k := 0
  for _ in List.range 64 do
    if bits ≠ 0 then
      out := out ||| (((x >>> bits.ctz.toNat) &&& 1) <<< k)
      k := k + 1
      bits := bits &&& (bits - 1)
  return out

/-- `x`'s bit at `y`'s most significant set bit, or `0` if `y` is zero.
Rust: crates/jolt-lookup-tables/src/tables/suffixes/window_sign.rs::window_sign_bit. -/
def windowSignBit (x y : BitVec 64) : BitVec 64 :=
  if y = 0 then 0 else (x >>> y.toNat.log2) &&& 1

/-- `pext x y`, sign-extended above bit `popcount y - 1` by `windowSignBit`.
Rust: crates/jolt-lookup-tables/src/tables/pext_signed.rs::pext_signed. -/
def pextSigned (x y : BitVec 64) : BitVec 64 :=
  let pc := y.cpop.toNat
  if pc = 0 then
    0
  else
    let pext := pext x y
    let sign := windowSignBit x y
    let ext := if sign = 1 then ((1#128 <<< 64) - (1#128 <<< pc)).setWidth 64 else 0
    pext + ext

/-- The PEXT table. Rust's `LookupBits::new(_, 64)` keeps all 64 bits of each
operand, so the operands reach `pext` unchanged.
Rust: crates/jolt-lookup-tables/src/tables/pext.rs. -/
noncomputable def pextTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  ((pext x y).toNat : F)

/-- The PEXT_SIGNED table, with the same operand handling as `pextTableEntry`.
Rust: crates/jolt-lookup-tables/src/tables/pext_signed.rs. -/
noncomputable def pextSignedTableEntry {F : Type} [Field F]
    (address : Fin (2 ^ 128)) : F :=
  let (x, y) := uninterleave address
  ((pextSigned x y).toNat : F)

/-- `Table_q(x)` from constraint (39) in `constraints.md`: the fixed table's
field value at the 128-bit Boolean address `x`. -/
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
  | .VirtualRev8W => virtualRev8WTableEntry address
  | .VirtualSRL => virtualSRLTableEntry address
  | .VirtualSRA => virtualSRATableEntry address
  | .VirtualROTR => virtualROTRTableEntry address
  | .VirtualROTRW => virtualROTRWTableEntry address
  | .VirtualNegateIf => virtualNegateIfTableEntry address
  | .MulUNoOverflow => mulUNoOverflowTableEntry address
  | .VirtualXORROT32 => virtualXorRotTableEntry 32 address
  | .VirtualXORROT24 => virtualXorRotTableEntry 24 address
  | .VirtualXORROT16 => virtualXorRotTableEntry 16 address
  | .VirtualXORROT63 => virtualXorRotTableEntry 63 address
  | .VirtualXORROTW16 => virtualXorRotWTableEntry 16 address
  | .VirtualXORROTW12 => virtualXorRotWTableEntry 12 address
  | .VirtualXORROTW8 => virtualXorRotWTableEntry 8 address
  | .VirtualXORROTW7 => virtualXorRotWTableEntry 7 address
  | .WindowMaskW => windowMaskWTableEntry address
  | .PextSigned => pextSignedTableEntry address
  | .VirtualXORROTW22 => virtualXorRotWTableEntry 22 address
  | .VirtualXORROTW19 => virtualXorRotWTableEntry 19 address
  | .VirtualXORROTW6 => virtualXorRotWTableEntry 6 address
  | .ShiftRightBitmaskW => shiftRightBitmaskWTableEntry address
  | .VirtualSRLW => virtualSRLWTableEntry address
  | .VirtualSRAW => virtualSRAWTableEntry address
  | .Pext => pextTableEntry address
  | .WindowMaskB => windowMaskBTableEntry address
  | .WindowMaskH => windowMaskHTableEntry address
  | .AlignAddr => alignAddrTableEntry address
  | .ShiftDataB => shiftDataBTableEntry address
  | .ShiftDataH => shiftDataHTableEntry address
  | .ShiftDataW => shiftDataWTableEntry address

end JoltConstraints
