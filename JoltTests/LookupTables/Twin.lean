import Mathlib.Algebra.BigOperators.Ring.Finset
import JoltConstraints.lookup_table

/-!
# A computable twin of the lookup tables

`JoltConstraints.lookupTableEntry` (`JoltConstraints/lookup_table.lean`) gives each
of the 55 lookup tables as a value in an arbitrary field `F`, so it is
noncomputable and cannot be evaluated on test vectors.
This file defines `lookupTableEntryNat`, the same tables with values in `Nat`,
and proves `lookupTableEntry_eq_twin`: at every table and every 128-bit address,
the field table is the cast of the `Nat` table.

Each twin `<table>Nat` is a copy of `JoltConstraints.<table>` with the cast to
`F` removed: a sum of `if … then (2 : F) ^ i else 0` becomes the same sum in
`Nat`, an `if … then 1 else 0` becomes the same `if` in `Nat`, and a final
`(v.toNat : F)` becomes `v.toNat`.
Every bit operation is unchanged, so each proof is a cast lemma (`Nat.cast_sum`,
`Nat.cast_ite`, `Nat.cast_pow`) or `rfl` after splitting the operand pair, and
never an argument about bits.

The comparator in `JoltTests/LookupTables/Main.lean` evaluates the twin on the
vectors that Jolt's `materialize_entry` produced.
The theorem carries an agreement at a sampled index over to the field table;
it says nothing about indices that were not sampled.
-/

set_option autoImplicit false

open JoltConstraints
open scoped BigOperators

namespace LookupTables

/-! ## Sum tables -/

/-- Twin of `andTableEntry`: for example, address `3` (both bit-0 operands set)
gives `1`. -/
def andTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  ∑ i : Fin 64,
    if address.val.testBit (2 * i.val + 1) && address.val.testBit (2 * i.val) then
      2 ^ i.val
    else 0

/-- Twin of `orTableEntry`: for example, address `2` gives `1`. -/
def orTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  ∑ i : Fin 64,
    if address.val.testBit (2 * i.val + 1) || address.val.testBit (2 * i.val) then
      2 ^ i.val
    else 0

/-- Twin of `xorTableEntry`: for example, address `3` gives `0`. -/
def xorTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  ∑ i : Fin 64,
    if address.val.testBit (2 * i.val + 1) != address.val.testBit (2 * i.val) then
      2 ^ i.val
    else 0

/-- Twin of `virtualXorRotL1TableEntry`: for example, address `1` (right
operand `1`) gives `2`. -/
def virtualXorRotL1TableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  ∑ i : Fin 64,
    if address.val.testBit (2 * i.val + 1) !=
        address.val.testBit (2 * ((i.val + 63) % 64)) then
      2 ^ i.val
    else 0

/-! ## Tables of the two operands -/

/-- Twin of `andnTableEntry`: `x &&& ~~~y` of the operands. -/
def andnTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  (x &&& ~~~y).toNat

/-- Twin of `equalTableEntry`: `1` when the operands are equal. -/
def equalTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  if x = y then 1 else 0

/-- Twin of `notEqualTableEntry`: `1` when the operands differ. -/
def notEqualTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  if x ≠ y then 1 else 0

/-- Twin of `unsignedLessThanTableEntry`. -/
def unsignedLessThanTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  if x < y then 1 else 0

/-- Twin of `unsignedLessThanEqualTableEntry`. -/
def unsignedLessThanEqualTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  if x ≤ y then 1 else 0

/-- Twin of `unsignedGreaterThanEqualTableEntry`. -/
def unsignedGreaterThanEqualTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  if x ≥ y then 1 else 0

/-- Twin of `signedLessThanTableEntry`. -/
def signedLessThanTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  if x.toInt < y.toInt then 1 else 0

/-- Twin of `signedGreaterThanEqualTableEntry`. -/
def signedGreaterThanEqualTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  if x.toInt ≥ y.toInt then 1 else 0

/-- Twin of `validDiv0TableEntry`: `1` unless the divisor is zero and the
quotient is not all ones. -/
def validDiv0TableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (divisor, quotient) := uninterleave address
  if divisor = 0 then
    let maxVal := ((1#128 <<< 64) - 1).setWidth 64
    if quotient = maxVal then 1 else 0
  else
    1

/-- Twin of `validUnsignedRemainderTableEntry`. -/
def validUnsignedRemainderTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (remainder, divisor) := uninterleave address
  if divisor = 0 ∨ remainder < divisor then 1 else 0

/-- Twin of `virtualNegateIfTableEntry`. -/
def virtualNegateIfTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (signSource, value) := uninterleave address
  let mask := ((1#128 <<< 64) - 1).setWidth 64
  let value := value &&& mask
  if signSource &&& (1#64 <<< 63) = 0 then
    value.toNat
  else
    (-value &&& mask).toNat

/-- Twin of `virtualXorRotTableEntry`: `x ^ y` rotated right by `rotation`. -/
def virtualXorRotTableEntryNat (rotation : Nat) (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  let xorResult := x ^^^ y
  let r := rotation % 64
  let mask := ((1#128 <<< 64) - 1).setWidth 64
  let v := (xorResult &&& mask).setWidth 128
  (((v >>> r) ||| (v <<< (64 - r))).setWidth 64 &&& mask).toNat

/-- Twin of `virtualXorRotWTableEntry`: the low word of `x ^ y` rotated right
within 32 bits by `rotation`. -/
def virtualXorRotWTableEntryNat (rotation : Nat) (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  let r := rotation % 32
  let halfMask := ((1#128 <<< 32) - 1).setWidth 64
  let xorResult := ((x.setWidth 128 ^^^ y.setWidth 128) &&& halfMask.setWidth 128).setWidth 64
  let v := xorResult.setWidth 128
  (((v >>> r) ||| (v <<< (32 - r))).setWidth 64 &&& halfMask).toNat

/-- Twin of `shiftDataBTableEntry`. -/
def shiftDataBTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  let lane := x &&& ((1#128 <<< 8) - 1).setWidth 64
  (lane <<< (8 * (y &&& 7).toNat)).toNat

/-- Twin of `shiftDataHTableEntry`. -/
def shiftDataHTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  let lane := x &&& ((1#128 <<< 16) - 1).setWidth 64
  (lane <<< (8 * (y &&& 6).toNat)).toNat

/-- Twin of `shiftDataWTableEntry`. -/
def shiftDataWTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  let lane := x &&& ((1#128 <<< 32) - 1).setWidth 64
  (lane <<< (8 * (y &&& 4).toNat)).toNat

/-- Twin of `virtualSRLTableEntry`. -/
def virtualSRLTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  let entry := Id.run do
    let mut entry : BitVec 64 := 0
    for i in (List.range 64).reverse do
      let xI := (x >>> i) &&& 1
      let yI := (y >>> i) &&& 1
      entry := entry * (1 + yI)
      entry := entry + xI * yI
    return entry
  entry.toNat

/-- Twin of `virtualSRATableEntry`. -/
def virtualSRATableEntryNat (address : Fin (2 ^ 128)) : Nat :=
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
  (entry + signBit * signExtension).toNat

/-- Twin of `virtualSRLWTableEntry`. -/
def virtualSRLWTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
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
  (entry + signBit * y0 * extension).toNat

/-- Twin of `virtualSRAWTableEntry`. -/
def virtualSRAWTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
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
  (entry + signBit * signExtension).toNat

/-- Twin of `virtualROTRTableEntry`. -/
def virtualROTRTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
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
  (firstSum + secondSum).toNat

/-- Twin of `virtualROTRWTableEntry`. -/
def virtualROTRWTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
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
  (firstSum + secondSum).toNat

/-- Twin of `pextTableEntry`. -/
def pextTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  (pext x y).toNat

/-- Twin of `pextSignedTableEntry`. -/
def pextSignedTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let (x, y) := uninterleave address
  (pextSigned x y).toNat

/-! ## Tables of the whole address -/

/-- Twin of `rangeCheckTableEntry`: the low 64 bits. -/
def rangeCheckTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  ((index &&& ((1#128 <<< 64) - 1)).setWidth 64).toNat

/-- Twin of `rangeCheckAlignedTableEntry`: the low 64 bits with bit 0 cleared. -/
def rangeCheckAlignedTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  ((index &&& ((1#128 <<< 64) - 1)).setWidth 64 &&& ~~~1#64).toNat

/-- Twin of `addressOffsetTableEntry`: for example, width 2 at address 11
gives 2. -/
def addressOffsetTableEntryNat (width : Nat) (address : Fin (2 ^ 128)) : Nat :=
  (BitVec.ofFin address &&& BitVec.ofNat 128 (8 - width)).toNat

/-- Twin of `upperWordTableEntry`: the high 64 bits. -/
def upperWordTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  ((index >>> 64).setWidth 64).toNat

/-- Twin of `lowerHalfWordTableEntry`: the low 32 bits. -/
def lowerHalfWordTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  ((index % (1#128 <<< 32)).setWidth 64).toNat

/-- Twin of `signMaskTableEntry`. -/
def signMaskTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  let signBit := 1#128 <<< 127
  if index &&& signBit ≠ 0 then (((1#128 <<< 64) - 1).setWidth 64).toNat else 0

/-- Twin of `signExtendWordTableEntry`. -/
def signExtendWordTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  let lowerHalf := (index % (1#128 <<< 32)).setWidth 64
  let signBit := (lowerHalf >>> 31) &&& 1
  if signBit = 1 then
    (lowerHalf ||| (((1#64 <<< 32) - 1) <<< 32)).toNat
  else
    lowerHalf.toNat

/-- Twin of `pow2TableEntry`. -/
def pow2TableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  (1#64 <<< (index % 64).toNat).toNat

/-- Twin of `pow2WTableEntry`. -/
def pow2WTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  (1#64 <<< (index % 32).toNat).toNat

/-- Twin of `shiftRightBitmaskTableEntry`. -/
def shiftRightBitmaskTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  let shift := (index % 64).toNat
  let ones := ((1#128 <<< (64 - shift)) - 1).setWidth 64
  (ones <<< shift).toNat

/-- Twin of `shiftRightBitmaskWTableEntry`. -/
def shiftRightBitmaskWTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  let shift := (index % 32).toNat
  (((1#128 <<< 32) - (1#128 <<< shift)).setWidth 64).toNat

/-- Twin of `mulUNoOverflowTableEntry`. -/
def mulUNoOverflowTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  let upperBits := index >>> 64
  if upperBits = 0 then 1 else 0

/-- Twin of `windowMaskBTableEntry`. -/
def windowMaskBTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  let mask := ((1#128 <<< 8) - 1).setWidth 64
  let offset := (index &&& 7).toNat
  (mask <<< (8 * offset)).toNat

/-- Twin of `windowMaskHTableEntry`. -/
def windowMaskHTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  let mask := ((1#128 <<< 16) - 1).setWidth 64
  let offset := (index &&& 6).toNat
  (mask <<< (8 * offset)).toNat

/-- Twin of `windowMaskWTableEntry`. -/
def windowMaskWTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  let mask := ((1#128 <<< 32) - 1).setWidth 64
  let bit2 := ((index >>> 2) &&& 1).toNat
  (mask <<< (32 * bit2)).toNat

/-- Twin of `virtualRev8WTableEntry`. -/
def virtualRev8WTableEntryNat (address : Fin (2 ^ 128)) : Nat :=
  let index := BitVec.ofFin address
  (rev8w (index.setWidth 64)).toNat

/-! ## The twin of `lookupTableEntry` -/

/-- `lookupTableEntry` with values in `Nat`: the same dispatch, with each table
replaced by its twin. For example, `AddressOffsetW` at address 12 gives 4. -/
def lookupTableEntryNat (table : LookupTableKind) (address : Fin (2 ^ 128)) : Nat :=
  match table with
  | .RangeCheck => rangeCheckTableEntryNat address
  | .RangeCheckAligned => rangeCheckAlignedTableEntryNat address
  | .And => andTableEntryNat address
  | .Andn => andnTableEntryNat address
  | .Or => orTableEntryNat address
  | .Xor => xorTableEntryNat address
  | .VirtualXORROTL1 => virtualXorRotL1TableEntryNat address
  | .Equal => equalTableEntryNat address
  | .SignedGreaterThanEqual => signedGreaterThanEqualTableEntryNat address
  | .UnsignedGreaterThanEqual => unsignedGreaterThanEqualTableEntryNat address
  | .NotEqual => notEqualTableEntryNat address
  | .SignedLessThan => signedLessThanTableEntryNat address
  | .UnsignedLessThan => unsignedLessThanTableEntryNat address
  | .SignMask => signMaskTableEntryNat address
  | .UpperWord => upperWordTableEntryNat address
  | .UnsignedLessThanEqual => unsignedLessThanEqualTableEntryNat address
  | .ValidUnsignedRemainder => validUnsignedRemainderTableEntryNat address
  | .ValidDiv0 => validDiv0TableEntryNat address
  | .LowerHalfWord => lowerHalfWordTableEntryNat address
  | .SignExtendWord => signExtendWordTableEntryNat address
  | .Pow2 => pow2TableEntryNat address
  | .Pow2W => pow2WTableEntryNat address
  | .ShiftRightBitmask => shiftRightBitmaskTableEntryNat address
  | .VirtualRev8W => virtualRev8WTableEntryNat address
  | .VirtualSRL => virtualSRLTableEntryNat address
  | .VirtualSRA => virtualSRATableEntryNat address
  | .VirtualROTR => virtualROTRTableEntryNat address
  | .VirtualROTRW => virtualROTRWTableEntryNat address
  | .VirtualNegateIf => virtualNegateIfTableEntryNat address
  | .MulUNoOverflow => mulUNoOverflowTableEntryNat address
  | .VirtualXORROT32 => virtualXorRotTableEntryNat 32 address
  | .VirtualXORROT24 => virtualXorRotTableEntryNat 24 address
  | .VirtualXORROT16 => virtualXorRotTableEntryNat 16 address
  | .VirtualXORROT63 => virtualXorRotTableEntryNat 63 address
  | .VirtualXORROTW16 => virtualXorRotWTableEntryNat 16 address
  | .VirtualXORROTW12 => virtualXorRotWTableEntryNat 12 address
  | .VirtualXORROTW8 => virtualXorRotWTableEntryNat 8 address
  | .VirtualXORROTW7 => virtualXorRotWTableEntryNat 7 address
  | .WindowMaskW => windowMaskWTableEntryNat address
  | .PextSigned => pextSignedTableEntryNat address
  | .VirtualXORROTW22 => virtualXorRotWTableEntryNat 22 address
  | .VirtualXORROTW19 => virtualXorRotWTableEntryNat 19 address
  | .VirtualXORROTW6 => virtualXorRotWTableEntryNat 6 address
  | .ShiftRightBitmaskW => shiftRightBitmaskWTableEntryNat address
  | .VirtualSRLW => virtualSRLWTableEntryNat address
  | .VirtualSRAW => virtualSRAWTableEntryNat address
  | .Pext => pextTableEntryNat address
  | .WindowMaskB => windowMaskBTableEntryNat address
  | .WindowMaskH => windowMaskHTableEntryNat address
  | .ShiftDataB => shiftDataBTableEntryNat address
  | .ShiftDataH => shiftDataHTableEntryNat address
  | .ShiftDataW => shiftDataWTableEntryNat address
  | .AddressOffsetB => addressOffsetTableEntryNat 1 address
  | .AddressOffsetH => addressOffsetTableEntryNat 2 address
  | .AddressOffsetW => addressOffsetTableEntryNat 4 address

/-! ## The equality -/

/-- The field table is the cast of its `Nat` twin, at every table and address.
For example, in any field `F`, `lookupTableEntry (F := F) .AddressOffsetW 12` is
`((lookupTableEntryNat .AddressOffsetW 12 : Nat) : F)`, which is `(4 : F)`.
The proof unfolds both sides and moves the cast with `Nat.cast_sum`,
`Nat.cast_ite` and `Nat.cast_pow`; for tables that end in `(v.toNat : F)`,
`dsimp` closes the goal once the `let`s and the operand-pair `match`es are
reduced on both sides. -/
theorem lookupTableEntry_eq_twin {F : Type} [Field F] (t : LookupTableKind)
    (a : Fin (2 ^ 128)) :
    lookupTableEntry (F := F) t a = (lookupTableEntryNat t a : F) := by
  cases t <;> dsimp only [lookupTableEntry, lookupTableEntryNat]
  -- The sum tables: push the cast through the sum, the `if` and the power.
  case And | Or | Xor | VirtualXORROTL1 =>
    delta andTableEntry andTableEntryNat orTableEntry orTableEntryNat xorTableEntry
      xorTableEntryNat virtualXorRotL1TableEntry virtualXorRotL1TableEntryNat
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero]
  -- The `if … then 1 else 0` tables and the two-branch tables: push the cast
  -- through the `if`.
  case Equal | NotEqual | UnsignedLessThan | UnsignedLessThanEqual | UnsignedGreaterThanEqual
      | SignedLessThan | SignedGreaterThanEqual | ValidDiv0 | ValidUnsignedRemainder
      | VirtualNegateIf | SignMask | SignExtendWord | MulUNoOverflow =>
    delta equalTableEntry equalTableEntryNat notEqualTableEntry notEqualTableEntryNat
      unsignedLessThanTableEntry unsignedLessThanTableEntryNat
      unsignedLessThanEqualTableEntry unsignedLessThanEqualTableEntryNat
      unsignedGreaterThanEqualTableEntry unsignedGreaterThanEqualTableEntryNat
      signedLessThanTableEntry signedLessThanTableEntryNat
      signedGreaterThanEqualTableEntry signedGreaterThanEqualTableEntryNat
      validDiv0TableEntry validDiv0TableEntryNat
      validUnsignedRemainderTableEntry validUnsignedRemainderTableEntryNat
      virtualNegateIfTableEntry virtualNegateIfTableEntryNat
      signMaskTableEntry signMaskTableEntryNat signExtendWordTableEntry signExtendWordTableEntryNat
      mulUNoOverflowTableEntry mulUNoOverflowTableEntryNat
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  -- The remaining tables end in `(v.toNat : F)`; the two sides differ only in
  -- where the cast sits relative to the `let`s and the operand-pair `match`es.
  all_goals
    delta andnTableEntry andnTableEntryNat virtualXorRotTableEntry virtualXorRotTableEntryNat
      virtualXorRotWTableEntry virtualXorRotWTableEntryNat shiftDataBTableEntry
      shiftDataBTableEntryNat shiftDataHTableEntry shiftDataHTableEntryNat shiftDataWTableEntry
      shiftDataWTableEntryNat virtualSRLTableEntry virtualSRLTableEntryNat virtualSRATableEntry
      virtualSRATableEntryNat virtualSRLWTableEntry virtualSRLWTableEntryNat
      virtualSRAWTableEntry virtualSRAWTableEntryNat virtualROTRTableEntry
      virtualROTRTableEntryNat virtualROTRWTableEntry virtualROTRWTableEntryNat pextTableEntry
      pextTableEntryNat pextSignedTableEntry pextSignedTableEntryNat rangeCheckTableEntry
      rangeCheckTableEntryNat rangeCheckAlignedTableEntry rangeCheckAlignedTableEntryNat
      addressOffsetTableEntry addressOffsetTableEntryNat upperWordTableEntry
      upperWordTableEntryNat lowerHalfWordTableEntry lowerHalfWordTableEntryNat pow2TableEntry
      pow2TableEntryNat pow2WTableEntry pow2WTableEntryNat shiftRightBitmaskTableEntry
      shiftRightBitmaskTableEntryNat shiftRightBitmaskWTableEntry shiftRightBitmaskWTableEntryNat
      windowMaskBTableEntry windowMaskBTableEntryNat windowMaskHTableEntry
      windowMaskHTableEntryNat windowMaskWTableEntry windowMaskWTableEntryNat
      virtualRev8WTableEntry virtualRev8WTableEntryNat
    dsimp only

end LookupTables

