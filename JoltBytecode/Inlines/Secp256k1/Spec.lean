/-!
# secp256k1 field inlines: moduli, limbs and the integer relations

This file states what Jolt's six secp256k1 field inlines (`SECP256K1_MULQ`, `SQUAREQ`,
`DIVQ` over the base field `p`, and `MULR`, `SQUARER`, `DIVR` over the group order `n`)
guarantee, as integer relations on 256-bit values, following `docs/inline-precompiles.md`
section 3.

Jolt sources, at a16z/jolt `a6b6dc717`:
- `jolt-inlines/secp256k1/src/sequence_builder.rs` (`MulqBuilder::inline_sequence`): the rows.
- `jolt-inlines/sdk/src/host.rs` (`limbs_to_nbiguint`, `nbiguint_to_limbs`): the limb order.

The rows compute `a·b + w·p'` (or `c·b + w·p'` for division) column by column, where
`p' = 2^256 - q`, and check that the low four 64-bit columns are the stored result `c` (for
division: the dividend `a` read again from memory) and that the high four columns equal the
advice quotient `w`, with no overflow out of the top column. With `a`, `b`, `c` and `w` each four
64-bit limbs, that is exactly `a·b + w·p' = c + 2^256·w`, which is `a·b = w·q + c`.
-/

namespace JoltISA.Inlines.Secp256k1

/-- The secp256k1 base-field prime `p = 2^256 - 2^32 - 977`.

Jolt takes it from `ark_secp256k1::Fq::MODULUS` (`sequence_builder.rs`, `secp256k1_modulus`).
Example: `p % 2^64 = 0xFFFFFFFEFFFFFC2F`. -/
def p : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- The secp256k1 group order `n`, the modulus of the scalar field.

Jolt takes it from `ark_secp256k1::Fr::MODULUS` (`sequence_builder.rs`, `secp256k1_modulus`)
and spells the same value as little-endian bytes in `glv.rs` (`r`).
Example: `n % 2^64 = 0xBFD25E8CD0364141`. -/
def n : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- `p'(q) = 2^256 - q`, the constant the rows multiply the quotient by.

Example: `pPrime p = 2^32 + 977 = 0x1000003D1`. -/
def pPrime (q : Nat) : Nat := 2 ^ 256 - q

/-- The closed form of `p`. Example: it says `p = 2^256 - 4294968273`. -/
theorem p_eq : p = 2 ^ 256 - 2 ^ 32 - 977 := by decide

/-- For the base field, `p'` is one limb: the constant `(1 << 32) + 977` loaded by the `LUI` row
in `MulqBuilder::inline_sequence` (`sequence_builder.rs`, the `else` branch after the advice
loop). Example: `pPrime p = 4294968273`. -/
theorem pPrime_p : pPrime p = 2 ^ 32 + 977 := by decide

/-- For the scalar field, `p'` has three limbs, `[0x402da1732fc9bebf, 0x4551231950b75fc4, 1]`:
the rows load the first two with `LUI` into `p` and `p2` and add the third limb `1` as a plain
`ADD` of `w[k-2]` (`MulqBuilder::inline_sequence`). Example: `pPrime n < 2^129`. -/
theorem pPrime_n :
    pPrime n = 0x402da1732fc9bebf + 2 ^ 64 * 0x4551231950b75fc4 + 2 ^ 128 * 1 := by
  decide

/-- Four 64-bit limbs of a 256-bit value, least significant first.

This is how the inlines lay a field element out in memory: `MulqBuilder::inline_sequence`
loads limb `i` with `LD` at byte offset `8·i` and puts its product terms in column `i` (weight
`2^(64·i)`), and `limbs_to_nbiguint` in `jolt-inlines/sdk/src/host.rs` reads the same order.
Example: `#v[1, 0, 0, 0]` is `1` and `#v[0, 1, 0, 0]` is `2^64`. -/
abbrev Limbs := Vector (BitVec 64) 4

/-- The value of four little-endian limbs: `l[0] + 2^64·l[1] + 2^128·l[2] + 2^192·l[3]`.

Example: `limbsToNat #v[5, 0, 0, 1] = 5 + 2^192`. -/
def limbsToNat (l : Limbs) : Nat :=
  l[0].toNat + 2 ^ 64 * l[1].toNat + 2 ^ 128 * l[2].toNat + 2 ^ 192 * l[3].toNat

/-- The four little-endian limbs of `x mod 2^256`.

Example: `natToLimbs (2^64 + 3) = #v[3, 1, 0, 0]`, and `natToLimbs (2^256) = #v[0, 0, 0, 0]`. -/
def natToLimbs (x : Nat) : Limbs :=
  #v[BitVec.ofNat 64 x, BitVec.ofNat 64 (x / 2 ^ 64), BitVec.ofNat 64 (x / 2 ^ 128),
    BitVec.ofNat 64 (x / 2 ^ 192)]

/-- Four limbs hold less than `2^256`. Example: `limbsToNat #v[-1, -1, -1, -1] = 2^256 - 1`. -/
theorem limbsToNat_lt (l : Limbs) : limbsToNat l < 2 ^ 256 := by
  have h0 := l[0].isLt
  have h1 := l[1].isLt
  have h2 := l[2].isLt
  have h3 := l[3].isLt
  unfold limbsToNat
  omega

/-- Reading back the limbs of `x` gives `x mod 2^256`. Example: `x = 2^256 + 7` gives `7`. -/
theorem limbsToNat_natToLimbs (x : Nat) : limbsToNat (natToLimbs x) = x % 2 ^ 256 := by
  simp only [limbsToNat, natToLimbs, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat]
  omega

/-- The integer relation of the MUL and SQUARE rows (spec section 3).

`MulRel q a b w c` says `a·b = w·q + c`, with the advice quotient `w` and the stored result
`c` both below `2^256`. For SQUARE, `b = a`.
The bounds are all that the rows check about `w` and `c`: each is four 64-bit limbs, and the
final `assert_lte` of `MulqBuilder::inline_sequence` rules out a wrap of the top column, so the
rows' identity `a·b + w·(2^256 - q) = c + 2^256·w` holds over the integers.
The rows do not check `c < q` (see `Canonical`).
Example: `MulRel p 2 ((p+1)/2) 1 1` (Jolt's advice) and `MulRel p 2 ((p+1)/2) 0 (p+1)` both
hold, by spec section 5.3. -/
def MulRel (q a b w c : Nat) : Prop :=
  a * b = w * q + c ∧ w < 2 ^ 256 ∧ c < 2 ^ 256

/-- The integer relation of the DIV rows (spec section 3).

`DivRel q a b w c` says `c·b = w·q + a`, where `a` is the dividend as read from memory
(not reduced), `b` the divisor, and the advice result `c` and quotient `w` are each below
`2^256`. The rows compare the low four columns of `c·b + w·p'` with the dividend read again
from `rs1`, and the high four with `w`, with the same top-column overflow check as `MulRel`.
Example: `DivRel p 1 1 0 1` (Jolt's advice for `1 / 1`) and `DivRel p 1 1 1 (p + 1)` both hold. -/
def DivRel (q a b w c : Nat) : Prop :=
  c * b = w * q + a ∧ w < 2 ^ 256 ∧ c < 2 ^ 256

/-- The canonical output: the stored result is fully reduced, `c < q`.

Jolt's advice produces canonical results for canonical inputs; the rows do not enforce it.
Example: `Canonical p 1` holds and `Canonical p (p + 1)` does not. -/
def Canonical (q c : Nat) : Prop := c < q

instance (q a b w c : Nat) : Decidable (MulRel q a b w c) := by
  unfold MulRel; infer_instance

instance (q a b w c : Nat) : Decidable (DivRel q a b w c) := by
  unfold DivRel; infer_instance

instance (q c : Nat) : Decidable (Canonical q c) := by
  unfold Canonical; infer_instance

/-- The rows' identity in the form they check it is `MulRel`'s equation: for `q ≤ 2^256`,
`a·b + w·(2^256 - q) = c + 2^256·w` exactly when `a·b = w·q + c`.
Example: with `q = p`, `a = 2`, `b = (p+1)/2`, `w = 1`, `c = 1`, both sides are `2^256 + 1`. -/
theorem rows_identity_iff (q a b w c : Nat) (hq : q ≤ 2 ^ 256) :
    a * b + w * pPrime q = c + 2 ^ 256 * w ↔ a * b = w * q + c := by
  unfold pPrime
  have h : w * (2 ^ 256 - q) + w * q = 2 ^ 256 * w := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hq, Nat.mul_comm]
  generalize a * b = x at *
  generalize w * (2 ^ 256 - q) = y at *
  generalize w * q = z at *
  omega

end JoltISA.Inlines.Secp256k1
