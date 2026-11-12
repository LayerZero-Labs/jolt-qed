import JoltBytecode.Inlines.Secp256k1.Spec
import Mathlib.Data.ZMod.Basic

/-!
# Jolt's advice functions for the seven secp256k1 inlines

Computable transcriptions of the Rust code that computes the advice words of the secp256k1
inlines, at a16z/jolt `a6b6dc717`:

- `jolt-inlines/sdk/src/host.rs`: `mulq_quotient_advice`, `mulq_division_advice`,
  `nbiguint_to_field_limbs`, and the `into_runtime_advice` methods of `QuotientAdvice`,
  `ModularDivisionAdvice` and `GlvDecompositionAdvice`;
- `jolt-inlines/secp256k1/src/sequence_builder.rs`: `MulqBuilder::quotient_advice`,
  `MulqBuilder::division_advice` (the `field_inv_mul` closure) and `GlvrAdvBuilder::advice`;
- `jolt-inlines/secp256k1/src/glv.rs`: `r`, `a1`, `b1`, `a2`, `rounded_div`,
  `decompose_scalar`, `to_sign_abs` and `decompose_scalar_to_u64s`.

Where the Rust code panics, the transcription returns `none`.
`joltAdvice` lists the words in the order the inline's `VirtualAdvice` rows consume them.
The test executable `secp256k1-kat` (`JoltTests/Secp256k1Kat/Main.lean`) checks every function
here against the Rust code on edge-case and random inputs.
-/

namespace JoltISA.Inlines.Secp256k1

/-! ## Field inlines -/

/-- `nbiguint_to_field_limbs` (`jolt-inlines/sdk/src/host.rs`): the four limbs of `x`, or
`none` where Rust's `assert!(limbs.len() <= 4)` panics, that is when `x ≥ 2^256`.
Example: `fieldLimbs? 5 = some #v[5, 0, 0, 0]` and `fieldLimbs? (2^256) = none`. -/
def fieldLimbs? (x : Nat) : Option Limbs :=
  if x < 2 ^ 256 then some (natToLimbs x) else none

/-- `mulq_quotient_advice` (`jolt-inlines/sdk/src/host.rs`) for the modulus `q`: the floor
quotient `⌊a·b / q⌋` of the 256-bit operands, as four limbs.

For SQUARE, Jolt reads `b` from the same address as `a` (`mulq_operands`), so the caller passes
`b = a`. Rust panics in `nbiguint_to_field_limbs` when the quotient needs a fifth limb, which
happens only for unreduced operands, for example `a = b = 2^256 - 1` with `q = p`; the
transcription returns `none` there.
Example: `mulqQuotientAdvice p (natToLimbs 2) (natToLimbs ((p + 1) / 2)) = some (natToLimbs 1)`. -/
def mulqQuotientAdvice (q : Nat) (a b : Limbs) : Option Limbs :=
  fieldLimbs? (limbsToNat a * limbsToNat b / q)

/-- The `field_inv_mul` closure of `MulqBuilder::division_advice` (`sequence_builder.rs`):
`(Fq::new(b).inverse() * Fq::new(a)).into_bigint()`, that is `a·b⁻¹ mod q` with both operands
first reduced modulo `q`, or `none` where `inverse()` returns `None` and Rust's `expect` panics
(`b ≡ 0 mod q`). Its result is below `q`.
Example: `fieldInvMul p (natToLimbs 2) (natToLimbs 1) = some ((p + 1) / 2)`. -/
def fieldInvMul (q : Nat) (b a : Limbs) : Option Nat :=
  if limbsToNat b % q = 0 then none
  else some (((limbsToNat a : ZMod q) * (limbsToNat b : ZMod q)⁻¹).val)

/-- `mulq_division_advice` (`jolt-inlines/sdk/src/host.rs`) for the modulus `q`: the pair
`(result, quotient)` with `result = a / b mod q` and `quotient = ⌊b·result / q⌋`, where `b` in
the quotient is the divisor as read from memory, not reduced. `none` when `b ≡ 0 mod q`
(Rust panics). Neither `nbiguint_to_field_limbs` call can panic, since `result < q < 2^256`
and `b < 2^256`.
Example: `mulqDivisionAdvice p (natToLimbs 1) (natToLimbs 2) = some (natToLimbs ((p+1)/2), natToLimbs 1)`. -/
def mulqDivisionAdvice (q : Nat) (a b : Limbs) : Option (Limbs × Limbs) := do
  let result ← fieldInvMul q b a
  let quotient := limbsToNat b * result / q
  let r ← fieldLimbs? result
  let w ← fieldLimbs? quotient
  pure (r, w)

/-- `QuotientAdvice::into_runtime_advice` (`jolt-inlines/sdk/src/host.rs`): the quotient limbs
in order. The MUL and SQUARE rows consume them as `w[0], w[1], w[2], w[3]`: one `VirtualAdvice`
per iteration of the load loop of `MulqBuilder::inline_sequence`.
Example: `quotientWords #v[1, 2, 3, 4] = [1, 2, 3, 4]`. -/
def quotientWords (w : Limbs) : List (BitVec 64) := w.toList

/-- `ModularDivisionAdvice::into_runtime_advice` (`jolt-inlines/sdk/src/host.rs`): result and
quotient limbs interleaved, `c[0], w[0], c[1], w[1], c[2], w[2], c[3], w[3]`. The DIV rows
consume them in this order: in each iteration `i` of the load loop of
`MulqBuilder::inline_sequence`, a `VirtualAdvice` into `a[i]` (the result) comes before the one
into `w[i]`.
Example: `divisionWords #v[1, 2, 3, 4] #v[5, 6, 7, 8] = [1, 5, 2, 6, 3, 7, 4, 8]`. -/
def divisionWords (c w : Limbs) : List (BitVec 64) :=
  [c[0], w[0], c[1], w[1], c[2], w[2], c[3], w[3]]

/-! ## GLV decomposition -/

/-- The little-endian byte string of `glv.rs`, read as a natural number.
Example: `natOfBytesLE [1, 2] = 0x0201`. -/
def natOfBytesLE (bytes : List Nat) : Nat :=
  bytes.foldr (fun byte acc => byte + 256 * acc) 0

/-- `glv.rs` `a1`: `0x3086d221a7d46bcde86c90e49284eb15`, the first coordinate of the first
lattice basis vector. It is also `b2` of the usual secp256k1 basis.
Example: `glvA1 < 2^126`. -/
def glvA1 : Nat := 0x3086d221a7d46bcde86c90e49284eb15

/-- `glv.rs` `b1`: `0xe4437ed6010e88286f547fa90abfe4c3`, the magnitude of `b1 = -0xe443…`
in the usual secp256k1 basis; `decompose_scalar` uses it with a positive sign.
Example: `glvB1 < 2^128`. -/
def glvB1 : Nat := 0xe4437ed6010e88286f547fa90abfe4c3

/-- `glv.rs` `a2`: `0x114ca50f7a8e2f3f657c1108d9d44cfd8`, a 129-bit value.
Example: `2^128 < glvA2`. -/
def glvA2 : Nat := 0x114ca50f7a8e2f3f657c1108d9d44cfd8

/-- The endomorphism eigenvalue `λ` of the SDK's GLV check (`sdk.rs`,
`decompose_scalar_impl`, the `lambda` limbs).
Example: `glvLambda < n`. -/
def glvLambda : Nat := 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72

/-- The constant `r()` of `glv.rs` is `n`, written as bytes. -/
theorem glv_r_bytes : natOfBytesLE [65, 65, 54, 208, 140, 94, 210, 191, 59, 160, 72, 175, 230,
    220, 174, 186, 254, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255] = n := by
  decide

/-- The constant `a1()` of `glv.rs`, written as bytes. -/
theorem glv_a1_bytes : natOfBytesLE [21, 235, 132, 146, 228, 144, 108, 232, 205, 107, 212, 167,
    33, 210, 134, 48] = glvA1 := by
  decide

/-- The constant `b1()` of `glv.rs`, written as bytes. -/
theorem glv_b1_bytes : natOfBytesLE [195, 228, 191, 10, 169, 127, 84, 111, 40, 136, 14, 1, 214,
    126, 67, 228] = glvB1 := by
  decide

/-- The constant `a2()` of `glv.rs`, written as bytes. -/
theorem glv_a2_bytes : natOfBytesLE [216, 207, 68, 157, 141, 16, 193, 87, 246, 243, 226, 168,
    247, 80, 202, 20, 1] = glvA2 := by
  decide

/-- The lattice facts behind the GLV split. The two basis vectors `(a1, -b1)` and `(a2, a1)`
satisfy `a1 - λ·b1 ≡ 0` and `a2 + λ·a1 ≡ 0 (mod n)`, and their determinant `a1² + b1·a2` is
`n`. These are the facts a proof of `glvDecompose_small` and `glvDecompose_recombines` (spec
section 5.4, phase I2) needs: writing `β1 = k·a1/n + e1` and `β2 = k·b1/n + e2` with
`|e1|, |e2| ≤ 1/2` gives `k1 = -(e1·a1 + e2·a2)` and `k2 = e1·b1 - e2·a1`, so
`|k1| ≤ (a1 + a2)/2` and `|k2| ≤ (b1 + a1)/2`, both below `2^128`. That argument is not
formalized here.
Example: `(glvA1 + glvA2) / 2 = 0xa2a8918ca85bafe22016d0b917e4dd76`. -/
theorem glv_lattice :
    (glvA1 + glvLambda * (n - glvB1)) % n = 0 ∧ (glvA2 + glvLambda * glvA1) % n = 0 ∧
      glvA1 ^ 2 + glvB1 * glvA2 = n ∧
      (glvA1 + glvA2) / 2 < 2 ^ 128 ∧ (glvB1 + glvA1) / 2 < 2 ^ 128 := by
  decide

/-- `rounded_div` of `glv.rs`: `k·coeff` divided by `r` with Rust `BigInt::div_rem`, which
truncates toward zero, plus one when `2·rem > r`.
For `k, coeff ≥ 0` and `r > 0` this rounds `k·coeff / r` to the nearest integer, halves down.
Example: `roundedDiv 3 1 2 = 1` (`rem = 1`, `2 > 2` fails) and `roundedDiv 5 1 3 = 2`;
`roundedDiv (-5) 1 3 = -1`, since truncation gives `-1` and `rem = -2`. -/
def roundedDiv (k coeff r : Int) : Int :=
  let div := (k * coeff).tdiv r
  let rem := (k * coeff).tmod r
  if rem + rem > r then div + 1 else div

/-- The split `(k1, k2)` that `decompose_scalar` (`glv.rs`) computes before `to_sign_abs`:
`β1 = rounded_div(k, a1, n)`, `β2 = rounded_div(k, b1, n)`, `k1 = k - β1·a1 - β2·a2`,
`k2 = β1·b1 - β2·a1`. Defined for every integer `k`, as Rust's `BigInt` code is.
Example: `glvSplit 1 = (1, 0)`, since both roundings give `0`. -/
def glvSplit (k : Int) : Int × Int :=
  let r : Int := n
  let beta1 := roundedDiv k glvA1 r
  let beta2 := roundedDiv k glvB1 r
  (k - beta1 * glvA1 - beta2 * glvA2, beta1 * glvB1 - beta2 * glvA1)

/-- `to_sign_abs` (`glv.rs`): `(x < 0, |x| mod 2^128)`. Rust takes the sign of the `BigInt`
(`Sign::Minus` only for negative values) and the low 16 bytes of its little-endian magnitude,
which truncates magnitudes of `2^128` or more.
Example: `toSignAbs (-3) = (true, 3)` and `toSignAbs (2^128 + 5) = (false, 5)`. -/
def toSignAbs (x : Int) : Bool × Nat := (decide (x < 0), x.natAbs % 2 ^ 128)

/-- `decompose_scalar` (`glv.rs`): `[(sign1, |k1|), (sign2, |k2|)]` with the sign `true` for
negative and each magnitude truncated to 128 bits by `to_sign_abs`.
Example: `decomposeScalar 1 = ((false, 1), (false, 0))`. -/
def decomposeScalar (k : Int) : (Bool × Nat) × (Bool × Nat) :=
  let s := glvSplit k
  (toSignAbs s.1, toSignAbs s.2)

/-- `decompose_scalar_to_u64s` (`glv.rs`) and `GlvDecompositionAdvice::into_runtime_advice`
(`jolt-inlines/sdk/src/host.rs`), which give the same six words:
`[sign1, k1_lo, k1_hi, sign2, k2_lo, k2_hi]`, each sign word `0` or `1`.
Example: `decomposeScalarToU64s 1 = #v[0, 1, 0, 0, 0, 0]`. -/
def decomposeScalarToU64s (k : Int) : Vector (BitVec 64) 6 :=
  let d := decomposeScalar k
  #v[BitVec.ofNat 64 d.1.1.toNat, BitVec.ofNat 64 d.1.2, BitVec.ofNat 64 (d.1.2 / 2 ^ 64),
    BitVec.ofNat 64 d.2.1.toNat, BitVec.ofNat 64 d.2.2, BitVec.ofNat 64 (d.2.2 / 2 ^ 64)]

/-- `GlvrAdvBuilder::advice` (`sequence_builder.rs`) as runtime words: it reads `k` through
`rs1`, reduces it with `Fr::new(BigInt(kr)).into_bigint()` (the value modulo `n`; the KAT checks
this for unreduced limbs), and splits it. The `GLVR_ADV` rows consume the six words in order:
`emit_advice_stores` emits one `VirtualAdvice` and one `SD` per word.
Example: `glvrAdvice (natToLimbs 1) = #v[0, 1, 0, 0, 0, 0]`. -/
def glvrAdvice (k : Limbs) : Vector (BitVec 64) 6 :=
  decomposeScalarToU64s (limbsToNat k % n : Nat)

/-! ## Per-inline advice -/

/-- The seven secp256k1 inlines (`jolt-inlines/secp256k1/src/lib.rs`), all with opcode `0x0B`
and `funct7 = 0x05`; the comment on each constructor gives its `funct3`. -/
inductive Secp256k1Inline where
  /-- `SECP256K1_MULQ`, `funct3 = 0`. -/
  | mulq
  /-- `SECP256K1_SQUAREQ`, `funct3 = 1`. -/
  | squareq
  /-- `SECP256K1_DIVQ`, `funct3 = 2`. -/
  | divq
  /-- `SECP256K1_MULR`, `funct3 = 4`. -/
  | mulr
  /-- `SECP256K1_SQUARER`, `funct3 = 5`. -/
  | squarer
  /-- `SECP256K1_DIVR`, `funct3 = 6`. -/
  | divr
  /-- `SECP256K1_GLVR_ADV`, `funct3 = 7`. -/
  | glvrAdv
  deriving DecidableEq, Repr

/-- The modulus an inline reduces by: `p` for the `Q` inlines, `n` for the `R` inlines and
`GLVR_ADV`. Example: `Secp256k1Inline.mulr.modulus = n`. -/
def Secp256k1Inline.modulus : Secp256k1Inline → Nat
  | .mulq | .squareq | .divq => p
  | .mulr | .squarer | .divr | .glvrAdv => n

/-- Jolt's advice words for one call (`InlineOp::build_runtime_advice` of the inline), in the
order its `VirtualAdvice` rows consume them. `a` is the 256-bit value at `rs1` (for `GLVR_ADV`,
the scalar `k`) and `b` the value at `rs2`; SQUARE and `GLVR_ADV` ignore `b`. `none` where the
Rust code panics: a zero divisor modulo `q` for DIV, a quotient of `2^256` or more for MUL and
SQUARE.
Example: `joltAdvice .mulq (natToLimbs 2) (natToLimbs ((p+1)/2)) = some [1, 0, 0, 0]`. -/
def joltAdvice (op : Secp256k1Inline) (a b : Limbs) : Option (List (BitVec 64)) :=
  match op with
  | .mulq | .mulr => quotientWords <$> mulqQuotientAdvice op.modulus a b
  | .squareq | .squarer => quotientWords <$> mulqQuotientAdvice op.modulus a a
  | .divq | .divr => (fun cw => divisionWords cw.1 cw.2) <$> mulqDivisionAdvice op.modulus a b
  | .glvrAdv => some (glvrAdvice a).toList

end JoltISA.Inlines.Secp256k1
