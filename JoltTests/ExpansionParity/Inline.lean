import JoltTests.ExpansionParity.Row
import JoltBytecode.Inlines.Generated

/-!
# The generated inline rows, by registration name

One entry per registered inline at the pin: the registration name, the Lean
definition for the `normal` case (`rd != x0`) and the one for the `rd_zero` case.
The table is written by hand from the generated files' declarations, not from the
generator's naming rule, so a renamed or missing definition fails to elaborate here.

Inlines with `VirtualAdvice` rows take `advice : Nat → BitVec 64`; the test passes
`advice k = k`. The advice value is a runtime value and appears in no rendered
field (`VirtualAdvice`'s immediate is its own field, 0 in every generated row).
-/

open LeanRV64D JoltISA.Inlines.Generated

namespace ExpansionParity

def testAdvice : Nat → BitVec 64 := fun k => BitVec.ofNat 64 k

structure InlineEntry where
  name : String
  normal : regidx → regidx → regidx → JoltISA.Program
  rdZero : regidx → regidx → JoltISA.Program

def inlineEntries : List InlineEntry :=
  [ ⟨"SHA256_INLINE", sha256RowsAuto, sha256RowsAutoRdZero⟩,
    ⟨"SHA256_INIT_INLINE", sha256InitRowsAuto, sha256InitRowsAutoRdZero⟩,
    ⟨"KECCAK256_INLINE", keccak256RowsAuto, keccak256RowsAutoRdZero⟩,
    ⟨"KECCAK256_ABSORB_PERMUTE_INLINE", keccak256AbsorbPermuteRowsAuto,
      keccak256AbsorbPermuteRowsAutoRdZero⟩,
    ⟨"BLAKE2_INLINE", blake2RowsAuto, blake2RowsAutoRdZero⟩,
    ⟨"BLAKE3_INLINE", blake3RowsAuto, blake3RowsAutoRdZero⟩,
    ⟨"BLAKE3_KEYED64_INLINE", blake3Keyed64RowsAuto, blake3Keyed64RowsAutoRdZero⟩,
    ⟨"BIGINT256_MUL_INLINE", bigint256MulRowsAuto, bigint256MulRowsAutoRdZero⟩,
    ⟨"SECP256K1_MULQ", (secp256k1MulqRowsAuto · · · testAdvice),
      (secp256k1MulqRowsAutoRdZero · · testAdvice)⟩,
    ⟨"SECP256K1_SQUAREQ", (secp256k1SquareqRowsAuto · · · testAdvice),
      (secp256k1SquareqRowsAutoRdZero · · testAdvice)⟩,
    ⟨"SECP256K1_DIVQ", (secp256k1DivqRowsAuto · · · testAdvice),
      (secp256k1DivqRowsAutoRdZero · · testAdvice)⟩,
    ⟨"SECP256K1_MULR", (secp256k1MulrRowsAuto · · · testAdvice),
      (secp256k1MulrRowsAutoRdZero · · testAdvice)⟩,
    ⟨"SECP256K1_SQUARER", (secp256k1SquarerRowsAuto · · · testAdvice),
      (secp256k1SquarerRowsAutoRdZero · · testAdvice)⟩,
    ⟨"SECP256K1_DIVR", (secp256k1DivrRowsAuto · · · testAdvice),
      (secp256k1DivrRowsAutoRdZero · · testAdvice)⟩,
    ⟨"SECP256K1_GLVR_ADV", (secp256k1GlvrAdvRowsAuto · · · testAdvice),
      (secp256k1GlvrAdvRowsAutoRdZero · · testAdvice)⟩,
    ⟨"GRUMPKIN_DIVQ_ADV", (grumpkinDivqAdvRowsAuto · · · testAdvice),
      (grumpkinDivqAdvRowsAutoRdZero · · testAdvice)⟩,
    ⟨"GRUMPKIN_DIVR_ADV", (grumpkinDivrAdvRowsAuto · · · testAdvice),
      (grumpkinDivrAdvRowsAutoRdZero · · testAdvice)⟩,
    ⟨"GRUMPKIN_GLVR_ADV", (grumpkinGlvrAdvRowsAuto · · · testAdvice),
      (grumpkinGlvrAdvRowsAutoRdZero · · testAdvice)⟩,
    ⟨"P256_MULQ", (p256MulqRowsAuto · · · testAdvice), (p256MulqRowsAutoRdZero · · testAdvice)⟩,
    ⟨"P256_SQUAREQ", (p256SquareqRowsAuto · · · testAdvice),
      (p256SquareqRowsAutoRdZero · · testAdvice)⟩,
    ⟨"P256_DIVQ", (p256DivqRowsAuto · · · testAdvice), (p256DivqRowsAutoRdZero · · testAdvice)⟩,
    ⟨"P256_MULR", (p256MulrRowsAuto · · · testAdvice), (p256MulrRowsAutoRdZero · · testAdvice)⟩,
    ⟨"P256_SQUARER", (p256SquarerRowsAuto · · · testAdvice),
      (p256SquarerRowsAutoRdZero · · testAdvice)⟩,
    ⟨"P256_DIVR", (p256DivrRowsAuto · · · testAdvice), (p256DivrRowsAutoRdZero · · testAdvice)⟩,
    ⟨"P256_FAKE_GLV_ADV", (p256FakeGlvAdvRowsAuto · · · testAdvice),
      (p256FakeGlvAdvRowsAutoRdZero · · testAdvice)⟩,
    ⟨"NTT64_I32_FORWARD", ntt64I32ForwardRowsAuto, ntt64I32ForwardRowsAutoRdZero⟩,
    ⟨"NTT64_I32_POINTWISE_DOT6", ntt64I32PointwiseDot6RowsAuto,
      ntt64I32PointwiseDot6RowsAutoRdZero⟩ ]

def findInline (name : String) : Option InlineEntry :=
  inlineEntries.find? (·.name == name)

def regOf (n : Nat) : regidx := regidx.Regidx (BitVec.ofNat 5 n)

/-- The generated rows of an inline at source operands `rs1`, `rs2` and
`rd` (`rs3`), using the `rd_zero` definition when `rd = x0`. -/
def InlineEntry.rows (e : InlineEntry) (rs1 rs2 rd : Nat) : List JoltISA.Instr :=
  if rd == 0 then programRows (e.rdZero (regOf rs1) (regOf rs2))
  else programRows (e.normal (regOf rs1) (regOf rs2) (regOf rd))

end ExpansionParity
