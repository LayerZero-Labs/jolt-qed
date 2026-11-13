/-
What the soundness theorem assumes, grouped by what each assumption is about:
the field, the instance, and temporary workarounds for known issues.
Nothing is assumed about the witness.
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.ZMod.Basic
import JoltConstraints.honest_trace
import JoltConstraints.Soundness.Layer3.Layout
import JoltConstraints.Soundness.Layer5.MemoryAccessRestriction
import JoltConstraints.Soundness.Layer5.HostCallSuccess
import JoltConstraints.Soundness.Layer5.TapeTrace
import JoltConstraints.Soundness.Layer5.TerminationRestriction
import JoltConstraints.Soundness.Layer5.PanicRestriction

open LeanRV64D

set_option autoImplicit false

-- The fields the theorem covers. Jolt's Rust code has a `JoltField` trait for the
-- fields it supports; this models only the one property our proofs use: the
-- characteristic is above 2^128 - 2^64.
-- Most proofs need only 2^127 < ringChar F (`two_pow_127_lt_char`). The full bound
-- is used where an identity-RAF lookup address (any value below 2^128) is
-- recovered from its field encoding (`identityAddress_lt_char`):
-- * BN254, characteristic about 2^254, exceeds every address. Jolt's default build
--   uses it, and the canonical-address check (63) is off.
-- * Akita's field `p = 2^128 - 1780711455` (`Prime128Offset6A23801F`, Jolt's
--   production field since a16z/jolt#2403) is below 2^128, so an address
--   k in [p, 2^128) would alias k - p. Jolt's `akita` build turns on check (63),
--   which rejects every address at or above 2^128 - 2^64; the remaining addresses
--   are below p. The model turns (63) on exactly when the characteristic is below
--   2^128 (`CanonicalInstructionAddress`).
-- NOTE: the field is not fully modeled yet. Everything else the Rust trait provides
-- (field size, encoding, arithmetic implementation) is outside this model.
def JoltField (F : Type) [Field F] : Prop :=
  2 ^ 128 - 2 ^ 64 < ringChar F

/-- The modulus of Jolt's production field with Akita, `Prime128Offset6A23801F`:
`2^128 - 1780711455`, where `1780711455 = 0x6A23801F`.
Jolt: `crates/jolt-algebra/src/solinas/mod.rs` (`Prime128Offset6A23801F`) at
a16z/jolt `25d87ba6` (#2403). -/
def akitaModulus : Nat := 2 ^ 128 - 1780711455

/-- BN254's scalar-field modulus, the field of Jolt's default (Dory) build. -/
def bn254ScalarModulus : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- Akita's modulus is above `2^128 - 2^64`: it falls short of `2^128` by
`1780711455`, which is less than `2^64`. -/
theorem akitaModulus_above : 2 ^ 128 - 2 ^ 64 < akitaModulus := by
  norm_num [akitaModulus]

/-- BN254's scalar modulus is above `2^128 - 2^64`. -/
theorem bn254ScalarModulus_above : 2 ^ 128 - 2 ^ 64 < bn254ScalarModulus := by
  norm_num [bn254ScalarModulus]

/-- The previous field premise, `2^128 < ringChar F`, implies `JoltField`. -/
theorem JoltField.of_two_pow_128_lt {F : Type} [Field F] (above : 2 ^ 128 < ringChar F) :
    JoltField F :=
  lt_trans (by norm_num) above

/-- Every field of Akita's characteristic is a `JoltField`. -/
theorem JoltField.of_ringChar_eq_akitaModulus {F : Type} [Field F]
    (characteristic : ringChar F = akitaModulus) : JoltField F := by
  unfold JoltField
  rw [characteristic]
  exact akitaModulus_above

/-- The integers modulo Akita's prime form a `JoltField`. Primality is the
hypothesis that makes `ZMod akitaModulus` a field; Jolt checks it with a
Pocklington certificate in HOL Light (a16z/jolt#2403). -/
theorem JoltField.zmod_akitaModulus [Fact akitaModulus.Prime] :
    JoltField (ZMod akitaModulus) :=
  JoltField.of_ringChar_eq_akitaModulus (ZMod.ringChar_zmod_n akitaModulus)

/-- The integers modulo BN254's scalar prime form a `JoltField`. -/
theorem JoltField.zmod_bn254ScalarModulus [Fact bn254ScalarModulus.Prime] :
    JoltField (ZMod bn254ScalarModulus) := by
  unfold JoltField
  rw [ZMod.ringChar_zmod_n]
  exact bn254ScalarModulus_above

-- What the soundness theorem assumes about the instance. Each field's comment says
-- whether a16z has confirmed it or it is still awaiting confirmation. Workarounds
-- for known issues are not here; they are in `JoltInstance.TemporaryRestrictions`.
structure JoltInstance.SoundnessAssumptions
    (joltInstance : JoltInstance SourceInstruction) : Prop where
  -- The whole maximum padded RAM region, including all eight bytes of every word,
  -- lies below 2^64. Approved by Ari on 2026-10-10.
  -- NOTE: to confirm with a16z.
  ramRegionFits : joltInstance.RamRegionFits

/-- Temporary restriction (FIXME) of the soundness theorem for committed advice words.
The untrusted-advice block Jolt's verifier checks holds no more bytes than the
configured maximum the tracer enforces. Equivalently, that maximum is a multiple
of 8: the layout rounds it up to a multiple of 8, and the block holds the rounded
size. Otherwise Jolt's verifier lets the prover commit to the whole rounded block,
and the tracer accepts only the configured number of bytes. For example, with a
maximum of 12 the verifier's block has 2 words, and the prover may set the top 4
bytes of the second word, which no tracer run can hold. Jolt's verifier does not
check it. It is a separate premise, not a field of `TemporaryRestrictions`, because
soundness for advice given as bytes (`JoltInstance.soundness_onBytes`) does not need
it. Remove when Jolt's tracer or `MemoryLayout::new` checks the rounded size. -/
def JoltInstance.UntrustedAdviceBlockFits {Source : Type} (joltInstance : JoltInstance Source) :
    Prop :=
  ∀ layout : MemoryLayout, joltInstance.memory_layout = some layout →
    layout.max_untrusted_advice_size.toNat ≤
      joltInstance.memory_config.max_untrusted_advice_size.toNat

-- Temporary program restrictions. Each excludes programs that expose reported
-- or suspected Jolt bugs. None is a check Jolt's verifier makes. Remove each
-- once Jolt and the model are fixed and the unrestricted proof is established.
structure JoltInstance.TemporaryRestrictions
    (joltInstance : JoltInstance SourceInstruction) : Prop where
  -- FIXME: every load and store the program attempts passes Jolt's tracer address
  -- checks (a16z/jolt#2044, plus four candidates in methods/soundness.md: stores
  -- at zero, the I/O gap, stack-canary stores, and accesses at or above heap_end).
  -- Narrow or remove it as each case is resolved.
  tracerAddressChecks : joltInstance.TracerAddressChecks
  -- FIXME: once the program has stored to the termination word, its next jump is
  -- the stall (a JAL with offset 0), and it never loads the termination word again
  -- (B6, stopping early; related to a16z/jolt#1950 and #1951 item 2).
  -- The SDK's exit is written this way. To raise with a16z with the other FIXMEs.
  terminationThenStall : joltInstance.TerminationThenStall
  -- FIXME: every store to the panic word stores 1, and no load reads the panic
  -- word after such a store. Excludes a store of 0 being proved as "no panic"
  -- (LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/completeness-and-soundness/index.md). A Jolt bug: it must
  -- be fixed in Jolt and cannot remain a restriction.
  panicStoresOne : joltInstance.PanicStoresOne
  -- FIXME: the claim says "no panic". Excludes a "panicked" claim proved from an
  -- execution cut short at a jump (LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/proof-stops-at-any-jump/index.md).
  -- A Jolt bug: it must be fixed in Jolt and cannot remain a restriction.
  claimsNoPanic : joltInstance.ClaimsNoPanic
