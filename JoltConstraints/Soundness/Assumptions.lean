/-
What the soundness theorem assumes, grouped by what each assumption is about:
the field, the instance, and temporary workarounds for known issues.
Nothing is assumed about the witness.
-/
import Mathlib.Algebra.CharP.Defs
import JoltConstraints.honest_trace
import JoltConstraints.Soundness.Layer3.Layout
import JoltConstraints.Soundness.Layer5.MemoryAccessRestriction
import JoltConstraints.Soundness.Layer5.HostCallRestriction
import JoltConstraints.Soundness.Layer5.TapeTrace
import JoltConstraints.Soundness.Layer5.TerminationRestriction
import JoltConstraints.Soundness.Layer5.PanicRestriction

open LeanRV64D

set_option autoImplicit false

-- The fields the base theorem covers. Jolt's Rust code has a `JoltField` trait for
-- the fields it supports; this models only the one property our proofs use: the
-- characteristic is above 2^128, so every 128-bit lookup address has a distinct
-- field encoding. BN254 satisfies this. Akita's prime, about 2^128 - 2^32, does not;
-- Akita is modeled separately.
-- NOTE: the field is not fully modeled yet. Everything else the Rust trait provides
-- (field size, encoding, arithmetic implementation) is outside this model.
def JoltField (F : Type) [Field F] : Prop :=
  2 ^ 128 < ringChar F

-- What the soundness theorem assumes about the instance. Each field's comment says
-- whether a16z has confirmed it or it is still awaiting confirmation. Workarounds
-- for known issues are not here; they are in `JoltInstance.TemporaryRestrictions`.
structure JoltInstance.SoundnessAssumptions
    (joltInstance : JoltInstance SourceInstruction) : Prop where
  -- The whole maximum padded RAM region, including all eight bytes of every word,
  -- lies below 2^64. Approved by Ari on 2026-10-10.
  -- NOTE: to confirm with a16z.
  ramRegionFits : joltInstance.RamRegionFits

/-- A temporary restriction on completed relaxed executions.
An `UntrustedAnswerTrace` records actual executed rows and independent tape
answers; `rows.size` counts those real rows. For a verifier-admissible maximum,
the excluded count `2 ^ Nat.log2 max_padded_trace_length` is the largest
power-of-two witness domain within that maximum.
For a maximum of 1024, a 1024-row trace is excluded, while a 256-row trace is
allowed: Jolt's prover pads the latter to 512.
Jolt's verifier can accept a full-length witness, but its prover adds a padding
row and would exceed the maximum. See
`LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/prover-verifier-trace-length/index.md` and
`jolt/crates/jolt-prover/src/config.rs:63-70,116-119` at `5def437f`. -/
def JoltInstance.NoMaxLengthTrace
    (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∀ (privateInputs : JoltPrivateInputs)
    (trace : JoltConstraints.Soundness.UntrustedAnswerTrace joltInstance privateInputs),
    trace.rows.size ≠ 2 ^ Nat.log2 joltInstance.max_padded_trace_length.toNat

-- The untrusted-advice block Jolt's verifier checks holds no more bytes than the
-- configured maximum the tracer enforces. Equivalently, that maximum is a multiple
-- of 8: the layout rounds it up to a multiple of 8, and the block holds the rounded
-- size.
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
  -- FIXME: every attempted VirtualHostIO call succeeds in the modeled
  -- execution. This excludes invalid cycle-marker or print events, and
  -- pointer overflow when the model enables its overflow check. Matching
  -- checked Rust overflow behavior remains a separate obligation.
  -- The local constraints do not encode host-call success.
  -- Candidate, not reproduced; to raise with a16z with the other FIXMEs.
  hostCallsSucceed : joltInstance.HostCallsSucceed
  -- FIXME: exclude a relaxed execution whose real rows fill the largest
  -- verifier-admissible power-of-two domain. Jolt's prover requires one more
  -- padding row, but its verifier can accept that full-length witness.
  -- Remove when Jolt resolves the mismatch described in
  -- LayerZero-Research/LZ-Notes:content/projects/jolt-qed/blog/prover-verifier-trace-length/index.md.
  noMaxLengthTrace : joltInstance.NoMaxLengthTrace
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
  -- FIXME: the configured maximum untrusted-advice size is a multiple of 8.
  -- Otherwise the layout rounds it up, Jolt's verifier lets the prover commit to
  -- the whole rounded block, and the tracer accepts only the configured number of
  -- bytes. For example, with a maximum of 12 the verifier's block has 2 words, and
  -- the prover may set the top 4 bytes of the second word, which no tracer run can
  -- hold. Remove when Jolt's tracer or `MemoryLayout::new` checks the rounded size.
  untrustedAdviceBlockFits : joltInstance.UntrustedAdviceBlockFits
