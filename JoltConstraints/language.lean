import JoltConstraints.prover_config

open LeanRV64D

/-! Jolt's language, shared by the soundness and completeness statements and
the inclusion into the relaxed tape-answer language. -/

set_option autoImplicit false

/-- An instance is in Jolt's language when, for some private inputs, the model has an
honest trace (`HonestTrace`) with these three properties, and nothing else.

An honest trace gives each advice step outside registered inlines the value Jolt's
tracer computes, and takes the advice words of inline calls from the private input
`inline_advice`, in order. Any words that pass the inline's own assertions are
allowed (decision D2, `docs/inline-precompiles.md` section 5.3). The language is
therefore larger than the set of instances whose trace Jolt's tracer generates at the
pin, which always fills an inline's advice with the words of its `build_advice`
function. For example, a run with a SECP256K1_MULQ call whose advice stores a
noncanonical result that passes the call's assertions can be in the language, although
Jolt's tracer would store the canonical result. For programs without inlines the two
coincide. -/
def JoltInstance.InLanguage (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∃ (privateInputs : JoltPrivateInputs) (trace : HonestTrace joltInstance privateInputs),
    -- The run ends with the claimed outputs (trailing zero bytes dropped) and panic flag.
    -- See : jolt/jolt-sdk/src/host_utils.rs:320
    --       jolt/book/src/usage/guests_hosts/guests.md:144, 223
    trace.matches_outputs joltInstance ∧
    -- Jolt's prover accepts the trace: it ends in a jump, its RAM addresses are at or
    -- above the lowest address, and its padded length is at most the instance's maximum.
    -- See : jolt/crates/jolt-prover/src/config.rs:53-100 (derive_from_dimensions)
    (trace.prover_config joltInstance).isSome ∧
    -- No spoil assert fails: a spoiled run is meant to have no proof.
    -- See : jolt/jolt-platform/src/spoil.rs:1-3
    --       jolt/tracer/src/instruction/virtual_assert_eq.rs:24-31
    trace.SpoilAssertsPass
