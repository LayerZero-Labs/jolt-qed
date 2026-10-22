import JoltConstraints.prover_config

/-! Jolt's language, shared by the soundness and completeness statements and
the inclusion into the relaxed tape-answer language. -/

set_option autoImplicit false

/-- An instance is in Jolt's language when, for some private inputs, Jolt's tracer
records an honest trace that Jolt proves: one with these three properties, and
nothing else. -/
def JoltInstance.InLanguage (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∃ (privateInputs : JoltPrivateInputs) (trace : HonestTrace joltInstance privateInputs),
    -- The run ends with the claimed outputs (trailing zero bytes dropped) and panic flag.
    -- See : jolt/jolt-sdk/src/host_utils.rs:320
    --       jolt/book/src/usage/guests_hosts/guests.md:144, 223
    trace.matches_outputs joltInstance ∧
    -- Jolt's prover accepts the trace: it ends in a jump, its RAM addresses are at or
    -- above the lowest address, and its padded length is at most the instance's maximum.
    -- See : jolt/crates/jolt-prover/src/config.rs:63-110 (derive_from_dimensions)
    (trace.prover_config joltInstance).isSome ∧
    -- No spoil assert fails: a spoiled run is meant to have no proof.
    -- See : jolt/jolt-platform/src/spoil.rs:1-3
    --       jolt/tracer/src/instruction/virtual_assert_eq.rs:24-31
    trace.SpoilAssertsPass
