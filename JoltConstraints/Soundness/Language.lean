import JoltConstraints.honest_trace

/-! The fixed-tape execution language, shared by the main soundness statement
and the inclusion into the relaxed tape-answer language. -/

set_option autoImplicit false

/-- For some private inputs, Jolt's tracer reaches the PC stall with the outputs
(trailing zero bytes dropped) and panic flag the instance claims.
See jolt/jolt-sdk/src/host_utils.rs:320 and
jolt/book/src/usage/guests_hosts/guests.md:144, 223. -/
def JoltInstance.InLanguage (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∃ (privateInputs : JoltPrivateInputs) (trace : HonestTrace joltInstance privateInputs),
    trace.matches_outputs
