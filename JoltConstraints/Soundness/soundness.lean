/-
The soundness statement: a witness that satisfies every constraint shows the instance
is in Jolt's language. The proof is left as `sorry`; it is not expected to hold yet
(methods/review_completeness_and_soundness.md, B6).
-/
import JoltConstraints.Constraints.All
import JoltConstraints.honest_trace

set_option autoImplicit false

-- The instance is in Jolt's language: for some private inputs, Rust's run of the
-- program stops at the PC stall with the outputs (trailing zero bytes dropped) and the
-- panic flag the instance claims.
-- See : jolt/jolt-sdk/src/host_utils.rs:320 (the claim is the tracer's final device)
--       jolt/book/src/usage/guests_hosts/guests.md:144, 223
def JoltInstance.InLanguage (joltInstance : JoltInstance SourceInstruction) : Prop :=
  ∃ (privateInputs : JoltPrivateInputs) (trace : HonestTrace joltInstance privateInputs),
    trace.matches_outputs

-- Soundness: if some private inputs and witness satisfy every constraint, the instance
-- is in Jolt's language. The private inputs of the run need not be the ones given.
-- FIXME: expected to fail today for programs that stop or panic in ways SDK guests
-- never do (B6, "Known not sound for this L").
theorem JoltInstance.soundness {F : Type} [Field F]
    -- the field's characteristic is above 2^127 (Akita's prime, about 2^128 - 2^32,
    -- and BN254's are)
    (largeField : 2 ^ 127 < ringChar F)
    (joltInstance : JoltInstance SourceInstruction)
    -- assumed: a legal ELF's PC does not wrap (a16z confirmed)
    (noWrap : joltInstance.program.NextPCNoWrap)
    -- assumed: the program does not change its own code (a16z, a16z/jolt#1952)
    (codeUnchanged : joltInstance.CodeUnchanged)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (satisfied : JoltConstraints.AllConstraints joltInstance privateInputs witness) :
    joltInstance.InLanguage := by
  sorry
