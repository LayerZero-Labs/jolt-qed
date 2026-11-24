import JoltConstraints.translation.witness_helpers.ram_state
import JoltConstraints.translation.verifier_sizes

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Data used by the constraint equations, bound to one instance and its private
inputs, with the verifier's public-input and domain-size checks. This contains
no execution rows or honesty certificate.

`io` is the verifier's public I/O. Trusted advice is part of the instance; Jolt's
verifier holds a commitment to it, and we model its contents directly.
`initialRam` includes this advice and the prover's untrusted advice, so it is
not claimed to be public. Its encoding comes from `initial_state`; the execution
tape does not affect this encoding. See `AllConstraints.advice_tape_irrelevant`. -/
structure ConstraintContext (joltInstance : JoltInstance SourceInstruction)
    (privateInputs : JoltPrivateInputs) (params : WitnessParams) where
  bytecode : Array JoltInstructionRow
  initialRam : Nat → BitVec 64
  io : JoltPublicIo
  entry : Fin (2 ^ params.logBytecodeK)
  expands : expand_program joltInstance.program = some bytecode
  initialized : ∃ state, joltInstance.initial_state privateInputs = some state ∧
    initialRam = TraceWitness.initialRamWordFromState state
  publicIo : joltInstance.public_io = some io
  validInputs : joltInstance.validate_inputs = true
  traceLengthBound : params.traceLength ≤ joltInstance.max_padded_trace_length.toNat
  -- Jolt's base verifier rejects a 128-cycle proof even if the instance maximum
  -- permits it; Akita's 4096-cycle floor is outside this model.
  -- See jolt/crates/jolt-verifier/src/verifier.rs:976-991 and
  -- jolt/crates/jolt-verifier/src/config.rs:109-120 at 5def437f.
  traceLengthFloor : 256 ≤ params.traceLength
  bytecodeDomain : params.BytecodeDomainFor bytecode.size
  ramSizeBounds : joltInstance.ram_size_in_bounds params.ramSize = true
  oneHotFitsSetup : joltInstance.one_hot_fits_setup params.logT params.chunkBits = true
  entryIsRust : ∃ slots, preprocess bytecode = some slots ∧
    get_first_pc slots joltInstance.program.entry_address = some entry.val

end JoltConstraints
