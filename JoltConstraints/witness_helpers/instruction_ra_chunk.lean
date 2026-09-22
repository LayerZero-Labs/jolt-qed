import JoltConstraints.witness_helpers.address_chunk
import JoltConstraints.witness_helpers.lookup_index
import JoltConstraints.witness

set_option autoImplicit false

namespace HonestWitness

-- Rust: [InstructionRaChunk](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/one_hot.rs:109).
-- Committed chunks of the full 128-bit lookup address. Every cycle selects one
-- entry per chunk; padding selects entry 0 rather than an entirely zero column.
noncomputable def InstructionRaChunk {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) :
    Fin p.instructionChunks → Fin (2 ^ p.chunkBits) → Fin p.traceLength → F :=
  fun chunk entry t =>
    addressChunkEntry p.chunkBits chunk (some (lookupIndex trace t.val).toNat) entry

end HonestWitness
