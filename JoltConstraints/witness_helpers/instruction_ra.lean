import JoltConstraints.witness_helpers.address_chunk
import JoltConstraints.witness_helpers.lookup_index
import JoltConstraints.witness

set_option autoImplicit false

namespace HonestWitness

-- Rust: [oracle_table InstructionRa](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/oracle.rs).
-- The same lookup address as InstructionRaChunk, split into wider virtual
-- chunks. "Virtual" refers to a witness family, not to virtual ISA instructions.
noncomputable def InstructionRa {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) :
    Fin p.virtualInstructionChunks → Fin (2 ^ p.virtualChunkBits) → Fin p.traceLength → F :=
  fun chunk entry t =>
    addressChunkEntry p.virtualChunkBits chunk (some (lookupIndex trace t.val).toNat) entry

end HonestWitness
