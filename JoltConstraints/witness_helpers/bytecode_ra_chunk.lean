import JoltConstraints.witness_helpers.address_chunk
import JoltConstraints.witness_helpers.pc

set_option autoImplicit false

namespace HonestWitness

-- Rust: [BytecodeRaChunk](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/one_hot.rs:121).
-- Encode the static bytecode slot, not the trace position: executing the same
-- instruction twice selects the same address. Padding selects slot 0.
noncomputable def BytecodeRaChunk {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) :
    Fin p.bytecodeChunks → Fin (2 ^ p.chunkBits) → Fin p.traceLength → F :=
  fun chunk entry t =>
    addressChunkEntry p.chunkBits chunk (some (bytecodePc trace t.val)) entry

end HonestWitness
