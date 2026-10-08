import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness_helpers.ram_ra_chunk

set_option autoImplicit false

namespace TraceWitness

-- Rust: [materialize_ram_ra](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/ram.rs:51).
-- Select the accessed word, using the same remapping as RamRaChunk. Instructions
-- without a memory access, raw address zero, and padding give all-zero columns.
noncomputable def RamRa {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) :
    Fin p.ramSize → Fin p.traceLength → F :=
  fun address t =>
    if remappedRamAddress trace t.val = some address.val then 1 else 0

end TraceWitness
