import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness_domain

set_option autoImplicit false

namespace HonestWitness

-- Rust: [materialize_ram_ra](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/ram.rs:51).
-- Select the accessed word, using the same remapping as RamRaChunk. Instructions
-- without a memory access, raw address zero, and padding give all-zero columns.
-- The required proof rules out Rust's remapping and domain-bound errors; it has
-- no runtime role in computing the entries.
noncomputable def RamRa {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) (_ramFits : p.RamFits trace) :
    Fin p.ramSize → Fin p.traceLength → F :=
  fun address t =>
    if remappedRamAddress trace t.val = some address.val then 1 else 0

end HonestWitness
