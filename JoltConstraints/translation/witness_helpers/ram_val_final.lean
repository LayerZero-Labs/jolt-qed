import JoltConstraints.translation.witness_helpers.ram_state

open LeanRV64D

set_option autoImplicit false

namespace TraceWitness

-- Rust: `crates/jolt-witness/src/backend/trace/ram.rs` (`materialize_ram_val_final`).
-- Encode the final memory image over the RAM address domain. This is independent
-- of witness padding and need not equal the last RamVal column: Rust rebuilds it
-- from the final shared-memory snapshot, including the input/output window.
noncomputable def RamValFinal {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) : Fin p.ramSize → F :=
  fun address => ((finalRamWord trace address.val).toNat : F)

end TraceWitness
