import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers.ram_state

set_option autoImplicit false

namespace HonestWitness

-- Rust: [materialize_ram_val_final](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/ram.rs:70).
-- Encode the final memory image over the RAM address domain. This is independent
-- of witness padding and need not equal the last RamVal column: Rust rebuilds it
-- from the final snapshot, including its special panic/termination words.
noncomputable def RamValFinal {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) : Fin p.ramSize → F :=
  fun address => ((finalRamWord trace address.val).toNat : F)

end HonestWitness
