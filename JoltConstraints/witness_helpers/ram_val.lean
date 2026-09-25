import JoltConstraints.witness_helpers.ram_state
import JoltConstraints.witness_helpers.ram_ra
import JoltConstraints.witness_helpers.ram_read_value
import JoltConstraints.witness_helpers.ram_write_value
import JoltConstraints.witness_helpers.op_flags

set_option autoImplicit false

namespace HonestWitness

-- Rust: [materialize_ram_val](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/backend/trace/ram.rs:22).
-- Start from the initial image and apply preceding captured stores. At the
-- current accessed address, use the captured PRE-access read value. This override
-- matters for device words whose readback differs from their last stored value.
-- Loads do not change the accumulated array; padding keeps its last contents.
noncomputable def RamVal {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) (ramFits : p.RamFits trace) :
    Fin p.ramSize → Fin p.traceLength → F :=
  fun address t =>
    let before := (List.finRange t.val).foldl (fun value i =>
      let cycle : Fin p.traceLength := ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩
      let writes := OpFlags p trace .Store cycle * RamRa p trace ramFits address cycle
      value + writes * (RamWriteValue p trace cycle - value))
      ((initialRamWord program address.val).toNat : F)
    before + RamRa p trace ramFits address t * (RamReadValue p trace t - before)

end HonestWitness
