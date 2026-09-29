import JoltConstraints.metadata
import JoltConstraints.witness_helpers.ram_read_value
import JoltConstraints.witness_helpers.ram_write_value

set_option autoImplicit false

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [RamInc::extract](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/increments.rs:45).
-- Stores contribute the new RAM word minus the old word, subtracting in F to
-- preserve signed decreases. Reads, other instructions, and padding contribute zero.
noncomputable def RamInc [Field F] {program : JoltProgram}
    (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let bytecodeRow := getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt
      if JoltMetadata.circuitFlag bytecodeRow .Store then
        RamWriteValue p trace t - RamReadValue p trace t
      else 0
    else 0

end HonestWitness
