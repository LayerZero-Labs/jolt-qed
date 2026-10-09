import JoltConstraints.execution_facts
import JoltConstraints.metadata
import JoltConstraints.honest_witness_helpers.ram_read_value
import JoltConstraints.witness_helpers.ram_write_value

set_option autoImplicit false

namespace HonestWitness

open TraceWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [RamInc::extract](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/increments.rs:45).
-- Stores contribute the new RAM word minus the old word, subtracting in F to
-- preserve signed decreases. Reads, other instructions, and padding contribute zero.
noncomputable def RamInc [Field F] {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let bytecodeRow := getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt
      if JoltMetadata.circuitFlag bytecodeRow .Store then
        RamWriteValue p trace t - RamReadValue p trace t
      else 0
    else 0

end HonestWitness
