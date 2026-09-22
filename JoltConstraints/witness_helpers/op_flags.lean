import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.metadata

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::OpFlag::{extract_indexed, to_field}.
-- Rust: crates/jolt-witness/src/backend/trace/cycle.rs::walk_cycles;
-- crates/jolt-riscv/src/instructions/i/noop.rs (padding has no circuit flags).
-- Circuit-flag bits over the padded witness; every padding bit is zero.
noncomputable def OpFlags [Field F] {program : JoltProgram}
    (trace : JoltTrace program) : CircuitFlags → Fin p.traceLength → F :=
  fun flag t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let bytecodeRow := getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt
      if JoltMetadata.circuitFlag bytecodeRow flag then 1 else 0
    else 0

end HonestWitness
