import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.metadata

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::OpFlag::{extract_indexed, to_field}.
-- Rust: crates/jolt-witness/src/backend/trace/cycle.rs::walk_cycles.
-- Rust: [no-op circuit flags](https://github.com/abiswas3/jolt/tree/main/crates/jolt-riscv/src/instructions/mod.rs#L536-L543).
-- Circuit-flag bits over the padded witness. Padding sets only
-- DoNotUpdateUnexpandedPC to one, keeping its zero unexpanded PC unchanged.
noncomputable def OpFlags [Field F] {program : JoltProgram}
    (trace : JoltTrace program) : CircuitFlags → Fin p.traceLength → F :=
  fun flag t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let bytecodeRow := getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt
      if JoltMetadata.circuitFlag bytecodeRow flag then 1 else 0
    else
      match flag with
      | .DoNotUpdateUnexpandedPC => 1
      | _ => 0

end HonestWitness
