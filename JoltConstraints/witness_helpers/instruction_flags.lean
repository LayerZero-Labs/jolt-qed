import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.metadata

set_option autoImplicit false

-- Rust paths are relative to /Users/ari.biswas/Work-with-A16z/jolt.

namespace HonestWitness

variable {F : Type} (p : WitnessParams)

-- Rust: crates/jolt-witness/src/witnesses/flags.rs::InstructionFlag::{extract_indexed, to_field}.
-- Rust: crates/jolt-witness/src/backend/trace/cycle.rs::walk_cycles;
-- crates/jolt-riscv/src/instructions/i/noop.rs (padding sets only IsNoop).
-- Instruction-flag bits over the padded witness; padding sets only IsNoop to one.
noncomputable def InstructionFlags [Field F] {program : JoltProgram}
    (trace : JoltTrace program) : _root_.InstructionFlags → Fin p.traceLength → F :=
  fun flag t =>
    -- t indexes the padded witness; the else branch represents a padding position.
    -- inBounds supplies the proof needed to read an actual execution row.
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
      if JoltMetadata.instructionFlag instruction flag then
        1
      else 0
    else
      match flag with
      | .IsNoop => 1
      | _ => 0

end HonestWitness
