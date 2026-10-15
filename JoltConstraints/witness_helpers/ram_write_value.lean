import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.witness_helpers.rd_value

set_option autoImplicit false

namespace TraceWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [RamWriteValue](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/witnesses/ram.rs).
-- Rust: [RAM capture slots](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-riscv/src/trace_row.rs#L388-L464).
-- A load preserves the RAM word, so its captured destination supplies this value.
-- A store supplies its source value from the pre-state, including for device stores
-- whose effects are not an ordinary RAM overwrite. Other instructions and padding
-- contribute zero. Encode the unsigned word in F without executing the instruction.
noncomputable def RamWriteValue [Field F] (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
      match instruction with
      | .LD _ _ _ _ => rdValue instruction row.postState
      | .SD _ value _ => ((JoltISA.sourceValue value row.preState).toNat : F)
      | _ => 0
    else 0

end TraceWitness
