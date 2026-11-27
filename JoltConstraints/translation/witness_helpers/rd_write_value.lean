import JoltConstraints.translation.witness
import JoltConstraints.translation.trace
import JoltConstraints.translation.witness_helpers.rd_value

open LeanRV64D

set_option autoImplicit false

namespace TraceWitness

variable {F : Type} (p : WitnessParams)

-- Rust: [RdWriteValue](https://github.com/a16z/jolt/blob/ff6fc656813d950565c9f6e1258b78bdaf0e60e8/crates/jolt-witness/src/witnesses/registers.rs).
-- Capture rd from the post-state; instructions without rd and padding give zero.
noncomputable def RdWriteValue [Field F] (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
      rdValue instruction row.postState
    else 0

end TraceWitness
