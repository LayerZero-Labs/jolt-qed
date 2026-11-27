import JoltConstraints.translation.metadata
import JoltConstraints.translation.trace

open LeanRV64D

set_option autoImplicit false

namespace TraceWitness

-- Rust: `crates/jolt-witness/src/witnesses/operands.rs` (`Imm`).
-- Encode the complete normalized immediate as a signed field value, regardless
-- of whether execution or the lookup query uses it. Padding contributes zero.
noncomputable def Imm {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
      (JoltMetadata.immediate instruction : F)
    else 0

end TraceWitness
