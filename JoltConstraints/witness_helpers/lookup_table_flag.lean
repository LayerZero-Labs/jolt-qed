import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.trace
import JoltConstraints.metadata

set_option autoImplicit false

namespace HonestWitness

-- Rust: [LookupTableFlag](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/flags.rs:177).
-- The selected lookup table gets one at this execution row. Every other table
-- gets zero. Instructions without a lookup table and padding give zero for
-- every table. Reuse metadata's instruction-to-table mapping.
noncomputable def LookupTableFlag {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) :
    LookupTableKind → Fin p.traceLength → F :=
  fun table t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
      if JoltMetadata.lookupTableFlag instruction table then 1 else 0
    else 0

end HonestWitness
