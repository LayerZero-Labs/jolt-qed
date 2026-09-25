import Mathlib.Algebra.Field.Defs
import JoltConstraints.metadata

set_option autoImplicit false

namespace HonestWitness

-- Rust: [Imm](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/operands.rs:146).
-- Encode the complete normalized immediate as a signed field value, regardless
-- of whether execution or the lookup query uses it. Padding contributes zero.
noncomputable def Imm {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
      (JoltMetadata.immediate instruction : F)
    else 0

end HonestWitness
