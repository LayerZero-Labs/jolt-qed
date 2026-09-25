import JoltConstraints.witness_helpers.right_instruction_input
import JoltConstraints.witness_helpers.lookup_index

set_option autoImplicit false

namespace HonestWitness

-- Rust: [RightLookupOperand](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/operands.rs:63).
-- Preserve all 128 bits of a combined lookup index, including arithmetic carry.
-- Other tables use the unsigned 64-bit right instruction input. Padding is zero.
noncomputable def RightLookupOperand {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
      if JoltMetadata.hasCombinedLookupOperands instruction then
        ((lookupIndex trace t.val).toNat : F)
      else RightInstructionInput p trace t
    else 0

end HonestWitness
