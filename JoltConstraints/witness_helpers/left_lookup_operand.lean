import JoltConstraints.witness_helpers.left_instruction_input

set_option autoImplicit false

namespace HonestWitness

-- Rust: [LeftLookupOperand](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/operands.rs:45).
-- Combined-operand tables put the entire lookup index on the right and zero
-- on the left. Other tables use the left instruction input. Padding is zero.
noncomputable def LeftLookupOperand {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
      if JoltMetadata.hasCombinedLookupOperands instruction then 0
      else LeftInstructionInput p trace t
    else 0

end HonestWitness
