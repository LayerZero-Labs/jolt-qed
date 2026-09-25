import JoltConstraints.metadata
import JoltConstraints.witness_helpers.rs1_value
import JoltConstraints.witness_helpers.unexpanded_pc

set_option autoImplicit false

namespace HonestWitness

-- Rust: [LeftInstructionInput](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/operands.rs:77).
-- The instruction flags select the original instruction address or captured rs1.
-- Loads, stores, advice, HOST_IO, and other instructions with neither flag use
-- zero, even if their trace row has a captured source register. Padding is zero.
noncomputable def LeftInstructionInput {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
      if JoltMetadata.instructionFlag instruction .LeftOperandIsPC then
        UnexpandedPC p trace t
      else if JoltMetadata.instructionFlag instruction .LeftOperandIsRs1Value then
        Rs1Value p trace t
      else 0
    else 0

end HonestWitness
