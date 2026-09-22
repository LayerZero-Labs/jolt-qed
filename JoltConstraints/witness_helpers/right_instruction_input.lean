import JoltConstraints.metadata
import JoltConstraints.witness_helpers.rs2_value
import JoltConstraints.witness_helpers.imm

set_option autoImplicit false

namespace HonestWitness

-- Rust: [RightInstructionInput](/Users/ari.biswas/Work-with-A16z/jolt/crates/jolt-witness/src/witnesses/operands.rs:96).
-- Use the same normalized immediate as Imm when the instruction's flag selects
-- it, or captured rs2 when the register flag is set. These flags describe lookup
-- inputs: loads/stores/advice/HOST_IO have zero inputs despite captured operands.
-- I/U/J and alignment immediates are unsigned 64-bit values widened to i128.
-- Padding contributes zero.
noncomputable def RightInstructionInput {F : Type} [Field F] (p : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt).instruction
      if JoltMetadata.instructionFlag instruction .RightOperandIsImm then
        Imm p trace t
      else if JoltMetadata.instructionFlag instruction .RightOperandIsRs2Value then
        Rs2Value p trace t
      else 0
    else 0

end HonestWitness
