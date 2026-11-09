import JoltConstraints.metadata
import JoltConstraints.witness_helpers.rs2_value
import JoltConstraints.witness_helpers.imm
import JoltConstraints.witness_helpers.rd_write_value

open LeanRV64D

set_option autoImplicit false

namespace TraceWitness

/-- The sum of the selected second-source, immediate and captured-destination
values in the field; padding contributes zero.
For example, ShiftData with rs2 = 10 and immediate -2 contributes 8,
while LD contributes its captured destination value.
Jolt's prover: `crates/jolt-lookup-tables/src/instructions/virt/shift_data_b.rs`
and `instructions/riscv/ld.rs` (`to_instruction_inputs`) at `c6703570`. -/
noncomputable def RightInstructionInput {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
      (if JoltMetadata.instructionFlag instruction .RightOperandIsRs2Value then
        Rs2Value p trace t else 0) +
      (if JoltMetadata.instructionFlag instruction .RightOperandIsImm then
        Imm p trace t else 0) +
      (if JoltMetadata.instructionFlag instruction .RightOperandIsRdWriteValue then
        RdWriteValue p trace t else 0)
    else 0

end TraceWitness
