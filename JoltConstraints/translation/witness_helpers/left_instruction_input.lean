import JoltConstraints.translation.metadata
import JoltConstraints.translation.witness_helpers.rs1_value
import JoltConstraints.translation.witness_helpers.unexpanded_pc

open LeanRV64D

set_option autoImplicit false

namespace TraceWitness

-- Rust: `crates/jolt-witness/src/witnesses/operands.rs` (`LeftInstructionInput`).
-- The instruction flags select the original instruction address or captured rs1.
-- The floor-addressed loads and stores (VirtualLoadB/H/W, VirtualStoreB/H/W)
-- select rs1 (`crates/jolt-lookup-tables/src/instructions/virt/floor_access.rs`).
-- LD, SD, advice, HOST_IO, and other instructions with neither flag use zero,
-- even if their trace row has a captured source register. Padding is zero.
noncomputable def LeftInstructionInput {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
      if JoltMetadata.instructionFlag instruction .LeftOperandIsPC then
        UnexpandedPC p trace t
      else if JoltMetadata.instructionFlag instruction .LeftOperandIsRs1Value then
        Rs1Value p trace t
      else 0
    else 0

end TraceWitness
