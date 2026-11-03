import JoltConstraints.witness_helpers.right_instruction_input
import JoltConstraints.witness_helpers.lookup_index
import JoltConstraints.lookup_table

set_option autoImplicit false

namespace TraceWitness

/-- The combined 128-bit index, or the right input wrapped to 64 bits for
interleaved rows, recovered from their lookup index; padding contributes zero.
For example, ShiftData with rs2 = 0 and immediate -1 contributes `2^64 - 1`.
Jolt's prover: `crates/jolt-lookup-tables/src/traits.rs`
(`LookupQuery::to_lookup_operands`) and
`crates/jolt-witness/src/witnesses/operands.rs` (`RightLookupOperand`) at `c6703570`. -/
noncomputable def RightLookupOperand {F : Type} [Field F] (p : WitnessParams)
    (trace : Trace) : Fin p.traceLength → F :=
  fun t =>
    if inBounds : t.val < trace.rows.size then
      let row := getElem trace.rows t.val inBounds
      let instruction :=
        (getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt).instruction
      if JoltMetadata.hasCombinedLookupOperands instruction then
        ((lookupIndex trace t.val).toNat : F)
      else ((JoltConstraints.uninterleave (lookupIndex trace t.val).toFin).2.toNat : F)
    else 0

end TraceWitness
