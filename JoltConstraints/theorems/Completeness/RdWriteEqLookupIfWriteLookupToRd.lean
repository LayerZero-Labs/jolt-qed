import JoltConstraints.theorems.Completeness.Helpers.TracePCProofHelpers
import JoltConstraints.translation.Constraints.RdWriteEqLookupIfWriteLookupToRd
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.Completeness.Helpers.TracePCProofHelpers
import JoltConstraints.theorems.witness_domain
import JoltConstraints.theorems.Completeness.Helpers.LookupWriteProofHelpers

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Completeness statement for the trace validity and trace assumptions. -/
def honestWitness_rdWriteEqLookupIfWriteLookupToRdStatement
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) : Prop :=
    rdWriteEqLookupIfWriteLookupToRd
      (HonestTrace.honestWitness (F := F) params trace)

/-- Every flagged real row writes its lookup result; padded rows have flag zero. -/
theorem honestWitness_rdWriteEqLookupIfWriteLookupToRd
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    rdWriteEqLookupIfWriteLookupToRd
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  simp only [HonestTrace.honestWitness]
  by_cases hb : t.val < trace.rows.size
  · let row := trace.row t.val (by omega)
    let bc := trace.bytecode[row.rowIndex]
    by_cases hflag : JoltMetadata.circuitFlag bc .WriteLookupOutputToRD = true
    · have hwrite := lookup_row_write (F := F) row (trace.rowValid row.rowIndex) (lookup_trace_PC trace t.val hb) hflag
      simp only [TraceWitness.OpFlags, TraceWitness.RdWriteValue,
        TraceWitness.LookupOutput, dite_eq_left hb]
      change (if JoltMetadata.circuitFlag bc .WriteLookupOutputToRD then (1 : F) else 0) *
        (TraceWitness.rdValue bc.instruction row.postState -
          ((TraceWitness.rowLookupOutput row.toTraceRow).toNat : F)) = 0
      rw [hwrite, sub_self, mul_zero]
    · change ¬ JoltMetadata.circuitFlag
        trace.bytecode[trace.rows[t.val].rowIndex.val] .WriteLookupOutputToRD = true
          at hflag
      simp only [TraceWitness.OpFlags, dite_eq_left hb, ite_eq_right hflag, zero_mul]
  · simp only [TraceWitness.OpFlags, dite_eq_right hb, zero_mul]

end JoltConstraints
