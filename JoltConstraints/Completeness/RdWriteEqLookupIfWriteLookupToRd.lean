import JoltConstraints.Constraints.RdWriteEqLookupIfWriteLookupToRd
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.Constraints.TracePCProofHelpers

set_option autoImplicit false

namespace JoltConstraints

/-- Completeness statement for the trace validity and trace assumptions. -/
def honestWitness_rdWriteEqLookupIfWriteLookupToRdStatement
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) : Prop :=
    rdWriteEqLookupIfWriteLookupToRd
      (HonestTrace.honestWitness (F := F) params trace)

/-- Every flagged real row writes its lookup result; padded rows have flag zero. -/
theorem honestWitness_rdWriteEqLookupIfWriteLookupToRd
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    rdWriteEqLookupIfWriteLookupToRd
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  simp only [HonestTrace.honestWitness]
  by_cases hb : t.val < trace.rows.size
  · let row := trace.rows[t.val]
    let bc := trace.bytecode[row.rowIndex]
    by_cases hflag : JoltMetadata.circuitFlag bc .WriteLookupOutputToRD = true
    · have hwrite := lookup_row_write (F := F) row (trace.rowValid row.rowIndex) (lookup_trace_PC trace t.val hb) hflag
      simp only [HonestWitness.OpFlags, HonestWitness.RdWriteValue,
        HonestWitness.LookupOutput, dif_pos hb]
      change (if JoltMetadata.circuitFlag bc .WriteLookupOutputToRD then (1 : F) else 0) *
        (HonestWitness.rdValue bc.instruction row.postState -
          ((HonestWitness.rowLookupOutput row).toNat : F)) = 0
      rw [hwrite, sub_self, mul_zero]
    · change ¬ JoltMetadata.circuitFlag
        trace.bytecode[trace.rows[t.val].rowIndex.val] .WriteLookupOutputToRD = true
          at hflag
      simp only [HonestWitness.OpFlags, dif_pos hb, if_neg hflag, zero_mul]
  · simp only [HonestWitness.OpFlags, dif_neg hb, zero_mul]

end JoltConstraints
