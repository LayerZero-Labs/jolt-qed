import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.Constraints.TracePCProofHelpers

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (13) in `constraints.md` (stage 1):
rows with WriteLookupOutputToRD copy the lookup output to the destination.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def rdWriteEqLookupIfWriteLookupToRd {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.OpFlags .WriteLookupOutputToRD t *
      (witness.RdWriteValue t - witness.LookupOutput t) = 0

/-- Completeness statement for the program validity and trace assumptions. -/
def honestWitness_rdWriteEqLookupIfWriteLookupToRdStatement
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) : Prop :=
    rdWriteEqLookupIfWriteLookupToRd
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain)

/-- Every flagged real row writes its lookup result; padded rows have flag zero. -/
theorem honestWitness_rdWriteEqLookupIfWriteLookupToRd
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    rdWriteEqLookupIfWriteLookupToRd
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  simp only [JoltProgram.honestWitness]
  by_cases hb : t.val < trace.rows.size
  · let row := trace.rows[t.val]
    let bc := program.expandedBytecode[row.rowIndex]
    by_cases hflag : JoltMetadata.circuitFlag bc .WriteLookupOutputToRD = true
    · have hwrite := lookup_row_write (F := F) row (lookup_trace_PC trace t.val hb) hflag
      simp only [HonestWitness.OpFlags, HonestWitness.RdWriteValue,
        HonestWitness.LookupOutput, dif_pos hb]
      change (if JoltMetadata.circuitFlag bc .WriteLookupOutputToRD then (1 : F) else 0) *
        (HonestWitness.rdValue bc.expandedInstruction row.postState -
          ((HonestWitness.rowLookupOutput row).toNat : F)) = 0
      rw [hwrite, sub_self, mul_zero]
    · change ¬ JoltMetadata.circuitFlag
        program.expandedBytecode[trace.rows[t.val].rowIndex.val] .WriteLookupOutputToRD = true
          at hflag
      simp only [HonestWitness.OpFlags, dif_pos hb, if_neg hflag, zero_mul]
  · simp only [HonestWitness.OpFlags, dif_neg hb, zero_mul]

end JoltConstraints
