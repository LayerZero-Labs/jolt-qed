import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (27) in `constraints.md` (stage 3): the next unexpanded PC is the
current unexpanded-PC column shifted by one cycle, with zero at the final cycle. -/
def nextUnexpandedPCEqShift {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.NextUnexpandedPC t =
      if nextInBounds : t.val + 1 < params.traceLength then
        witness.UnexpandedPC ⟨t.val + 1, nextInBounds⟩
      else 0

/-- The honest witness satisfies the NextUnexpandedPC shift constraint at every padded cycle. -/
theorem honestWitness_nextUnexpandedPCEqShift
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : trace.rows.size ≤ params.traceLength) :
    nextUnexpandedPCEqShift
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits) := by
  sorry

end JoltConstraints
