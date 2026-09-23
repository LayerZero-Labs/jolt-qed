import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (28) in `constraints.md` (stage 3): the next expanded PC is the
current expanded-PC column shifted by one cycle, with zero at the final cycle. -/
def nextPCEqShift {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.NextPC t =
      if nextInBounds : t.val + 1 < params.traceLength then
        witness.PC ⟨t.val + 1, nextInBounds⟩
      else 0

/-- The honest witness satisfies the NextPC shift constraint at every padded cycle. -/
theorem honestWitness_nextPCEqShift
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    nextPCEqShift
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  sorry

end JoltConstraints
