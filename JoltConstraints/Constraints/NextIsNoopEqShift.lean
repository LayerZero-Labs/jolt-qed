import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (31) in `constraints.md` (stage 3): the next no-op flag is the
current no-op flag shifted by one cycle, with one at the final cycle. -/
def nextIsNoopEqShift {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.NextIsNoop t =
      if nextInBounds : t.val + 1 < params.traceLength then
        witness.InstructionFlags .IsNoop ⟨t.val + 1, nextInBounds⟩
      else 1

/-- The honest witness satisfies the NextIsNoop shift constraint at every padded cycle. -/
theorem honestWitness_nextIsNoopEqShift
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace) :
    nextIsNoopEqShift
      (JoltProgram.honestWitness (F := F) params trace ramFits) := by
  sorry

end JoltConstraints
