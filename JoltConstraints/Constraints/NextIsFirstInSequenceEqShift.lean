import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (30) in `constraints.md` (stage 3): the next first-in-sequence flag
is the current flag shifted by one cycle, with zero at the final cycle. -/
def nextIsFirstInSequenceEqShift {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.NextIsFirstInSequence t =
      if nextInBounds : t.val + 1 < params.traceLength then
        witness.OpFlags .IsFirstInSequence ⟨t.val + 1, nextInBounds⟩
      else 0

end JoltConstraints
