import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

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

end JoltConstraints
