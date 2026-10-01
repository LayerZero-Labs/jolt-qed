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

end JoltConstraints
