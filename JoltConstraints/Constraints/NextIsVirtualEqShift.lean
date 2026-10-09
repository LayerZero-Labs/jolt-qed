import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (29) in `constraints.md` (stage 3): the next virtual-instruction flag
is the current flag shifted by one cycle, with zero at the final cycle. -/
def nextIsVirtualEqShift {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.NextIsVirtual t =
      if nextInBounds : t.val + 1 < params.traceLength then
        witness.OpFlags .VirtualInstruction ⟨t.val + 1, nextInBounds⟩
      else 0

end JoltConstraints
