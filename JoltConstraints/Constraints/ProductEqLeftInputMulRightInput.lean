import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.witness_helpers

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (20) in `constraints.md` (stage 2): at every padded cycle,
`Product` equals the product of the two instruction inputs. -/
def productEqLeftInputMulRightInput {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.Product t = witness.LeftInstructionInput t * witness.RightInstructionInput t

end JoltConstraints
