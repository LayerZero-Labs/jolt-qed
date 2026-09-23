import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Constraint (20) in `constraints.md` (stage 2): at every padded cycle,
`Product` equals the product of the two instruction inputs. -/
def productEqLeftInputMulRightInput {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.Product t = witness.LeftInstructionInput t * witness.RightInstructionInput t

/-- The honest witness satisfies the product constraint at every padded cycle. -/
theorem honestWitness_productEqLeftInputMulRightInput
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    productEqLeftInputMulRightInput
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  rfl

end JoltConstraints
