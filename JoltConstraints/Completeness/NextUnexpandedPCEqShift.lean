import JoltConstraints.Constraints.NextUnexpandedPCEqShift
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies the NextUnexpandedPC shift constraint at every padded cycle. -/
theorem honestWitness_nextUnexpandedPCEqShift
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    nextUnexpandedPCEqShift
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  rfl

end JoltConstraints
