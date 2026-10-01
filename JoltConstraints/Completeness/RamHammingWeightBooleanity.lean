import JoltConstraints.Constraints.RamHammingWeightBooleanity
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- The honest witness satisfies constraint (57). -/
theorem honestWitness_ramHammingWeightBooleanity
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    ramHammingWeightBooleanity
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  dsimp [JoltProgram.honestWitness, HonestWitness.RamHammingWeight]
  split_ifs
  · split <;> (try split_ifs) <;> simp_all
  · simp

end JoltConstraints
