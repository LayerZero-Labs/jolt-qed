import JoltConstraints.Constraints.RamAddrEqRs1PlusImmIfLoadStore
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- Completeness target for the honest witness; proof pending.
The statement is provisional until the required validity assumptions are added.
TODO: Relate the wrapping 64-bit address calculation to field addition;
rule out address wraparound in the admissible execution assumptions. -/
theorem honestWitness_ramAddrEqRs1PlusImmIfLoadStore
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    ramAddrEqRs1PlusImmIfLoadStore
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  sorry

end JoltConstraints
