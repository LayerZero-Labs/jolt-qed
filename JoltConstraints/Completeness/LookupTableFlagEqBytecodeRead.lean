import JoltConstraints.Constraints.LookupTableFlagEqBytecodeRead
import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.Constraints.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
The domain contains every expanded row and the leading no-op slot. -/
theorem honestWitness_lookupTableFlagEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    : lookupTableFlagEqBytecodeRead program
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro table t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeLookupTableFlag program table) t]
  by_cases h : t.val < trace.rows.size
  · simp [JoltProgram.honestWitness, HonestWitness.LookupTableFlag,
      HonestWitness.bytecodePc, bytecodeLookupTableFlag, bytecodeRow, h]
  · simp [JoltProgram.honestWitness, HonestWitness.LookupTableFlag,
      HonestWitness.bytecodePc, bytecodeLookupTableFlag, bytecodeRow, h]

end JoltConstraints
