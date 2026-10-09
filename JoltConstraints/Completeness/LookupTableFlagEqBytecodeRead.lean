import JoltConstraints.Completeness.Helpers.BytecodeReadSelection
import JoltConstraints.Constraints.LookupTableFlagEqBytecodeRead
import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.Completeness.Helpers.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
The domain contains every expanded row and the leading no-op slot. -/
theorem honestWitness_lookupTableFlagEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    : lookupTableFlagEqBytecodeRead trace.bytecode
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro table t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeLookupTableFlag trace.bytecode table) t]
  by_cases h : t.val < trace.rows.size
  · simp [HonestTrace.honestWitness, TraceWitness.LookupTableFlag,
      TraceWitness.bytecodePc, bytecodeLookupTableFlag, bytecodeRow, h]
  · simp [HonestTrace.honestWitness, TraceWitness.LookupTableFlag,
      TraceWitness.bytecodePc, bytecodeLookupTableFlag, bytecodeRow, h]

end JoltConstraints
