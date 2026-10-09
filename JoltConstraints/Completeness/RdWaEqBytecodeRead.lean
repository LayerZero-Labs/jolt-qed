import JoltConstraints.Completeness.Helpers.BytecodeReadSelection
import JoltConstraints.Constraints.RdWaEqBytecodeRead
import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.Completeness.Helpers.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target. Both selectors read the destination
recorded in the expanded row, including x0, without a second source rewrite.
The bytecode domain contains every expanded row and its leading padding slot. -/
theorem honestWitness_rdWaEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    : rdWaEqBytecodeRead trace.bytecode
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro register t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeRegisterSelector trace.bytecode bytecodeRdRegister register) t]
  by_cases h : t.val < trace.rows.size
  · simp [HonestTrace.honestWitness, TraceWitness.RdWa,
      TraceWitness.bytecodePc, bytecodeRegisterSelector, bytecodeRow, h]
    cases hinst :
      trace.bytecode[↑(trace.rows[↑t].rowIndex)].instruction <;>
      simp [bytecodeRdRegister, eq_comm]
  · simp [HonestTrace.honestWitness, TraceWitness.RdWa,
      TraceWitness.bytecodePc, bytecodeRegisterSelector, bytecodeRow, h]

end JoltConstraints
