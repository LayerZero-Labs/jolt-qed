import JoltConstraints.Completeness.Helpers.BytecodeReadSelection
import JoltConstraints.Constraints.Rs2RaEqBytecodeRead
import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.Completeness.Helpers.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
The domain contains every expanded row and the leading no-op slot. -/
theorem honestWitness_rs2RaEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    : rs2RaEqBytecodeRead trace.bytecode
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro register t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeRegisterSelector trace.bytecode bytecodeRs2Register register) t]
  by_cases h : t.val < trace.rows.size
  · simp [HonestTrace.honestWitness, TraceWitness.Rs2Ra,
      TraceWitness.bytecodePc, bytecodeRegisterSelector, bytecodeRow, h]
    cases hinst :
      trace.bytecode[↑(trace.rows[↑t].rowIndex)].instruction <;>
      simp [bytecodeRs2Register, eq_comm]
  · simp [HonestTrace.honestWitness, TraceWitness.Rs2Ra,
      TraceWitness.bytecodePc, bytecodeRegisterSelector, bytecodeRow, h]

end JoltConstraints
