import JoltConstraints.Completeness.Helpers.BytecodeReadSelection
import JoltConstraints.Constraints.InstructionRafFlagEqBytecodeRead
import JoltConstraints.Constraints.BytecodeReadSelectors
import JoltConstraints.Completeness.Helpers.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness target for the honest witness.
The domain contains every expanded row and the leading no-op slot. -/
theorem honestWitness_instructionRafFlagEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    : instructionRafFlagEqBytecodeRead trace.bytecode
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeRafFlag trace.bytecode) t]
  by_cases h : t.val < trace.rows.size
  · simp [HonestTrace.honestWitness, TraceWitness.InstructionRafFlag,
      TraceWitness.bytecodePc, bytecodeRafFlag, bytecodeRow, h]
  · simp [HonestTrace.honestWitness, TraceWitness.InstructionRafFlag,
      TraceWitness.bytecodePc, bytecodeRafFlag, bytecodeRow, h]

end JoltConstraints
