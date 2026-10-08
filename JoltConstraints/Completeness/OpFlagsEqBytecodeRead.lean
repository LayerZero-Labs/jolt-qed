import JoltConstraints.Completeness.Helpers.BytecodeReadSelection
import JoltConstraints.Constraints.OpFlagsEqBytecodeRead
import JoltConstraints.Constraints.BytecodeReadData
import JoltConstraints.Completeness.Helpers.BytecodeReadSelection
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- The honest witness satisfies constraint (46).
The bytecode domain must contain every trace row and the leading no-op slot.
This bound prevents the address chunks from truncating an executed bytecode PC. -/
theorem honestWitness_opFlagsEqBytecodeRead
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    opFlagsEqBytecodeRead trace.bytecode
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro flag t
  rw [bytecodeRead_honest params trace ramFits traceFits bytecodeDomain
    (bytecodeCircuitFlag trace.bytecode flag) t]
  by_cases h : t.val < trace.rows.size
  · simp [HonestTrace.honestWitness, TraceWitness.OpFlags,
      TraceWitness.bytecodePc, bytecodeCircuitFlag, bytecodeRow, h]
  · cases flag <;>
      simp [HonestTrace.honestWitness, TraceWitness.OpFlags,
        TraceWitness.bytecodePc, bytecodeCircuitFlag, bytecodeRow, h]

end JoltConstraints
