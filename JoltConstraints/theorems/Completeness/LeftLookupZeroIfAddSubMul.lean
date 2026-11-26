import JoltConstraints.translation.Constraints.LeftLookupZeroIfAddSubMul
import JoltConstraints.translation.honest_witness
import JoltConstraints.theorems.witness_domain

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

private theorem arithmeticLeftLookupIsZero {F : Type} [Field F]
    (instruction : JoltISA.Instr) (left : F) :
    ((if JoltMetadata.opcodeFlag instruction .AddOperands then 1 else 0) +
      (if JoltMetadata.opcodeFlag instruction .SubtractOperands then 1 else 0) +
      (if JoltMetadata.opcodeFlag instruction .MultiplyOperands then 1 else 0)) *
      (if JoltMetadata.hasCombinedLookupOperands instruction then 0 else left) = 0 := by
  cases instruction <;>
    simp [JoltMetadata.opcodeFlag, JoltMetadata.hasCombinedLookupOperands]

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_leftLookupZeroIfAddSubMul
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (_ramFits : params.RamFits trace)
    (_traceFits : params.ProverPaddedFor trace.rows.size)
    (_bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    leftLookupZeroIfAddSubMul
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases inBounds : t.val < trace.rows.size
  · simpa [HonestTrace.honestWitness, TraceWitness.OpFlags,
      TraceWitness.LeftLookupOperand, JoltMetadata.circuitFlag, inBounds] using!
        (arithmeticLeftLookupIsZero (F := F)
          (trace.bytecode[(trace.rows[t.val]'inBounds).rowIndex]).instruction
          (TraceWitness.LeftInstructionInput params trace t))
  · simp [HonestTrace.honestWitness, TraceWitness.OpFlags,
      TraceWitness.LeftLookupOperand, inBounds]

end JoltConstraints
