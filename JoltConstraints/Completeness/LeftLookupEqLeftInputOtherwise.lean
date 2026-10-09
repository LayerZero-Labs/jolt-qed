import JoltConstraints.Constraints.LeftLookupEqLeftInputOtherwise
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

private theorem leftLookupOtherwiseForOpcode {F : Type} [Field F]
    (instruction : JoltISA.Instr) (pc rs1 : F) :
    let left := if JoltMetadata.instructionFlag instruction .LeftOperandIsPC then pc
      else if JoltMetadata.instructionFlag instruction .LeftOperandIsRs1Value then rs1 else 0
    ((1 : F) - (if JoltMetadata.opcodeFlag instruction .AddOperands then 1 else 0) -
      (if JoltMetadata.opcodeFlag instruction .SubtractOperands then 1 else 0) -
      (if JoltMetadata.opcodeFlag instruction .MultiplyOperands then 1 else 0)) *
      ((if JoltMetadata.hasCombinedLookupOperands instruction then 0 else left) - left) = 0 := by
  cases instruction <;>
    simp [JoltMetadata.opcodeFlag, JoltMetadata.instructionFlag,
      JoltMetadata.hasCombinedLookupOperands]

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_leftLookupEqLeftInputOtherwise
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    leftLookupEqLeftInputOtherwise
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases inBounds : t.val < trace.rows.size
  · simpa [HonestTrace.honestWitness, TraceWitness.OpFlags,
      TraceWitness.LeftLookupOperand, TraceWitness.LeftInstructionInput,
      JoltMetadata.circuitFlag, inBounds] using
        (leftLookupOtherwiseForOpcode (F := F)
          (trace.bytecode[(trace.rows[t.val]'inBounds).rowIndex]).instruction
          (TraceWitness.UnexpandedPC params trace t)
          (TraceWitness.Rs1Value params trace t))
  · simp [HonestTrace.honestWitness, TraceWitness.OpFlags,
      TraceWitness.LeftLookupOperand, TraceWitness.LeftInstructionInput, inBounds]

end JoltConstraints
