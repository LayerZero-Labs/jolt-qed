import JoltConstraints.Constraints.RightLookupEqRightInputOtherwise
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

private theorem rightLookupOtherwiseForOpcode {F : Type} [Field F]
    (instruction : JoltISA.Instr) (lookup right : F) :
    ((1 : F) - (if JoltMetadata.opcodeFlag instruction .AddOperands then 1 else 0) -
      (if JoltMetadata.opcodeFlag instruction .SubtractOperands then 1 else 0) -
      (if JoltMetadata.opcodeFlag instruction .MultiplyOperands then 1 else 0) -
      (if JoltMetadata.opcodeFlag instruction .Advice then 1 else 0)) *
      ((if JoltMetadata.hasCombinedLookupOperands instruction then lookup else right) - right) = 0 := by
  cases instruction <;>
    simp [JoltMetadata.opcodeFlag, JoltMetadata.hasCombinedLookupOperands]

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_rightLookupEqRightInputOtherwise
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    rightLookupEqRightInputOtherwise
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  by_cases inBounds : t.val < trace.rows.size
  · simpa [JoltProgram.honestWitness, HonestWitness.OpFlags,
      HonestWitness.RightLookupOperand, JoltMetadata.circuitFlag, inBounds] using
        (rightLookupOtherwiseForOpcode (F := F)
          (program.expandedBytecode[(trace.rows[t.val]'inBounds).rowIndex]).expandedInstruction
          ((HonestWitness.lookupIndex trace t.val).toNat : F)
          (HonestWitness.RightInstructionInput params trace t))
  · simp [JoltProgram.honestWitness, HonestWitness.OpFlags,
      HonestWitness.RightLookupOperand, HonestWitness.RightInstructionInput, inBounds]

end JoltConstraints
