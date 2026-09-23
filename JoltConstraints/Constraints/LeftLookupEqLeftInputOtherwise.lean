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

/-- Constraint (07) in `constraints.md` (stage 1):
the other operand modes preserve the left instruction input.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def leftLookupEqLeftInputOtherwise {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (1 - witness.OpFlags .AddOperands t - witness.OpFlags .SubtractOperands t -
      witness.OpFlags .MultiplyOperands t) *
      (witness.LeftLookupOperand t - witness.LeftInstructionInput t) = 0

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_leftLookupEqLeftInputOtherwise
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    leftLookupEqLeftInputOtherwise
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  by_cases inBounds : t.val < trace.rows.size
  · simpa [JoltProgram.honestWitness, HonestWitness.OpFlags,
      HonestWitness.LeftLookupOperand, HonestWitness.LeftInstructionInput,
      JoltMetadata.circuitFlag, inBounds] using
        (leftLookupOtherwiseForOpcode (F := F)
          (program.expandedBytecode[(trace.rows[t.val]'inBounds).rowIndex]).instruction
          (HonestWitness.UnexpandedPC params trace t)
          (HonestWitness.Rs1Value params trace t))
  · simp [JoltProgram.honestWitness, HonestWitness.OpFlags,
      HonestWitness.LeftLookupOperand, HonestWitness.LeftInstructionInput, inBounds]

end JoltConstraints
