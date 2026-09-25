import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness

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

/-- Constraint (06) in `constraints.md` (stage 1):
addition, subtraction and multiplication use zero as their left lookup operand.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def leftLookupZeroIfAddSubMul {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (witness.OpFlags .AddOperands t + witness.OpFlags .SubtractOperands t +
      witness.OpFlags .MultiplyOperands t) * witness.LeftLookupOperand t = 0

/-- Completeness target for the honest witness; proof pending. -/
theorem honestWitness_leftLookupZeroIfAddSubMul
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    leftLookupZeroIfAddSubMul
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  by_cases inBounds : t.val < trace.rows.size
  · simpa [JoltProgram.honestWitness, HonestWitness.OpFlags,
      HonestWitness.LeftLookupOperand, JoltMetadata.circuitFlag, inBounds] using
        (arithmeticLeftLookupIsZero (F := F)
          (program.expandedBytecode[(trace.rows[t.val]'inBounds).rowIndex]).instruction
          (HonestWitness.LeftInstructionInput params trace t))
  · simp [JoltProgram.honestWitness, HonestWitness.OpFlags,
      HonestWitness.LeftLookupOperand, inBounds]

end JoltConstraints
