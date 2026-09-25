import JoltConstraints.Constraints.LookupOperandData
import JoltConstraints.Constraints.InstructionReadSelection

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Constraint (40) in `constraints.md`:
The left lookup operand is zero for identity RAF and the deinterleaved left value otherwise.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs#L181-L201 -/
def leftLookupOperandEqInstructionRaf {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    witness.LeftLookupOperand t =
      ∑ address : Fin (2 ^ 128), instructionLookupRa witness address t *
        (1 - witness.InstructionRafFlag t) * lookupAddressLeft address

/-- Completeness of constraint (40) for the honest witness.
Uses the address-chunk selection and operand-encoding correspondence.
This equation does not require any lookup-table output to be implemented. -/
theorem honestWitness_leftLookupOperandEqInstructionRaf
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    : leftLookupOperandEqInstructionRaf
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
  intro t
  simp only [mul_assoc]
  rw [instructionRead_honest params trace ramFits traceFits bytecodeDomain
    (fun address =>
      (1 - (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain).InstructionRafFlag t) *
        lookupAddressLeft address) t]
  by_cases inBounds : t.val < trace.rows.size
  · -- The selected index must deinterleave to Rust's captured left operand.
    -- Unfolding lookupAddressLeft drops the index's bound proof, so the row's
    -- instruction can be generalized and split by constructor.
    simp only [JoltProgram.honestWitness, HonestWitness.LeftLookupOperand,
      HonestWitness.InstructionRafFlag, HonestWitness.lookupIndex,
      HonestWitness.LeftInstructionInput, HonestWitness.Rs1Value, lookupAddressLeft,
      inBounds, dite_true]
    generalize (program.expandedBytecode[(trace.rows[t.val]'inBounds).rowIndex.val]'
      (trace.rows[t.val]'inBounds).rowIndex.isLt).instruction = instruction
    -- RAF rows are zero on both sides. Interleaved rows recover rs1, while
    -- FENCE, LD, SD, and HostIO have a zero left input and a zero index.
    cases instruction <;>
      simp only [JoltMetadata.hasCombinedLookupOperands, JoltMetadata.instructionRafFlag,
        JoltMetadata.opcodeFlag, JoltMetadata.instructionFlag,
        HonestWitness.instructionLookupIndex,
        Bool.false_eq_true, Bool.or_false, Bool.or_true, ↓reduceIte, sub_zero, sub_self,
        one_mul, zero_mul]
    -- simp rewrites each ite condition but not its Decidable instance, so the
    -- interleaved rows are closed by exact, up to unfolding the lookup index.
    all_goals first
      | exact (sum_interleave_odd_bits _ _).symm
      | simp
  · simp [JoltProgram.honestWitness, HonestWitness.LeftLookupOperand,
      HonestWitness.InstructionRafFlag, HonestWitness.lookupIndex,
      lookupAddressLeft, inBounds]

end JoltConstraints
