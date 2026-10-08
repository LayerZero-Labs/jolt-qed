import JoltConstraints.Completeness.Helpers.InstructionReadSelection
import JoltConstraints.Constraints.RightLookupOperandEqInstructionRaf
import JoltConstraints.Constraints.LookupOperandData
import JoltConstraints.Completeness.Helpers.InstructionReadSelection

set_option autoImplicit false

namespace JoltConstraints

open scoped BigOperators

/-- Completeness of constraint (41) for the honest witness.
Uses the address-chunk selection and operand-encoding correspondence.
The entire 128-bit address is cast into F, preserving arithmetic carry. -/
theorem honestWitness_rightLookupOperandEqInstructionRaf
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    : rightLookupOperandEqInstructionRaf
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  rw [instructionRead_honest params trace ramFits traceFits bytecodeDomain
    (fun address =>
      (1 - (HonestTrace.honestWitness (F := F) params trace).InstructionRafFlag t) *
          lookupAddressRight address +
        (HonestTrace.honestWitness (F := F) params trace).InstructionRafFlag t *
          (address.val : F)) t]
  by_cases inBounds : t.val < trace.rows.size
  · -- Combined operands use the full index; ordinary operands deinterleave it.
    -- Unfolding lookupAddressRight drops the index's bound proof, so the row's
    -- instruction can be generalized and split by constructor.
    simp only [HonestTrace.honestWitness, TraceWitness.RightLookupOperand,
      TraceWitness.InstructionRafFlag, TraceWitness.lookupIndex,
      TraceWitness.RightInstructionInput, TraceWitness.Imm, TraceWitness.Rs2Value,
      lookupAddressRight, inBounds, dite_true]
    generalize (trace.bytecode[(trace.rows[t.val]'inBounds).rowIndex.val]'
      (trace.rows[t.val]'inBounds).rowIndex.isLt).instruction = instruction
    -- RAF rows keep the full index on both sides. Interleaved rows recover the
    -- immediate or rs2, while FENCE, LD, SD, and HostIO have zero input and index.
    cases instruction <;>
      simp only [JoltMetadata.hasCombinedLookupOperands, JoltMetadata.instructionRafFlag,
        JoltMetadata.opcodeFlag, JoltMetadata.instructionFlag, JoltMetadata.immediate,
        TraceWitness.instructionLookupIndex, Int.cast_natCast,
        Bool.false_eq_true, Bool.or_false, Bool.or_true, ↓reduceIte, sub_zero, sub_self,
        one_mul, zero_mul, zero_add, add_zero]
    -- simp rewrites each ite condition but not its Decidable instance, so the
    -- interleaved rows are closed by exact, up to unfolding the lookup index.
    all_goals first
      | exact (sum_interleave_even_bits _ _).symm
      | simp
  · simp [HonestTrace.honestWitness, TraceWitness.RightLookupOperand,
      TraceWitness.InstructionRafFlag, TraceWitness.lookupIndex,
      lookupAddressRight, inBounds]

end JoltConstraints
