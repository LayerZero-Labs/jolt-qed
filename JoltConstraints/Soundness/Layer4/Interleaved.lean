import JoltConstraints.Soundness.Layer4.Table
import JoltConstraints.Soundness.Layer4.Interleave
import JoltConstraints.Soundness.Layer0.Words

/-! Recover both 64-bit operands when the lookup RAF flag is zero. The field
encodings determine each word separately, so the weaker `2^127` characteristic
bound suffices even though the combined lookup address has 128 bits.
Operand agreement is a local obligation for the later instruction proofs. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include charAbove2pow127 context equations

/-- At RAF flag zero, the selected address decodes to the two words whose field
encodings appear in the lookup operand columns. -/
theorem uninterleave_of_lookup_operands (t : Fin params.traceLength)
    (address : Fin (2 ^ 128)) (selected : instructionLookupRa witness address t = 1)
    (lhs rhs : BitVec 64) (raf : witness.InstructionRafFlag t = 0)
    (left : witness.LeftLookupOperand t = (lhs.toNat : F))
    (right : witness.RightLookupOperand t = (rhs.toNat : F)) :
    uninterleave address = (lhs, rhs) := by
  have leftRead := leftLookupOperand_of_selected
    charAbove2pow127 context equations t address selected
  have rightRead := rightLookupOperand_of_selected
    charAbove2pow127 context equations t address selected
  apply Prod.ext
  · apply word_eq_of_field_eq charAbove2pow127
    simpa only [raf, sub_zero, one_mul, lookupAddressLeft_eq_uninterleave] using
      leftRead.symm.trans left
  · apply word_eq_of_field_eq charAbove2pow127
    simpa only [raf, sub_zero, one_mul, zero_mul, add_zero,
      lookupAddressRight_eq_uninterleave] using rightRead.symm.trans right

/-- At RAF flag zero, the lookup selector chooses the interleaving of the two
encoded operands. This recovers the address without casting all 128 bits into
the field at once. -/
theorem instructionLookupRa_of_interleaved (t : Fin params.traceLength)
    (lhs rhs : BitVec 64) (raf : witness.InstructionRafFlag t = 0)
    (left : witness.LeftLookupOperand t = (lhs.toNat : F))
    (right : witness.RightLookupOperand t = (rhs.toNat : F)) :
    instructionLookupRa witness (TraceWitness.interleaveLookupOperands lhs rhs).toFin t = 1 := by
  obtain ⟨address, selected, _⟩ :=
    instructionLookupRa_unique charAbove2pow127 context equations t
  have decoded := uninterleave_of_lookup_operands charAbove2pow127 context equations
    t address selected lhs rhs raf left right
  have same := interleave_uninterleave address
  rw [decoded] at same
  simpa only [same] using selected

/-- The lookup output is the selected bytecode table evaluated at the recovered
interleaved operands. Padding and absent tables still give output zero. -/
theorem lookupOutput_of_interleaved (t : Fin params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK)) (selected : bytecodeRa witness slot t = 1)
    (lhs rhs : BitVec 64) (raf : witness.InstructionRafFlag t = 0)
    (left : witness.LeftLookupOperand t = (lhs.toNat : F))
    (right : witness.RightLookupOperand t = (rhs.toNat : F)) :
    witness.LookupOutput t =
      match (bytecodeRow context.bytecode slot.val).bind
          (fun row => JoltMetadata.lookupTable row.instruction) with
      | some table => lookupTableEntry table (TraceWitness.interleaveLookupOperands lhs rhs).toFin
      | none => 0 :=
  lookupOutput_of_selected_bytecode charAbove2pow127 context equations t slot selected
    (TraceWitness.interleaveLookupOperands lhs rhs).toFin
    (instructionLookupRa_of_interleaved charAbove2pow127 context equations t lhs rhs raf left right)

end JoltConstraints.Soundness
