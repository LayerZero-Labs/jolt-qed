import JoltConstraints.Soundness.Layer4.Table

/-! Recover a full 128-bit lookup address from its field encoding when the
instruction uses identity RAF. This is where the stronger field bound is needed. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include charAbove2pow128 context equations

/-- Identity RAF selects the given 128-bit value when the right lookup operand
encodes it. Both addresses lie below the characteristic, so equality in the
field gives equality of addresses. -/
theorem instructionLookupRa_of_identity (t : Fin params.traceLength) (value : BitVec 128)
    (raf : witness.InstructionRafFlag t = 1)
    (encoded : witness.RightLookupOperand t = (value.toNat : F)) :
    instructionLookupRa witness value.toFin t = 1 := by
  have charAbove2pow127 := two_pow_127_lt_char charAbove2pow128
  obtain ⟨chosen, selected, _⟩ := instructionLookupRa_unique charAbove2pow127 context equations t
  have operand := rightLookupOperand_of_selected charAbove2pow127 context equations t chosen selected
  have same : (chosen.val : F) = (value.toNat : F) := by
    simpa [raf, encoded] using operand.symm
  have address : chosen = value.toFin := Fin.ext
    (natCast_injective_below_char (lt_trans chosen.isLt charAbove2pow128)
      (lt_trans value.isLt charAbove2pow128) same)
  simpa only [address] using selected

/-- At identity RAF, the lookup output is the selected bytecode table evaluated
at the recovered 128-bit value. The operand encoding is a local obligation for
the instruction proof, not a premise of the soundness theorem. -/
theorem lookupOutput_of_identity (t : Fin params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK)) (selected : bytecodeRa witness slot t = 1)
    (value : BitVec 128) (raf : witness.InstructionRafFlag t = 1)
    (encoded : witness.RightLookupOperand t = (value.toNat : F)) :
    witness.LookupOutput t =
      match (bytecodeRow context.bytecode slot.val).bind
          (fun row => JoltMetadata.lookupTable row.instruction) with
      | some table => lookupTableEntry table value.toFin
      | none => 0 :=
  lookupOutput_of_selected_bytecode (two_pow_127_lt_char charAbove2pow128)
    context equations t slot selected value.toFin
    (instructionLookupRa_of_identity charAbove2pow128 context equations t value raf encoded)

end JoltConstraints.Soundness
