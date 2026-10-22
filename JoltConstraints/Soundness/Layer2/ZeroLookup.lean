import JoltConstraints.Soundness.Layer1.InstructionReads

/-! The one lookup fact needed before the register induction: identity RAF
with right operand zero selects address zero, whose RangeCheck output is zero.
General lookup semantics remain a Layer 4 obligation. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

/-- The RangeCheck lookup output is zero when identity RAF has a zero right
operand. The stronger field bound forces the full address to zero by preventing
a nonzero address from casting to zero. -/
theorem lookupOutput_rangeCheck_zero
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (charAbove2pow128 : 2 ^ 128 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength)
    (raf : witness.InstructionRafFlag t = 1)
    (right : witness.RightLookupOperand t = 0)
    (tables : ∀ table, witness.LookupTableFlag table t =
      if table = .RangeCheck then 1 else 0) :
    witness.LookupOutput t = 0 := by
  have charAbove2pow127 : 2 ^ 127 < ringChar F := two_pow_127_lt_char charAbove2pow128
  obtain ⟨chosen, selected, _⟩ := instructionLookupRa_unique charAbove2pow127 context equations t
  have operand := rightLookupOperand_of_selected charAbove2pow127 context equations t chosen selected
  have castZero : (chosen.val : F) = (0 : Nat) := by
    simpa [raf, right] using operand.symm
  have chosenZero : chosen = 0 := Fin.ext
    (natCast_injective_below_char (lt_trans chosen.isLt charAbove2pow128)
      (by omega) castZero)
  have output := lookupOutput_of_selected charAbove2pow127 context equations t chosen selected
  simp_rw [tables] at output
  simpa [chosenZero, lookupTableEntry, rangeCheckTableEntry] using output

end JoltConstraints.Soundness
