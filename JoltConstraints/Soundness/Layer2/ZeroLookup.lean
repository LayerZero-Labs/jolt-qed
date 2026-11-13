import JoltConstraints.Soundness.Layer1.InstructionReads

open LeanRV64D

/-! The one lookup fact needed before the register induction: identity RAF
with right operand zero selects address zero, whose RangeCheck output is zero.
General lookup semantics remain a Layer 4 obligation. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

open scoped BigOperators

/-- The RangeCheck lookup output is zero when identity RAF has a zero right
operand. The selected address lies below the characteristic
(`identityAddress_lt_char`), so it casts to zero only if it is zero. -/
theorem lookupOutput_rangeCheck_zero
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (charAbove2pow128Minus2pow64 : 2 ^ 128 - 2 ^ 64 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength)
    (raf : witness.InstructionRafFlag t = 1)
    (right : witness.RightLookupOperand t = 0)
    (tables : ∀ table, witness.LookupTableFlag table t =
      if table = .RangeCheck then 1 else 0) :
    witness.LookupOutput t = 0 := by
  have charAbove2pow127 : 2 ^ 127 < ringChar F := two_pow_127_lt_char charAbove2pow128Minus2pow64
  obtain ⟨chosen, selected, _⟩ := instructionLookupRa_unique charAbove2pow127 context equations t
  have operand := rightLookupOperand_of_selected charAbove2pow127 context equations t chosen selected
  have castZero : (chosen.val : F) = (0 : Nat) := by
    simpa [raf, right] using operand.symm
  have chosenZero : chosen = 0 := Fin.ext
    (natCast_injective_below_char
      (identityAddress_lt_char charAbove2pow128Minus2pow64 context equations t chosen selected raf)
      (lt_trans (by simp) charAbove2pow128Minus2pow64) castZero)
  have output := lookupOutput_of_selected charAbove2pow127 context equations t chosen selected
  simp_rw [tables] at output
  simpa [chosenZero, lookupTableEntry, rangeCheckTableEntry] using output

end JoltConstraints.Soundness
