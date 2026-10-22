import JoltConstraints.Soundness.Layer4.RangeCheck

/-! Recover the wide addition, biased subtraction, and multiplication addresses
from the arithmetic constraints. RangeCheck then returns their low 64 bits.
The inputs are arbitrary 64-bit words whose field encodings agree with the
instruction-input columns; Layer 5b must derive that agreement from its state.
The full address also feeds the W-operation and MULHU results in
WordArithmetic.lean. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

private theorem addWide_lt_two_pow_128 (lhs rhs : BitVec 64) :
    JoltISA.addWide lhs rhs < 2 ^ 128 := by
  have := lhs.isLt
  have := rhs.isLt
  unfold JoltISA.addWide
  omega

private theorem subWide_lt_two_pow_128 (lhs rhs : BitVec 64) :
    JoltISA.subWide lhs rhs < 2 ^ 128 := by
  have := lhs.isLt
  unfold JoltISA.subWide
  omega

private theorem mulWide_lt_two_pow_128 (lhs rhs : BitVec 64) :
    JoltISA.mulWide lhs rhs < 2 ^ 128 := by
  calc lhs.toNat * rhs.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' lhs.isLt rhs.isLt
    _ = 2 ^ 128 := by norm_num

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}

/-- Addition retains the carry into bit 64 in the right lookup operand. -/
theorem rightLookupOperand_add (addition : rightLookupAdd witness) (t : Fin params.traceLength)
    (active : witness.OpFlags .AddOperands t = 1) (lhs rhs : BitVec 64)
    (left : witness.LeftInstructionInput t = (lhs.toNat : F))
    (right : witness.RightInstructionInput t = (rhs.toNat : F)) :
    witness.RightLookupOperand t = ((BitVec.ofNat 128 (JoltISA.addWide lhs rhs)).toNat : F) := by
  have relation := addition t
  rw [active, one_mul, left, right] at relation
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (addWide_lt_two_pow_128 lhs rhs)]
  simp only [JoltISA.addWide, Nat.cast_add]
  simpa only [add_comm] using sub_eq_iff_eq_add.mp (sub_eq_zero.mp relation)

/-- Subtraction uses the nonnegative address `2^64 + lhs - rhs`, including
the `rhs = 0` case. Removing the bias happens only at the table lookup. -/
theorem rightLookupOperand_sub (subtraction : rightLookupSub witness) (t : Fin params.traceLength)
    (active : witness.OpFlags .SubtractOperands t = 1) (lhs rhs : BitVec 64)
    (left : witness.LeftInstructionInput t = (lhs.toNat : F))
    (right : witness.RightInstructionInput t = (rhs.toNat : F)) :
    witness.RightLookupOperand t = ((BitVec.ofNat 128 (JoltISA.subWide lhs rhs)).toNat : F) := by
  have relation := subtraction t
  rw [active, one_mul, left, right] at relation
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (subWide_lt_two_pow_128 lhs rhs)]
  simp only [JoltISA.subWide, Nat.cast_add, Nat.cast_sub (Nat.le_of_lt rhs.isLt),
    Nat.cast_pow, Nat.cast_ofNat]
  linear_combination relation

/-- Multiplication retains all 128 product bits in the right lookup operand. -/
theorem rightLookupOperand_mul (multiplication : rightLookupEqProductIfMul witness)
    (product : productEqLeftInputMulRightInput witness) (t : Fin params.traceLength)
    (active : witness.OpFlags .MultiplyOperands t = 1) (lhs rhs : BitVec 64)
    (left : witness.LeftInstructionInput t = (lhs.toNat : F))
    (right : witness.RightInstructionInput t = (rhs.toNat : F)) :
    witness.RightLookupOperand t = ((BitVec.ofNat 128 (JoltISA.mulWide lhs rhs)).toNat : F) := by
  have relation := multiplication t
  rw [active, one_mul, product t, left, right] at relation
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (mulWide_lt_two_pow_128 lhs rhs)]
  simpa only [JoltISA.mulWide, Nat.cast_mul] using sub_eq_zero.mp relation

variable {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include charAbove2pow128 context equations

/-- A RangeCheck addition cycle returns the wrapped 64-bit sum of its inputs. -/
theorem lookupOutput_rangeCheck_add (t : Fin params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK)) (selected : bytecodeRa witness slot t = 1)
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .RangeCheck)
    (active : witness.OpFlags .AddOperands t = 1) (lhs rhs : BitVec 64)
    (left : witness.LeftInstructionInput t = (lhs.toNat : F))
    (right : witness.RightInstructionInput t = (rhs.toNat : F)) :
    witness.LookupOutput t = ((lhs + rhs).toNat : F) := by
  have raf := instructionRafFlag_one_of_arithmetic (two_pow_127_lt_char charAbove2pow128)
    context equations t (Or.inl active)
  have output := lookupOutput_rangeCheck_of_identity charAbove2pow128 context equations
    t slot selected table _ raf (rightLookupOperand_add equations.rightLookupAdd t active lhs rhs left right)
  simpa only [BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128), JoltISA.addWide_low] using output

/-- A RangeCheck subtraction cycle returns the wrapped 64-bit difference. -/
theorem lookupOutput_rangeCheck_sub (t : Fin params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK)) (selected : bytecodeRa witness slot t = 1)
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .RangeCheck)
    (active : witness.OpFlags .SubtractOperands t = 1) (lhs rhs : BitVec 64)
    (left : witness.LeftInstructionInput t = (lhs.toNat : F))
    (right : witness.RightInstructionInput t = (rhs.toNat : F)) :
    witness.LookupOutput t = ((lhs - rhs).toNat : F) := by
  have raf := instructionRafFlag_one_of_arithmetic (two_pow_127_lt_char charAbove2pow128)
    context equations t (Or.inr (Or.inl active))
  have output := lookupOutput_rangeCheck_of_identity charAbove2pow128 context equations
    t slot selected table _ raf (rightLookupOperand_sub equations.rightLookupSub t active lhs rhs left right)
  simpa only [BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128), JoltISA.subWide_low] using output

/-- A RangeCheck multiplication cycle returns the wrapped 64-bit product. -/
theorem lookupOutput_rangeCheck_mul (t : Fin params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK)) (selected : bytecodeRa witness slot t = 1)
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .RangeCheck)
    (active : witness.OpFlags .MultiplyOperands t = 1) (lhs rhs : BitVec 64)
    (left : witness.LeftInstructionInput t = (lhs.toNat : F))
    (right : witness.RightInstructionInput t = (rhs.toNat : F)) :
    witness.LookupOutput t = ((lhs * rhs).toNat : F) := by
  have raf := instructionRafFlag_one_of_arithmetic (two_pow_127_lt_char charAbove2pow128)
    context equations t (Or.inr (Or.inr active))
  have output := lookupOutput_rangeCheck_of_identity charAbove2pow128 context equations
    t slot selected table _ raf (rightLookupOperand_mul equations.rightLookupEqProductIfMul
      equations.productEqLeftInputMulRightInput t active lhs rhs left right)
  simpa only [BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128), JoltISA.mulWide_low] using output

end JoltConstraints.Soundness
