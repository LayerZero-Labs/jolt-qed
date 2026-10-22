import JoltConstraints.Soundness.Layer4.Arithmetic
import JoltConstraints.Soundness.Layer4.Word

/-! Word arithmetic and high-product results from the recovered wide addresses. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  (t : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
  (selected : bytecodeRa witness slot t = 1)

include charAbove2pow128 context equations selected

/-- A SignExtendWord add cycle returns the signed low 32-bit result. -/
theorem lookupOutput_signExtendWord_add
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .SignExtendWord)
    (active : witness.OpFlags .AddOperands t = 1) (lhs rhs : BitVec 64)
    (left : witness.LeftInstructionInput t = (lhs.toNat : F))
    (right : witness.RightInstructionInput t = (rhs.toNat : F)) :
    witness.LookupOutput t = ((((lhs + rhs).setWidth 32).signExtend 64).toNat : F) := by
  have raf := instructionRafFlag_one_of_arithmetic (two_pow_127_lt_char charAbove2pow128)
    context equations t (Or.inl active)
  have output := lookupOutput_signExtendWord_of_identity charAbove2pow128 context equations
    t slot selected _ raf (rightLookupOperand_add equations.rightLookupAdd
      t active lhs rhs left right) table
  have low : (BitVec.ofNat 128 (JoltISA.addWide lhs rhs)).setWidth 64 = lhs + rhs := by
    rw [BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128), JoltISA.addWide_low]
  rw [← BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), low] at output
  exact output

/-- A SignExtendWord sub cycle returns the signed low 32-bit result. -/
theorem lookupOutput_signExtendWord_sub
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .SignExtendWord)
    (active : witness.OpFlags .SubtractOperands t = 1) (lhs rhs : BitVec 64)
    (left : witness.LeftInstructionInput t = (lhs.toNat : F))
    (right : witness.RightInstructionInput t = (rhs.toNat : F)) :
    witness.LookupOutput t = ((((lhs - rhs).setWidth 32).signExtend 64).toNat : F) := by
  have raf := instructionRafFlag_one_of_arithmetic (two_pow_127_lt_char charAbove2pow128)
    context equations t (Or.inr (Or.inl active))
  have output := lookupOutput_signExtendWord_of_identity charAbove2pow128 context equations
    t slot selected _ raf (rightLookupOperand_sub equations.rightLookupSub
      t active lhs rhs left right) table
  have low : (BitVec.ofNat 128 (JoltISA.subWide lhs rhs)).setWidth 64 = lhs - rhs := by
    rw [BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128), JoltISA.subWide_low]
  rw [← BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), low] at output
  exact output

/-- A SignExtendWord mul cycle returns the signed low 32-bit result. -/
theorem lookupOutput_signExtendWord_mul
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .SignExtendWord)
    (active : witness.OpFlags .MultiplyOperands t = 1) (lhs rhs : BitVec 64)
    (left : witness.LeftInstructionInput t = (lhs.toNat : F))
    (right : witness.RightInstructionInput t = (rhs.toNat : F)) :
    witness.LookupOutput t = ((((lhs * rhs).setWidth 32).signExtend 64).toNat : F) := by
  have raf := instructionRafFlag_one_of_arithmetic (two_pow_127_lt_char charAbove2pow128)
    context equations t (Or.inr (Or.inr active))
  have output := lookupOutput_signExtendWord_of_identity charAbove2pow128 context equations
    t slot selected _ raf (rightLookupOperand_mul equations.rightLookupEqProductIfMul equations.productEqLeftInputMulRightInput
      t active lhs rhs left right) table
  have low : (BitVec.ofNat 128 (JoltISA.mulWide lhs rhs)).setWidth 64 = lhs * rhs := by
    rw [BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128), JoltISA.mulWide_low]
  rw [← BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), low] at output
  exact output

/-- UpperWord multiplication returns the high 64 bits of the full product. -/
theorem lookupOutput_upperWord_mul
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .UpperWord)
    (active : witness.OpFlags .MultiplyOperands t = 1) (lhs rhs : BitVec 64)
    (left : witness.LeftInstructionInput t = (lhs.toNat : F))
    (right : witness.RightInstructionInput t = (rhs.toNat : F)) :
    witness.LookupOutput t = ((BitVec.ofNat 64 (lhs.toNat * rhs.toNat / 2 ^ 64)).toNat : F) := by
  have raf := instructionRafFlag_one_of_arithmetic (two_pow_127_lt_char charAbove2pow128)
    context equations t (Or.inr (Or.inr active))
  have output := lookupOutput_upperWord_of_identity charAbove2pow128 context equations
    t slot selected _ raf (rightLookupOperand_mul equations.rightLookupEqProductIfMul
      equations.productEqLeftInputMulRightInput t active lhs rhs left right) table
  have bound : lhs.toNat * rhs.toNat < 2 ^ 128 := by
    calc lhs.toNat * rhs.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' lhs.isLt rhs.isLt
         _ = 2 ^ 128 := by norm_num
  simpa only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    JoltISA.mulWide, Nat.mod_eq_of_lt bound, Nat.shiftRight_eq_div_pow] using output

end JoltConstraints.Soundness
