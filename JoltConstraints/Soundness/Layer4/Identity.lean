import JoltConstraints.Soundness.Layer4.Table

open LeanRV64D

/-! Recover a full 128-bit lookup address from its field encoding when the
instruction uses identity RAF. This is where the field bound of `JoltField` and,
below characteristic `2^128`, Akita's canonical-address check (63) are needed. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

/-- An add row's lookup index, at most `2^65 - 2`, lies below `2^128 - 2^64`. -/
theorem addWideIndex_lt (lhs rhs : BitVec 64) :
    (BitVec.ofNat 128 (JoltISA.addWide lhs rhs)).toNat < 2 ^ 128 - 2 ^ 64 := by
  have := lhs.isLt
  have := rhs.isLt
  rw [BitVec.toNat_ofNat]
  unfold JoltISA.addWide
  omega

/-- A sub row's lookup index, at most `2^65 - 1`, lies below `2^128 - 2^64`. -/
theorem subWideIndex_lt (lhs rhs : BitVec 64) :
    (BitVec.ofNat 128 (JoltISA.subWide lhs rhs)).toNat < 2 ^ 128 - 2 ^ 64 := by
  have := lhs.isLt
  rw [BitVec.toNat_ofNat]
  unfold JoltISA.subWide
  omega

/-- A mul row's lookup index, at most `(2^64 - 1)^2 = 2^128 - 2^65 + 1`, lies
below `2^128 - 2^64`. -/
theorem mulWideIndex_lt (lhs rhs : BitVec 64) :
    (BitVec.ofNat 128 (JoltISA.mulWide lhs rhs)).toNat < 2 ^ 128 - 2 ^ 64 := by
  have lhsLe : lhs.toNat ≤ 2 ^ 64 - 1 := by have := lhs.isLt; omega
  have rhsLe : rhs.toNat ≤ 2 ^ 64 - 1 := by have := rhs.isLt; omega
  have product : lhs.toNat * rhs.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul lhsLe rhsLe
  rw [BitVec.toNat_ofNat]
  unfold JoltISA.mulWide
  exact lt_of_le_of_lt (Nat.mod_le _ _) (lt_of_le_of_lt product (by norm_num))

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128Minus2pow64 : 2 ^ 128 - 2 ^ 64 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include charAbove2pow128Minus2pow64 context equations

/-- Identity RAF selects the given 128-bit value when the right lookup operand
encodes it and the value lies below `2^128 - 2^64`. Both the value and the
selected address (`identityAddress_lt_char`) lie below the characteristic, so
equality in the field gives equality of addresses.
The bound on the value is needed: with Akita's `p = 2^128 - 1780711455`, the
value `p + 5` encodes the same field element as 5, and the selected address is 5. -/
theorem instructionLookupRa_of_identity (t : Fin params.traceLength) (value : BitVec 128)
    (raf : witness.InstructionRafFlag t = 1)
    (encoded : witness.RightLookupOperand t = (value.toNat : F))
    (valueBelow : value.toNat < 2 ^ 128 - 2 ^ 64) :
    instructionLookupRa witness value.toFin t = 1 := by
  have charAbove2pow127 := two_pow_127_lt_char charAbove2pow128Minus2pow64
  obtain ⟨chosen, selected, _⟩ := instructionLookupRa_unique charAbove2pow127 context equations t
  have operand := rightLookupOperand_of_selected charAbove2pow127 context equations t chosen selected
  have same : (chosen.val : F) = (value.toNat : F) := by
    simpa [raf, encoded] using operand.symm
  have address : chosen = value.toFin := Fin.ext
    (natCast_injective_below_char
      (identityAddress_lt_char charAbove2pow128Minus2pow64 context equations t chosen selected raf)
      (lt_trans valueBelow charAbove2pow128Minus2pow64) same)
  simpa only [address] using selected

/-- At identity RAF, the lookup output is the selected bytecode table evaluated
at the recovered 128-bit value. The operand encoding is a local obligation for
the instruction proof, not a premise of the soundness theorem. -/
theorem lookupOutput_of_identity (t : Fin params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK)) (selected : bytecodeRa witness slot t = 1)
    (value : BitVec 128) (raf : witness.InstructionRafFlag t = 1)
    (encoded : witness.RightLookupOperand t = (value.toNat : F))
    (valueBelow : value.toNat < 2 ^ 128 - 2 ^ 64) :
    witness.LookupOutput t =
      match (bytecodeRow context.bytecode slot.val).bind
          (fun row => JoltMetadata.lookupTable row.instruction) with
      | some table => lookupTableEntry table value.toFin
      | none => 0 :=
  lookupOutput_of_selected_bytecode (two_pow_127_lt_char charAbove2pow128Minus2pow64)
    context equations t slot selected value.toFin
    (instructionLookupRa_of_identity charAbove2pow128Minus2pow64 context equations t value raf encoded
      valueBelow)

end JoltConstraints.Soundness
