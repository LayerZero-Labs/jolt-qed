import JoltConstraints.Soundness.Layer4.Identity

open LeanRV64D

/-! Product-bound assertions at a recovered wide address. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow128 : 2 ^ 128 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  (t : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
  (selected : bytecodeRa witness slot t = 1)
  (value : BitVec 128) (raf : witness.InstructionRafFlag t = 1)
  (encoded : witness.RightLookupOperand t = (value.toNat : F))

include charAbove2pow128 context equations selected raf encoded

/-- MulUNoOverflow tests that the recovered wide product fits in 64 bits. -/
theorem lookupOutput_mulUNoOverflow_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .MulUNoOverflow) :
    witness.LookupOutput t = (if value.toNat < 2 ^ 64 then 1 else 0) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  simp [lookupTableEntry, mulUNoOverflowTableEntry, ← BitVec.toNat_inj,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff]

end JoltConstraints.Soundness
