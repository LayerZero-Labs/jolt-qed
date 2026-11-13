import JoltConstraints.Soundness.Layer4.Identity
import JoltConstraints.Soundness.Layer4.RangeCheckEntry

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints.Soundness

/-- When the selected instruction uses RangeCheck and identity RAF, its lookup
output is the low 64 bits of the recovered address. -/
theorem lookupOutput_rangeCheck_of_identity
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (charAbove2pow128Minus2pow64 : 2 ^ 128 - 2 ^ 64 < ringChar F)
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (t : Fin params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK)) (selected : bytecodeRa witness slot t = 1)
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .RangeCheck)
    (value : BitVec 128) (raf : witness.InstructionRafFlag t = 1)
    (encoded : witness.RightLookupOperand t = (value.toNat : F))
    (valueBelow : value.toNat < 2 ^ 128 - 2 ^ 64) :
    witness.LookupOutput t = ((value.setWidth 64).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128Minus2pow64 context equations t slot selected value raf encoded
      valueBelow,
    table]
  exact rangeCheck_entry value

end JoltConstraints.Soundness
