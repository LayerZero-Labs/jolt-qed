import JoltConstraints.Soundness.Layer4.Interleaved
import JoltConstraints.Soundness.Layer4.PextEntry

/-! Extraction lookup outputs on arbitrary source words and masks. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
  (t : Fin params.traceLength) (slot : Fin (2 ^ params.logBytecodeK))
  (selected : bytecodeRa witness slot t = 1)
  (lhs rhs : BitVec 64) (raf : witness.InstructionRafFlag t = 0)
  (left : witness.LeftLookupOperand t = (lhs.toNat : F))
  (right : witness.RightLookupOperand t = (rhs.toNat : F))

include charAbove2pow127 context equations selected raf left right

/-- Pext returns the instruction's bit-extraction value. -/
theorem lookupOutput_pext
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .Pext) :
    witness.LookupOutput t = ((jolt_virtual_pext_value lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  simp only [lookupTableEntry, pextTableEntry, uninterleave_interleave, pext_eq_jolt_virtual_pext_value]

/-- PextSigned returns the instruction's bit-extraction value. -/
theorem lookupOutput_pextSigned
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .PextSigned) :
    witness.LookupOutput t = ((jolt_virtual_pext_signed_value lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  simp only [lookupTableEntry, pextSignedTableEntry, uninterleave_interleave, pextSigned_eq_jolt_virtual_pext_signed_value]

end JoltConstraints.Soundness
