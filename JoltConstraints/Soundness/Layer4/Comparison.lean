import JoltConstraints.Soundness.Layer4.Interleaved
import JoltConstraints.Soundness.Layer4.ComparisonEntry

/-! Interpret comparison lookup outputs at the recovered operands.
The selected bytecode row supplies the table. RAF zero and operand agreement
are local obligations for the instruction proofs. -/

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

/-- The equality table returns its operation on the two recovered words. -/
theorem lookupOutput_equal
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .Equal) :
    witness.LookupOutput t = (if lhs = rhs then 1 else 0) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact equal_entry lhs rhs

/-- The inequality table returns its operation on the two recovered words. -/
theorem lookupOutput_notEqual
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .NotEqual) :
    witness.LookupOutput t = (if lhs ≠ rhs then 1 else 0) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact notEqual_entry lhs rhs

/-- The unsigned less-than table returns its operation on the two recovered words. -/
theorem lookupOutput_unsignedLessThan
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .UnsignedLessThan) :
    witness.LookupOutput t = (if lhs < rhs then 1 else 0) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact unsignedLessThan_entry lhs rhs

/-- The unsigned less-than-or-equal table returns its operation on the two recovered words. -/
theorem lookupOutput_unsignedLessThanEqual
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .UnsignedLessThanEqual) :
    witness.LookupOutput t = (if lhs ≤ rhs then 1 else 0) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact unsignedLessThanEqual_entry lhs rhs

/-- The unsigned greater-than-or-equal table returns its operation on the two recovered words. -/
theorem lookupOutput_unsignedGreaterThanEqual
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .UnsignedGreaterThanEqual) :
    witness.LookupOutput t = (if lhs ≥ rhs then 1 else 0) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact unsignedGreaterThanEqual_entry lhs rhs

/-- The signed less-than table returns its operation on the two recovered words. -/
theorem lookupOutput_signedLessThan
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .SignedLessThan) :
    witness.LookupOutput t = (if lhs.toInt < rhs.toInt then 1 else 0) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact signedLessThan_entry lhs rhs

/-- The signed greater-than-or-equal table returns its operation on the two recovered words. -/
theorem lookupOutput_signedGreaterThanEqual
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .SignedGreaterThanEqual) :
    witness.LookupOutput t = (if lhs.toInt ≥ rhs.toInt then 1 else 0) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact signedGreaterThanEqual_entry lhs rhs

end JoltConstraints.Soundness
