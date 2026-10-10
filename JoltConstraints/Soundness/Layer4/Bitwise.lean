import JoltConstraints.Soundness.Layer4.Interleaved
import JoltConstraints.Soundness.Layer4.BitwiseEntry

/-! Interpret bitwise lookup outputs at the recovered operands.
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

/-- The AND table returns its operation on the two recovered words. -/
theorem lookupOutput_and
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .And) :
    witness.LookupOutput t = (((lhs &&& rhs).toNat : F)) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact and_entry lhs rhs

/-- The OR table returns its operation on the two recovered words. -/
theorem lookupOutput_or
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .Or) :
    witness.LookupOutput t = (((lhs ||| rhs).toNat : F)) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact or_entry lhs rhs

/-- The XOR table returns its operation on the two recovered words. -/
theorem lookupOutput_xor
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .Xor) :
    witness.LookupOutput t = (((lhs ^^^ rhs).toNat : F)) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact xor_entry lhs rhs

/-- The AND with the right operand complemented table returns its operation on the two recovered words. -/
theorem lookupOutput_andn
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .Andn) :
    witness.LookupOutput t = (((lhs &&& ~~~rhs).toNat : F)) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact andn_entry lhs rhs

end JoltConstraints.Soundness
