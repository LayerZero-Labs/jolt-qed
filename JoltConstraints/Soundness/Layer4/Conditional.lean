import JoltConstraints.Soundness.Layer4.Interleaved
import JoltConstraints.Soundness.Layer4.ConditionalEntry

/-! Conditional, division-check and store-lane lookup outputs. -/

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

/-- ValidDiv0 evaluated on the two recovered operands. -/
theorem lookupOutput_validDiv0
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .ValidDiv0) :
    witness.LookupOutput t = (if lhs = 0 ∧ rhs ≠ -1 then 0 else 1) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact validDiv0_entry lhs rhs

/-- ValidUnsignedRemainder evaluated on the two recovered operands. -/
theorem lookupOutput_validUnsignedRemainder
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .ValidUnsignedRemainder) :
    witness.LookupOutput t = (if rhs = 0 ∨ lhs < rhs then 1 else 0) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact validUnsignedRemainder_entry lhs rhs

/-- SignMask evaluated on the two recovered operands. -/
theorem lookupOutput_signMask
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .SignMask) :
    witness.LookupOutput t = (((if lhs.msb then (-1 : BitVec 64) else 0).toNat : F)) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact signMask_entry lhs rhs

/-- VirtualNegateIf evaluated on the two recovered operands. -/
theorem lookupOutput_negateIf
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualNegateIf) :
    witness.LookupOutput t = (((if lhs.msb then -rhs else rhs).toNat : F)) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact negateIf_entry lhs rhs

/-- ShiftDataB evaluated on the two recovered operands. -/
theorem lookupOutput_shiftDataB
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .ShiftDataB) :
    witness.LookupOutput t = (((jolt_virtual_shift_data_b_value lhs rhs).toNat : F)) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact shiftDataB_entry lhs rhs

/-- ShiftDataH evaluated on the two recovered operands. -/
theorem lookupOutput_shiftDataH
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .ShiftDataH) :
    witness.LookupOutput t = (((jolt_virtual_shift_data_h_value lhs rhs).toNat : F)) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact shiftDataH_entry lhs rhs

/-- ShiftDataW evaluated on the two recovered operands. -/
theorem lookupOutput_shiftDataW
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .ShiftDataW) :
    witness.LookupOutput t = (((jolt_virtual_shift_data_w_value lhs rhs).toNat : F)) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact shiftDataW_entry lhs rhs

end JoltConstraints.Soundness
