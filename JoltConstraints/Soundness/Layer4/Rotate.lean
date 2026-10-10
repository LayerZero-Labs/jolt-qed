import JoltConstraints.Soundness.Layer4.Interleaved
import JoltConstraints.Soundness.Layer4.RotateEntry

/-! XOR-rotation lookup outputs, including the 32-bit variants. -/

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

/-- XORs the left word with the right word rotated left once. -/
theorem lookupOutput_xorRotL1
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualXORROTL1) :
    witness.LookupOutput t = ((jolt_virtual_xorrotl1_value lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact xorRotL1_entry lhs rhs

/-- Rotates the XOR of both words right by 32 bits. -/
theorem lookupOutput_xorRot32
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualXORROT32) :
    witness.LookupOutput t = ((jolt_virtual_xorrot_value 32 lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact xorRot_entry 32 (by decide) lhs rhs

/-- Rotates the XOR of both words right by 24 bits. -/
theorem lookupOutput_xorRot24
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualXORROT24) :
    witness.LookupOutput t = ((jolt_virtual_xorrot_value 24 lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact xorRot_entry 24 (by decide) lhs rhs

/-- Rotates the XOR of both words right by 16 bits. -/
theorem lookupOutput_xorRot16
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualXORROT16) :
    witness.LookupOutput t = ((jolt_virtual_xorrot_value 16 lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact xorRot_entry 16 (by decide) lhs rhs

/-- Rotates the XOR of both words right by 63 bits. -/
theorem lookupOutput_xorRot63
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualXORROT63) :
    witness.LookupOutput t = ((jolt_virtual_xorrot_value 63 lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact xorRot_entry 63 (by decide) lhs rhs

/-- Rotates the XOR of the low 32-bit words right by 16 bits, then zero-extends. -/
theorem lookupOutput_xorRotW16
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualXORROTW16) :
    witness.LookupOutput t = ((jolt_virtual_xorrotw_value 16 lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact xorRotW_entry 16 (by decide) lhs rhs

/-- Rotates the XOR of the low 32-bit words right by 12 bits, then zero-extends. -/
theorem lookupOutput_xorRotW12
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualXORROTW12) :
    witness.LookupOutput t = ((jolt_virtual_xorrotw_value 12 lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact xorRotW_entry 12 (by decide) lhs rhs

/-- Rotates the XOR of the low 32-bit words right by 8 bits, then zero-extends. -/
theorem lookupOutput_xorRotW8
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualXORROTW8) :
    witness.LookupOutput t = ((jolt_virtual_xorrotw_value 8 lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact xorRotW_entry 8 (by decide) lhs rhs

/-- Rotates the XOR of the low 32-bit words right by 7 bits, then zero-extends. -/
theorem lookupOutput_xorRotW7
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualXORROTW7) :
    witness.LookupOutput t = ((jolt_virtual_xorrotw_value 7 lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact xorRotW_entry 7 (by decide) lhs rhs

/-- Rotates the XOR of the low 32-bit words right by 22 bits, then zero-extends. -/
theorem lookupOutput_xorRotW22
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualXORROTW22) :
    witness.LookupOutput t = ((jolt_virtual_xorrotw_value 22 lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact xorRotW_entry 22 (by decide) lhs rhs

/-- Rotates the XOR of the low 32-bit words right by 19 bits, then zero-extends. -/
theorem lookupOutput_xorRotW19
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualXORROTW19) :
    witness.LookupOutput t = ((jolt_virtual_xorrotw_value 19 lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact xorRotW_entry 19 (by decide) lhs rhs

/-- Rotates the XOR of the low 32-bit words right by 6 bits, then zero-extends. -/
theorem lookupOutput_xorRotW6
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualXORROTW6) :
    witness.LookupOutput t = ((jolt_virtual_xorrotw_value 6 lhs rhs).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact xorRotW_entry 6 (by decide) lhs rhs

end JoltConstraints.Soundness
