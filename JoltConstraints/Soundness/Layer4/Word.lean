import JoltConstraints.Soundness.Layer4.Identity
import JoltConstraints.Soundness.Layer4.WordEntry

/-! Identity-RAF table outputs: word slices, sign extension, powers and masks.
The wide address is retained until each table performs its own truncation. -/

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

/-- SignExtendWord sign-extends the low 32 bits. -/
theorem lookupOutput_signExtendWord_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .SignExtendWord) :
    witness.LookupOutput t = (((value.setWidth 32).signExtend 64).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  exact signExtendWord_entry value

/-- LowerHalfWord zero-extends the low 32 bits. -/
theorem lookupOutput_lowerHalfWord_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .LowerHalfWord) :
    witness.LookupOutput t = (((value.setWidth 32).setWidth 64).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  exact lowerHalfWord_entry value

/-- UpperWord returns the high 64 bits. -/
theorem lookupOutput_upperWord_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .UpperWord) :
    witness.LookupOutput t = (((value >>> 64).setWidth 64).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  rfl

/-- RangeCheckAligned clears the low address bit. -/
theorem lookupOutput_rangeCheckAligned_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .RangeCheckAligned) :
    witness.LookupOutput t = ((value.setWidth 64 &&& ~~~1#64).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  exact rangeCheckAligned_entry value

/-- AlignAddr clears the low three address bits. -/
theorem lookupOutput_alignAddr_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .AlignAddr) :
    witness.LookupOutput t = ((value.setWidth 64 &&& ~~~7#64).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  exact alignAddr_entry value

/-- Pow2 produces one set bit at the index modulo 64. -/
theorem lookupOutput_pow2_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .Pow2) :
    witness.LookupOutput t = ((BitVec.ofNat 64 (2 ^ (value.toNat % 64))).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  exact pow2_entry value

/-- Pow2W produces one set bit at the index modulo 32. -/
theorem lookupOutput_pow2W_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .Pow2W) :
    witness.LookupOutput t = ((BitVec.ofNat 64 (2 ^ (value.toNat % 32))).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  exact pow2W_entry value

/-- ShiftRightBitmask sets bits from the shift through bit 63. -/
theorem lookupOutput_shiftRightBitmask_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .ShiftRightBitmask) :
    witness.LookupOutput t = ((BitVec.ofNat 64 (((1 <<< (64 - value.toNat % 64)) - 1) <<< (value.toNat % 64))).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  exact shiftRightBitmask_entry value

/-- ShiftRightBitmaskW sets bits from the shift through bit 31. -/
theorem lookupOutput_shiftRightBitmaskW_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .ShiftRightBitmaskW) :
    witness.LookupOutput t = ((BitVec.ofNat 64 (2 ^ 32 - 2 ^ (value.toNat % 32))).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  exact shiftRightBitmaskW_entry value

/-- VirtualRev8W reverses the bytes within each 32-bit half. -/
theorem lookupOutput_rev8w_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualRev8W) :
    witness.LookupOutput t = ((rev8w (value.setWidth 64)).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  rfl

/-- WindowMaskB selects one byte lane. -/
theorem lookupOutput_windowMaskB_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .WindowMaskB) :
    witness.LookupOutput t = ((0xFF#64 <<< (8 * (value &&& 7).toNat)).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  rfl

/-- WindowMaskH selects one aligned halfword lane. -/
theorem lookupOutput_windowMaskH_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .WindowMaskH) :
    witness.LookupOutput t = ((0xFFFF#64 <<< (8 * (value &&& 6).toNat)).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  rfl

/-- WindowMaskW selects one aligned 32-bit lane. -/
theorem lookupOutput_windowMaskW_of_identity
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .WindowMaskW) :
    witness.LookupOutput t = ((0xFFFF_FFFF#64 <<< (32 * ((value >>> 2) &&& 1).toNat)).toNat : F) := by
  rw [lookupOutput_of_identity charAbove2pow128 context equations
    t slot selected value raf encoded, table]
  rfl

end JoltConstraints.Soundness
