import JoltConstraints.Soundness.Layer4.Interleaved
import JoltConstraints.Soundness.Layer4.ShiftEntry

/-! Shift lookup outputs on right-shift masks. Mask shape is a local obligation
for the expansion proof; no executed trace is assumed here. -/

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

/-- VirtualSRL returns the shift specified by its right-shift mask. -/
theorem lookupOutput_srl
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualSRL)
    (shift : Nat)
    (mask : ∀ i < 64, rhs.getLsbD i = decide (shift ≤ i)) :
    witness.LookupOutput t = ((lhs >>> shift).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact ShiftTables.srl_entry _ lhs rhs (uninterleave_interleave lhs rhs) shift mask

/-- VirtualSRA returns the shift specified by its right-shift mask. -/
theorem lookupOutput_sra
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualSRA)
    (shift : Nat) (shiftLt : shift < 64)
    (mask : ∀ i < 64, rhs.getLsbD i = decide (shift ≤ i)) :
    witness.LookupOutput t = ((lhs.sshiftRight shift).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact ShiftTables.sra_entry _ lhs rhs (uninterleave_interleave lhs rhs) shift shiftLt mask

/-- VirtualSRLW returns the shift specified by its right-shift mask. -/
theorem lookupOutput_srlw
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualSRLW)
    (shift : Nat) (shiftLt : shift < 32)
    (mask : ∀ i < 32, rhs.getLsbD i = decide (shift ≤ i)) :
    witness.LookupOutput t = (((lhs.setWidth 32 >>> shift).signExtend 64).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact ShiftTables.srlw_entry _ lhs rhs (uninterleave_interleave lhs rhs) shift shiftLt mask

/-- VirtualSRAW returns the shift specified by its right-shift mask. -/
theorem lookupOutput_sraw
    (table : (bytecodeRow context.bytecode slot.val).bind
      (fun row => JoltMetadata.lookupTable row.instruction) = some .VirtualSRAW)
    (shift : Nat) (shiftLt : shift < 32)
    (mask : ∀ i < 32, rhs.getLsbD i = decide (shift ≤ i)) :
    witness.LookupOutput t = ((((lhs.setWidth 32).sshiftRight shift).signExtend 64).toNat : F) := by
  rw [lookupOutput_of_interleaved charAbove2pow127 context equations
    t slot selected lhs rhs raf left right, table]
  exact ShiftTables.sraw_entry _ lhs rhs (uninterleave_interleave lhs rhs) shift shiftLt mask

end JoltConstraints.Soundness
