import JoltConstraints.Soundness.Layer1.BytecodeReads
import JoltConstraints.trace_interface

/-! Recover selected bytecode slots across the initial and interior cycles.
The field PC is converted back to a slot index using the verifier's domain
bound; no execution-state or theorem premise is added. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
  {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include charAbove2pow127 context equations

/-- The first witness cycle selects exactly the preprocessed entry slot. This
also handles entry address zero, which maps to padding slot zero. -/
theorem selected_entry (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot
      ⟨0, pow_pos (by decide : 0 < (2 : Nat)) _⟩ = 1) :
    slot = context.entry :=
  bytecodeRa_at_most_one charAbove2pow127 context equations _ _ _ selected
    equations.bytecodeRaAtEntryEqOne

/-- A nonlast virtual row advances the expanded bytecode slot by exactly one.
The next slot is derived from the witness's unique selector, not assumed. -/
theorem selected_next_of_nonlast_virtual
    (t : Fin params.traceLength) (next : t.val + 1 < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1)
    (virtual : witness.OpFlags .VirtualInstruction t = 1)
    (nonlast : witness.OpFlags .IsLastInSequence t = 0) :
    ∃ nextSlot : Fin (2 ^ params.logBytecodeK),
      bytecodeRa witness nextSlot ⟨t.val + 1, next⟩ = 1 ∧
      nextSlot.val = slot.val + 1 := by
  obtain ⟨nextSlot, nextSelected, _⟩ :=
    bytecodeRa_unique charAbove2pow127 context equations ⟨t.val + 1, next⟩
  have increment : witness.NextPC t = witness.PC t + 1 := by
    have relation := equations.nextPCEqPCPlusOneIfInline t
    rw [virtual, nonlast] at relation
    linear_combination relation
  have shifted : witness.NextPC t = witness.PC ⟨t.val + 1, next⟩ := by
    simpa only [nextPCEqShift, dif_pos next] using equations.nextPCEqShift t
  have oldPC := pc_of_selected_bytecode charAbove2pow127 context equations t slot selected
  have newPC := pc_of_selected_bytecode charAbove2pow127 context equations
    ⟨t.val + 1, next⟩ nextSlot nextSelected
  have same : ((slot.val + 1 : Nat) : F) = (nextSlot.val : F) := by
    calc
      ((slot.val + 1 : Nat) : F) = witness.PC t + 1 := by
        rw [Nat.cast_add, Nat.cast_one, oldPC]
      _ = witness.NextPC t := increment.symm
      _ = witness.PC ⟨t.val + 1, next⟩ := shifted
      _ = (nextSlot.val : F) := newPC
  have domain : 2 ^ params.logBytecodeK ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide : 0 < 2) params.logBytecodeK_lt_usizeBits.le
  have oldBound : slot.val + 1 < ringChar F := by omega
  have newBound : nextSlot.val < ringChar F := by omega
  refine ⟨nextSlot, nextSelected, ?_⟩
  exact (natCast_injective_below_char oldBound newBound same).symm

/-- The selected row's sequence stamp provides the nonlast virtual flags.
This is the form the execution-prefix induction will use. -/
theorem selected_next_of_remaining
    (t : Fin params.traceLength) (next : t.val + 1 < params.traceLength)
    (slot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1)
    {row : JoltInstructionRow}
    (rowIs : bytecodeRow context.bytecode slot.val = some row)
    (remaining : row.virtual_sequence_remaining.getD 0 ≠ 0) :
    ∃ nextSlot : Fin (2 ^ params.logBytecodeK),
      bytecodeRa witness nextSlot ⟨t.val + 1, next⟩ = 1 ∧
      nextSlot.val = slot.val + 1 := by
  have virtual : witness.OpFlags .VirtualInstruction t = 1 := by
    rw [opFlag_of_selected_bytecode charAbove2pow127 context equations
      .VirtualInstruction t slot selected]
    simp only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag]
    have some : row.virtual_sequence_remaining.isSome = true := by
      cases h : row.virtual_sequence_remaining with
      | none => simp only [h, Option.getD_none] at remaining; exact False.elim (remaining rfl)
      | some n => rfl
    simp only [some, ↓reduceIte]
  have nonlast : witness.OpFlags .IsLastInSequence t = 0 := by
    rw [opFlag_of_selected_bytecode charAbove2pow127 context equations
      .IsLastInSequence t slot selected]
    simp only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag]
    have notLast : row.virtual_sequence_remaining ≠ some 0 := by
      intro h
      rw [h] at remaining
      exact remaining rfl
    simp only [beq_iff_eq, notLast, ↓reduceIte]
  exact selected_next_of_nonlast_virtual charAbove2pow127 context equations
    t next slot selected virtual nonlast

/-- If the next selected row is interior to an expansion and the current slot
is a real row, the current row must be its immediate predecessor. The real-row
condition excludes padding, which also sets `DoNotUpdateUnexpandedPC`. -/
theorem selected_interior_predecessor
    (t : Fin params.traceLength) (next : t.val + 1 < params.traceLength)
    (slot nextSlot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1)
    (nextSelected : bytecodeRa witness nextSlot ⟨t.val + 1, next⟩ = 1)
    {row nextRow : JoltInstructionRow}
    (rowIs : bytecodeRow context.bytecode slot.val = some row)
    (nextRowIs : bytecodeRow context.bytecode nextSlot.val = some nextRow)
    (interior : nextRow.starts_source = false) :
    nextSlot.val = slot.val + 1 := by
  have interiorFlags : nextRow.virtual_sequence_remaining.isNone = false ∧
      nextRow.is_first_in_sequence = false := by
    simpa only [JoltInstructionRow.starts_source, Bool.or_eq_false_iff] using interior
  have some : nextRow.virtual_sequence_remaining.isSome = true := by
    cases h : nextRow.virtual_sequence_remaining with
    | none =>
      simp only [h, Option.isNone_none] at interiorFlags
      cases interiorFlags.1
    | some n => rfl
  have nextVirtual : witness.NextIsVirtual t = 1 := by
    rw [equations.nextIsVirtualEqShift t]
    simp only [dif_pos next]
    rw [opFlag_of_selected_bytecode charAbove2pow127 context equations
      .VirtualInstruction ⟨t.val + 1, next⟩ nextSlot nextSelected]
    simp only [bytecodeCircuitFlag, nextRowIs, JoltMetadata.circuitFlag,
      some, ↓reduceIte]
  have nextFirst : witness.NextIsFirstInSequence t = 0 := by
    rw [equations.nextIsFirstInSequenceEqShift t]
    simp only [dif_pos next]
    rw [opFlag_of_selected_bytecode charAbove2pow127 context equations
      .IsFirstInSequence ⟨t.val + 1, next⟩ nextSlot nextSelected]
    simp only [bytecodeCircuitFlag, nextRowIs, JoltMetadata.circuitFlag,
      interiorFlags.2, Bool.false_eq_true, ↓reduceIte]
  have doNot : witness.OpFlags .DoNotUpdateUnexpandedPC t = 1 := by
    have relation := equations.mustStartSequenceFromBeginning t
    rw [nextVirtual, nextFirst] at relation
    simp only [sub_zero, one_mul] at relation
    exact (sub_eq_zero.mp relation).symm
  have remaining : row.virtual_sequence_remaining.getD 0 ≠ 0 := by
    rw [opFlag_of_selected_bytecode charAbove2pow127 context equations
      .DoNotUpdateUnexpandedPC t slot selected] at doNot
    simp only [bytecodeCircuitFlag, rowIs, JoltMetadata.circuitFlag] at doNot
    by_contra zero
    simp only [zero, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at doNot
    exact zero_ne_one doNot
  obtain ⟨chosen, chosenSelected, before⟩ :=
    selected_next_of_remaining charAbove2pow127 context equations
      t next slot selected rowIs remaining
  have same := bytecodeRa_at_most_one charAbove2pow127 context equations
    ⟨t.val + 1, next⟩ nextSlot chosen nextSelected chosenSelected
  simpa only [same] using before

/-- A selected register shift follows its actual mask-producing bytecode row.
The producer's post-state is a separate execution-prefix linkage obligation. -/
theorem selected_registerShift_fed
    (t : Fin params.traceLength) (next : t.val + 1 < params.traceLength)
    (slot nextSlot : Fin (2 ^ params.logBytecodeK))
    (selected : bytecodeRa witness slot t = 1)
    (nextSelected : bytecodeRa witness nextSlot ⟨t.val + 1, next⟩ = 1)
    {row nextRow : JoltInstructionRow}
    (rowIs : bytecodeRow context.bytecode slot.val = some row)
    (nextRowIs : bytecodeRow context.bytecode nextSlot.val = some nextRow)
    (isShift : ExpansionFacts.isRegisterShift nextRow.instruction = true) :
    nextSlot.val = slot.val + 1 ∧
      ExpansionFacts.masksFed row.instruction nextRow.instruction = true := by
  obtain ⟨nextIndex, nextBound⟩ := nextSlot
  cases nextIndex with
  | zero =>
    simp only [bytecodeRow] at nextRowIs
    cases nextRowIs
  | succ k =>
    simp only [bytecodeRow] at nextRowIs
    obtain ⟨inRange, rowEq⟩ := Array.getElem?_eq_some_iff.mp nextRowIs
    obtain ⟨j, before, fed, notStart⟩ :=
      ExpansionRows.expand_program_shiftPairs _ _ context.expands k inRange
        (by simpa only [Array.getElem_toList inRange, rowEq] using isShift)
    have interior : nextRow.starts_source = false := by
      simpa only [Array.getElem_toList inRange, rowEq] using notStart
    have adjacent := selected_interior_predecessor charAbove2pow127 context equations
      t next slot ⟨k + 1, nextBound⟩ selected nextSelected rowIs
      (by simpa only [bytecodeRow] using nextRowIs) interior
    have prevIndex : slot.val = j + 1 := by
      change k + 1 = slot.val + 1 at adjacent
      omega
    have jBound : j < context.bytecode.size := by omega
    have producer : row = context.bytecode[j] := by
      rw [prevIndex] at rowIs
      simp only [bytecodeRow, Array.getElem?_eq_getElem jBound,
        Option.some.injEq] at rowIs
      exact rowIs.symm
    refine ⟨adjacent, ?_⟩
    simpa only [Array.getElem_toList jBound, Array.getElem_toList inRange,
      producer, rowEq] using fed

end JoltConstraints.Soundness
