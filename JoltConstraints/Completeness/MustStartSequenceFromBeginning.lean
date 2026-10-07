import JoltConstraints.Constraints.MustStartSequenceFromBeginning
import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions

set_option autoImplicit false

namespace JoltConstraints

private theorem array_fin_index {α : Type} (a : Array α) (i : Fin a.size) :
    a[i] = a[i.val] := rfl

private theorem virtual_flag_eq_first_of_entry {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (layout : BytecodeLayout trace.bytecode) (i : Fin trace.bytecode.size)
    (hentry : trace.bytecode[i].starts_source = true) :
    JoltMetadata.circuitFlag trace.bytecode[i] .VirtualInstruction =
      JoltMetadata.circuitFlag trace.bytecode[i] .IsFirstInSequence := by
  change trace.bytecode[i].virtual_sequence_remaining.isSome =
    trace.bytecode[i].is_first_in_sequence
  cases hs : trace.bytecode[i].virtual_sequence_remaining with
  | none =>
      have hfirst := layout.ordinary i hs
      simp only [array_fin_index] at hs hfirst ⊢
      simp [hfirst]
  | some n =>
      have hfirst : trace.bytecode[i].is_first_in_sequence = true := by
        unfold JoltInstructionRow.starts_source at hentry
        simp only [array_fin_index] at hs hentry ⊢
        simpa [hs] using hentry
      simp only [array_fin_index] at hs hfirst ⊢
      simp [hfirst]

/-- Completeness under the explicit execution conditions below.
The trace type supplies fetched addresses and source/virtual sequence boundaries;
termination and arithmetic bounds are required separately where used. -/
theorem honestWitness_mustStartSequenceFromBeginning
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (tracePadded : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size) :
    mustStartSequenceFromBeginning
      (HonestTrace.honestWitness (F := F) params trace) := by
  intro t
  by_cases hnextWitness : t.val + 1 < params.traceLength
  · by_cases hnextTrace : t.val + 1 < trace.rows.size
    · have ht : t.val < trace.rows.size := by omega
      let row := getElem trace.rows t.val ht
      let nextRow := getElem trace.rows (t.val + 1) hnextTrace
      let bytecodeRow := getElem trace.bytecode row.rowIndex.val row.rowIndex.isLt
      let nextBytecodeRow := getElem trace.bytecode
        nextRow.rowIndex.val nextRow.rowIndex.isLt
      by_cases hcont : bytecodeRow.continues = true
      · have hflag : JoltMetadata.circuitFlag bytecodeRow
            .DoNotUpdateUnexpandedPC = true := by
          simpa [JoltMetadata.circuitFlag, JoltInstructionRow.continues] using hcont
        have hflag' : JoltMetadata.circuitFlag
            trace.bytecode[trace.rows[t.val].rowIndex] .DoNotUpdateUnexpandedPC =
              true := by
          simpa only [bytecodeRow, row] using hflag
        dsimp [mustStartSequenceFromBeginning, HonestTrace.honestWitness,
          HonestWitness.OpFlags]
        simp only [dif_pos ht]
        simp only [array_fin_index] at hflag' ⊢
        simp [hflag']
      · have hfalse : bytecodeRow.continues = false := Bool.eq_false_iff.mpr hcont
        have hsucc := trace.successor t.val ht hnextTrace
        change (if bytecodeRow.continues then _ else
          row.postState.sail.regs.get? Register.nextPC = some nextBytecodeRow.address ∧
          nextBytecodeRow.starts_source = true ∧ nextBytecodeRow.address ≠ bytecodeRow.address) at hsucc
        simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at hsucc
        have hflags := virtual_flag_eq_first_of_entry trace trace.layout
          nextRow.rowIndex hsucc.2.1
        have hflags' : JoltMetadata.circuitFlag
            trace.bytecode[trace.rows[t.val + 1].rowIndex]
              .VirtualInstruction = JoltMetadata.circuitFlag
            trace.bytecode[trace.rows[t.val + 1].rowIndex]
              .IsFirstInSequence := by
          simpa only [nextRow] using hflags
        dsimp [mustStartSequenceFromBeginning, HonestTrace.honestWitness,
          HonestWitness.NextIsVirtual, HonestWitness.NextIsFirstInSequence,
          HonestWitness.OpFlags]
        simp only [dif_pos hnextWitness, dif_pos hnextTrace, dif_pos ht]
        simp only [array_fin_index] at hflags' ⊢
        rw [hflags']
        ring
    · simp [HonestTrace.honestWitness, HonestWitness.NextIsVirtual,
        HonestWitness.NextIsFirstInSequence, HonestWitness.OpFlags,
        hnextWitness, hnextTrace]
  · simp [HonestTrace.honestWitness, HonestWitness.NextIsVirtual,
      HonestWitness.NextIsFirstInSequence, hnextWitness]

end JoltConstraints
