import Mathlib.Algebra.Field.Defs
import JoltConstraints.witness
import JoltConstraints.honest_witness
import JoltConstraints.execution_conditions

set_option autoImplicit false

namespace JoltConstraints

private theorem array_fin_index {α : Type} (a : Array α) (i : Fin a.size) :
    a[i] = a[i.val] := rfl

private theorem virtual_flag_eq_first_of_entry (program : JoltProgram)
    (layout : program.SequenceLayout) (i : Fin program.expandedBytecode.size)
    (hentry : program.expandedBytecode[i].isEntry) :
    JoltMetadata.circuitFlag program.expandedBytecode[i] .VirtualInstruction =
      JoltMetadata.circuitFlag program.expandedBytecode[i] .IsFirstInSequence := by
  change program.expandedBytecode[i].virtualSequenceRemaining.isSome =
    program.expandedBytecode[i].isFirstInSequence
  cases hs : program.expandedBytecode[i].virtualSequenceRemaining with
  | none =>
      have hfirst := layout.ordinary i hs
      simp only [array_fin_index] at hs hfirst ⊢
      simp [hfirst]
  | some n =>
      have hfirst : program.expandedBytecode[i].isFirstInSequence = true := by
        change program.expandedBytecode[i].virtualSequenceRemaining = none ∨
          program.expandedBytecode[i].isFirstInSequence = true at hentry
        simp only [array_fin_index] at hs hentry ⊢
        simpa [hs] using hentry
      simp only [array_fin_index] at hs hfirst ⊢
      simp [hfirst]

/-- Constraint (19) in `constraints.md` (stage 1):
entering an interior virtual-sequence row requires preserving the unexpanded PC.
Rust: https://github.com/abiswas3/jolt/tree/main/crates/jolt-r1cs/src/constraints/rv64.rs -/
def mustStartSequenceFromBeginning {F : Type} [Field F] {params : WitnessParams}
    (witness : WitnessType F params) : Prop :=
  ∀ t : Fin params.traceLength,
    (witness.NextIsVirtual t - witness.NextIsFirstInSequence t) *
      (1 - witness.OpFlags .DoNotUpdateUnexpandedPC t) = 0

/-- Completeness under the explicit execution conditions below.
The trace type supplies fetched addresses and source/virtual sequence boundaries;
termination and arithmetic bounds are required separately where used. -/
theorem honestWitness_mustStartSequenceFromBeginning
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (tracePadded : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size) :
    mustStartSequenceFromBeginning
      (JoltProgram.honestWitness (F := F) params trace ramFits tracePadded bytecodeDomain) := by
  intro t
  by_cases hnextWitness : t.val + 1 < params.traceLength
  · by_cases hnextTrace : t.val + 1 < trace.rows.size
    · have ht : t.val < trace.rows.size := by omega
      let row := getElem trace.rows t.val ht
      let nextRow := getElem trace.rows (t.val + 1) hnextTrace
      let bytecodeRow := getElem program.expandedBytecode row.rowIndex.val row.rowIndex.isLt
      let nextBytecodeRow := getElem program.expandedBytecode
        nextRow.rowIndex.val nextRow.rowIndex.isLt
      by_cases hcont : bytecodeRow.continues = true
      · have hflag : JoltMetadata.circuitFlag bytecodeRow
            .DoNotUpdateUnexpandedPC = true := by
          simpa [JoltMetadata.circuitFlag, JoltProgramRow.continues] using hcont
        have hflag' : JoltMetadata.circuitFlag
            program.expandedBytecode[trace.rows[t.val].rowIndex] .DoNotUpdateUnexpandedPC =
              true := by
          simpa only [bytecodeRow, row] using hflag
        dsimp [mustStartSequenceFromBeginning, JoltProgram.honestWitness,
          HonestWitness.OpFlags]
        simp only [dif_pos ht]
        simp only [array_fin_index] at hflag' ⊢
        simp [hflag']
      · have hfalse : bytecodeRow.continues = false := Bool.eq_false_iff.mpr hcont
        have hsucc := trace.successor t.val ht hnextTrace
        change (if bytecodeRow.continues then _ else
          row.postState.sail.regs.get? Register.nextPC = some nextBytecodeRow.address ∧
          nextBytecodeRow.isEntry ∧ nextBytecodeRow.address ≠ bytecodeRow.address) at hsucc
        simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at hsucc
        have hflags := virtual_flag_eq_first_of_entry program trace.sequenceLayout
          nextRow.rowIndex hsucc.2.1
        have hflags' : JoltMetadata.circuitFlag
            program.expandedBytecode[trace.rows[t.val + 1].rowIndex]
              .VirtualInstruction = JoltMetadata.circuitFlag
            program.expandedBytecode[trace.rows[t.val + 1].rowIndex]
              .IsFirstInSequence := by
          simpa only [nextRow] using hflags
        dsimp [mustStartSequenceFromBeginning, JoltProgram.honestWitness,
          HonestWitness.NextIsVirtual, HonestWitness.NextIsFirstInSequence,
          HonestWitness.OpFlags]
        simp only [dif_pos hnextWitness, dif_pos hnextTrace, dif_pos ht]
        simp only [array_fin_index] at hflags' ⊢
        rw [hflags']
        ring
    · simp [JoltProgram.honestWitness, HonestWitness.NextIsVirtual,
        HonestWitness.NextIsFirstInSequence, HonestWitness.OpFlags,
        hnextWitness, hnextTrace]
  · simp [JoltProgram.honestWitness, HonestWitness.NextIsVirtual,
      HonestWitness.NextIsFirstInSequence, hnextWitness]

end JoltConstraints
