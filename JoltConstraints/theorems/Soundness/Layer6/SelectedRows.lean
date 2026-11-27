import JoltConstraints.theorems.Soundness.Layer6.ExecutionPrefix
import JoltConstraints.theorems.Soundness.Layer1.BytecodeReads
import JoltConstraints.theorems.Soundness.Assumptions
import JoltConstraints.theorems.Soundness.Layer1.Bytecode

open LeanRV64D
set_option autoImplicit false
namespace JoltInstance

/-- At a represented real cycle, the selected bytecode slot is the executed
row's index plus one; for example, row zero occupies slot one. -/
theorem RepresentsRows.selected_row
    {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (run : Trace)
    (bytecodeEq : run.bytecode = context.bytecode)
    (represented : RepresentsRows witness run)
    (cycle : Fin params.traceLength) (inRun : cycle.val < run.rows.size) :
    JoltConstraints.bytecodeRa witness
      ⟨run.rows[cycle.val].rowIndex.val + 1, by
        have domain : params.BytecodeDomainFor run.bytecode.size := by
          simpa only [bytecodeEq] using context.bytecodeDomain
        have fits := domain.rowsFit
        have rowBound := run.rows[cycle.val].rowIndex.isLt
        omega⟩ cycle = 1 := by
  obtain ⟨slot, selected, _⟩ := JoltConstraints.Soundness.bytecodeRa_unique
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField) context equations cycle
  have pcSelected := JoltConstraints.Soundness.pc_of_selected_bytecode
    (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    context equations cycle slot selected
  have pcRun := represented.pc cycle inRun
  have encoded : (slot.val : F) = ((run.rows[cycle.val].rowIndex.val + 1 : Nat) : F) := by
    rw [← pcSelected, pcRun]
    simp [TraceWitness.PC, TraceWitness.bytecodePc, inRun]
  have slotBound : slot.val < ringChar F := by
    have domain := params.logBytecodeK_lt_usizeBits
    have small : 2 ^ params.logBytecodeK ≤ 2 ^ 64 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have characteristic := JoltConstraints.Soundness.two_pow_64_lt_char
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    omega
  have rowBound : run.rows[cycle.val].rowIndex.val + 1 < ringChar F := by
    have domain : params.BytecodeDomainFor run.bytecode.size := by
      simpa only [bytecodeEq] using context.bytecodeDomain
    have fits := domain.rowsFit
    have small : 2 ^ params.logBytecodeK ≤ 2 ^ 64 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) params.logBytecodeK_lt_usizeBits.le
    have characteristic := JoltConstraints.Soundness.two_pow_64_lt_char
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField)
    omega
  have same := JoltConstraints.Soundness.natCast_injective_below_char
    slotBound rowBound encoded
  have sameSlot : slot = ⟨run.rows[cycle.val].rowIndex.val + 1, by
      have domain : params.BytecodeDomainFor run.bytecode.size := by
        simpa only [bytecodeEq] using context.bytecodeDomain
      have fits := domain.rowsFit
      have rowBound := run.rows[cycle.val].rowIndex.isLt
      omega⟩ := Fin.ext same
  simpa only [sameSlot] using selected

end JoltInstance

namespace JoltConstraints.Soundness

/-- A halt selected from the checked bytecode completes its source sequence.
For example, the single EBREAK panic row has countdown zero. -/
theorem ConstraintContext.halt_terminal
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (context : ConstraintContext inst inputs params) (row : JoltInstructionRow)
    (member : row ∈ context.bytecode) (halted : row.instruction.haltKind?.isSome = true) :
    row.virtual_sequence_remaining.getD 0 = 0 := by
  have accepted : pc_map_ok context.bytecode = true := by
    obtain ⟨slots, preprocessed, _⟩ := context.entryIsRust
    unfold preprocess at preprocessed
    split at preprocessed
    · assumption
    · cases preprocessed
  exact pc_map_ok_halt_terminal context.bytecode accepted row member halted

/-- The selected entry slot is a real row of the checked program.
For example, preprocessing cannot use the reserved padding slot as the entry.
Jolt at `ff6fc6568`: `ProgramPreprocessing::validate_entry_row`. -/
theorem ConstraintContext.entry_row
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (context : ConstraintContext inst inputs params) :
    ∃ row, bytecodeRow context.bytecode context.entry.val = some row := by
  have valid := context.validInputs
  unfold JoltInstance.validate_inputs at valid
  cases configured : inst.memory_layout with
  | none => simp only [configured, Bool.false_eq_true] at valid
  | some layout =>
    rw [configured] at valid
    simp only [Bool.and_eq_true] at valid
    have addressNonzero : inst.program.entry_address ≠ 0 := by
      simpa only [bne_iff_ne] using valid.2.1
    obtain ⟨slots, preprocessed, found⟩ := context.entryIsRust
    obtain ⟨noopSlot, rowSlots, paddingSlots, _⟩ := preprocess_slots context.bytecode slots preprocessed
    unfold get_first_pc at found
    rw [ite_eq_right addressNonzero, Array.findIdx?_eq_some_iff_getElem] at found
    obtain ⟨inSlots, addressMatches, _⟩ := found
    have notZero : context.entry.val ≠ 0 := by
      intro zero
      have noop := (Array.getElem?_eq_some_iff.mp noopSlot).2
      simp only [zero, noop] at addressMatches
      exact Bool.false_ne_true addressMatches
    have inRows : context.entry.val - 1 < context.bytecode.size := by
      by_contra outside
      have padding := paddingSlots context.entry.val (by omega) inSlots
      rw [(Array.getElem?_eq_some_iff.mp padding).2] at addressMatches
      exact Bool.false_ne_true addressMatches
    refine ⟨context.bytecode[context.entry.val - 1], ?_⟩
    conv_lhs => rw [show context.entry.val = (context.entry.val - 1) + 1 by omega]
    simp only [bytecodeRow, Array.getElem?_eq_getElem inRows]

end JoltConstraints.Soundness
