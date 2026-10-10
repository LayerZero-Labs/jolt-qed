import JoltConstraints.Soundness.Layer1.BytecodeReads
import JoltConstraints.Soundness.Layer1.RamReads

/-! Consequences of the memory-operation flags. Non-memory cycles have no RAM
address, padding has those flags unset, and loads contribute no write increment.
Flag equalities for executed instructions come from Layer 1's bytecode reads. -/

set_option autoImplicit false

namespace JoltConstraints.Soundness

variable {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}

/-- A cycle with neither memory-operation flag set has zero RAM address. -/
theorem ramAddress_zero_of_not_load_store
    (noAccess : ramAddrEqZeroIfNotLoadStore witness) (t : Fin params.traceLength)
    (noLoad : witness.OpFlags .Load t = 0) (noStore : witness.OpFlags .Store t = 0) :
    witness.RamAddress t = 0 := by
  simpa [noLoad, noStore] using noAccess t

variable {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
  (charAbove2pow127 : 2 ^ 127 < ringChar F)
  (context : ConstraintContext joltInstance privateInputs params)
  (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)

include charAbove2pow127 context equations

/-- Every padding cycle has zero RAM address. This does not assume that padding
forms a suffix; that is a separate Layer 6 obligation. -/
theorem ramAddress_zero_of_padding (t : Fin params.traceLength)
    (padding : witness.InstructionFlags .IsNoop t = 1) : witness.RamAddress t = 0 := by
  obtain ⟨chosen, selected, _⟩ := bytecodeRa_unique charAbove2pow127 context equations t
  have flag := instructionFlag_of_selected_bytecode charAbove2pow127 context equations
    .IsNoop t chosen selected
  have noRow : bytecodeRow context.bytecode chosen.val = none := by
    cases present : bytecodeRow context.bytecode chosen.val with
    | none => rfl
    | some row =>
      simp [bytecodeInstructionFlag, present, JoltMetadata.instructionFlag, padding] at flag
  apply ramAddress_zero_of_not_load_store equations.ramAddrEqZeroIfNotLoadStore t
  · rw [opFlag_of_selected_bytecode charAbove2pow127 context equations .Load t chosen selected]
    simp [bytecodeCircuitFlag, noRow]
  · rw [opFlag_of_selected_bytecode charAbove2pow127 context equations .Store t chosen selected]
    simp [bytecodeCircuitFlag, noRow]

private theorem ramInc_zero_of_selected_load (t : Fin params.traceLength)
    (load : witness.OpFlags .Load t = 1)
    (chosen : Fin params.ramSize) (selected : witness.RamRa chosen t = 1) :
    witness.RamInc t = 0 := by
  have equal : witness.RamReadValue t = witness.RamWriteValue t := by
    apply sub_eq_zero.mp
    simpa [load] using equations.ramReadEqRamWriteIfLoad t
  rw [ramReadValue_of_selected charAbove2pow127 context equations t chosen selected,
    ramWriteValue_of_selected charAbove2pow127 context equations t chosen selected] at equal
  simpa only [add_eq_left] using equal.symm

/-- A load has zero write effect on every RAM word, including when its raw
address is zero and no word is selected. This does not assert execution succeeds. -/
theorem ram_write_effect_zero_of_load (t : Fin params.traceLength)
    (load : witness.OpFlags .Load t = 1) (address : Fin params.ramSize) :
    witness.RamRa address t * witness.RamInc t = 0 := by
  rcases ramRa_zero_or_unique charAbove2pow127 context equations t with zero | ⟨chosen, selected, _⟩
  · simp [zero]
  · rw [ramInc_zero_of_selected_load charAbove2pow127 context equations t load chosen selected, mul_zero]

end JoltConstraints.Soundness
