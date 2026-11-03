import JoltConstraints.honest_witness

set_option autoImplicit false

namespace JoltConstraints

/-- A load's RAM read is its captured destination, including floor loads;
for example, LoadB captures the containing doubleword rather than one byte.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`load`) at `c6703570`. -/
theorem ramReadValue_of_load {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance inputs) (t : Fin params.traceLength)
    (ht : t.val < trace.rows.size)
    (load : JoltMetadata.opcodeFlag trace.bytecode[(trace.rows[t.val]'ht).rowIndex].instruction
      .Load = true) :
    HonestWitness.RamReadValue (F := F) params trace t =
      TraceWitness.RdWriteValue params trace t := by
  obtain ⟨faultClass, dst, base, imm, selected⟩ := JoltMetadata.opcodeFlag_load_cases _ load
  simp only [Fin.getElem_fin] at selected
  rcases selected with selected | ⟨fault, selected | selected | selected⟩ <;>
    simp [HonestWitness.RamReadValue, TraceWitness.RdWriteValue, HonestTrace.row, ht, selected]
  all_goals split <;> simp_all
  all_goals
    rename_i excluded
    first
    | exact False.elim (excluded _ _ _ _ rfl rfl rfl rfl)
    | exact False.elim (excluded _ _ _ _ _ rfl rfl rfl rfl rfl)

/-- A load's RAM write also preserves its captured doubleword; for example,
LoadW changes a register but leaves RAM unchanged.
Jolt's tracer: `tracer/src/instruction/floor_access.rs` (`load`) at `c6703570`. -/
theorem ramWriteValue_of_load {F : Type} [Field F] (params : WitnessParams)
    (trace : Trace) (t : Fin params.traceLength) (ht : t.val < trace.rows.size)
    (load : JoltMetadata.opcodeFlag trace.bytecode[(trace.rows[t.val]'ht).rowIndex].instruction
      .Load = true) :
    TraceWitness.RamWriteValue (F := F) params trace t =
      TraceWitness.RdWriteValue params trace t := by
  obtain ⟨faultClass, dst, base, imm, selected⟩ := JoltMetadata.opcodeFlag_load_cases _ load
  simp only [Fin.getElem_fin] at selected
  rcases selected with selected | ⟨fault, selected | selected | selected⟩ <;>
    simp [TraceWitness.RamWriteValue, TraceWitness.RdWriteValue, ht, selected]

end JoltConstraints
