import JoltConstraints.Soundness.Layer6.RamCutAgreement

/-! Shared assembly of load/store execution into a represented row extension. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

/-- The cut image supplies ordinary RAM at the prepared state and device words
at the retained prefix; for example, both are available before an LD. -/
theorem ExpansionState.memoryAt
    {F : Type} [Field F] {params : WitnessParams}
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {witness : WitnessType F params} {context : ConstraintContext inst inputs params}
    {run : UntrustedAnswerRun inst inputs} {first : Fin context.bytecode.size} {done : Nat}
    (state : ExpansionState witness context run first done) (bound : run.rows.size < params.traceLength)
    {next : Fin run.bytecode.size} {pre : SailJoltState} (entry : RawRowEntry run next pre) :
    OrdinaryRamAgreement context.io.memory_layout (fun index => witness.RamVal index ⟨run.rows.size, bound⟩) pre ∧
    DeviceRamAgreement (fun index => witness.RamVal index ⟨run.rows.size, bound⟩) run.toTrace := by
  obtain ⟨ram, device⟩ := (ramAgreement_iff context run _).mp (state.represents.cutRam.1 bound)
  have prepared := rawEntry_prepared entry (state.registers bound)
  refine ⟨?_, device⟩
  intro index inRam
  rw [prepared.2.1]
  rw [initial_state_memory_layout context run.initialized] at ram
  exact ram index inRam

/-- Enlarging the recorded store event weakens only the conditional obligation
that termination remain zero; for example, include a newly appended SD. -/
theorem memory_step_mono
    {F : Type} [Field F] {params : WitnessParams} {witness : WitnessType F params}
    {t : Fin params.traceLength} {trace : Trace} {step : TraceRow trace.bytecode} {old new : Prop}
    (memory : DeviceMemoryStepAgreement witness t trace step old) (implies : old → new) :
    DeviceMemoryStepAgreement witness t trace step new := by
  refine ⟨fun next => ⟨(memory.1 next).1, (memory.1 next).2.1, ?_⟩, memory.2⟩
  intro absent
  exact (memory.1 next).2.2 (fun old => absent (implies old))

private theorem exists_fin_push {α : Type} (rows : Array α) (step : α) (property : α → Prop) :
    (∃ i : Fin (rows.push step).size, property (rows.push step)[i]) ↔
      (∃ i : Fin rows.size, property rows[i]) ∨ property step := by
  simp only [Fin.exists_iff, Fin.getElem_fin, ← Array.exists_mem_iff_exists_getElem,
    Array.mem_push, or_and_right, exists_or]
  simp

/-- A successful memory row with both memory agreements extends the expansion.
The store event includes old SDs and the newly appended row, so an output SD
preserves termination zero while a termination SD discharges that obligation. -/
theorem append_memory_row
    {F : Type} [Field F] (joltField : JoltField F) {params : WitnessParams}
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (witness : WitnessType F params) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun inst inputs) (first : Fin context.bytecode.size) (done : Nat)
    (state : ExpansionState witness context run first done)
    (unfinished : done < expansionRowCount context.bytecode first)
    (bound : run.rows.size < params.traceLength) (step : TraceRow run.bytecode)
    (indexIs : step.rowIndex.val = first.val + done) (entry : RawRowEntry run step.rowIndex step.preState)
    (present : AllRegistersPresent step.preState.sail)
    (noAdvice : run.bytecode[step.rowIndex].instruction.adviceValue? = none)
    (noTape : ∀ dst width, run.bytecode[step.rowIndex].instruction ≠ .VirtualAdviceLoad dst width)
    (executes : execWithTapeAnswer (run.bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice)
      0 step.preState = .ok RETIRE_SUCCESS step.postState)
    (rows : RepresentsRows witness {run.toTrace with rows := run.rows.push step})
    (registers : ∀ next : run.rows.size + 1 < params.traceLength,
      RegisterAgreementOn (fun register => ExpansionLive context.bytecode first done register ∨
        ∃ dst ∈ run.bytecode[step.rowIndex].instruction.destination?,
          register = TraceWitness.destinationRegisterAddress dst)
        witness ⟨run.rows.size + 1, next⟩ step.postState)
    (memory : DeviceMemoryStepAgreement witness ⟨run.rows.size, bound⟩ run.toTrace step
      ((∃ i : Fin run.rows.size, run.StoresTerminationAt i) ∨
        match run.bytecode[step.rowIndex].instruction with
        | .SD base _ imm => TouchesTermination step.preState.jolt_device (sourceValue base step.preState + imm)
        | _ => False)) :
    PlainRowExtension witness context run first done bound := by
  let extended := appendUntrustedRow run step 0 executes (rawEntry_starts entry) (rawEntry_linked entry)
  have image (values : Fin params.ramSize → F)
      (ram : OrdinaryRamAgreement run.initialState.jolt_device.memory_layout values step.postState)
      (device : DeviceRamAgreement values {run.toTrace with rows := run.rows.push step}) :=
    (ramAgreement_iff context extended values).mpr
      ⟨by simpa only [extended, appendUntrustedRow, finalTraceState_push] using ram, device⟩
  have represented : RepresentsPrefix witness {run.toTrace with rows := run.rows.push step} := by
    refine { rows with cutRam := ⟨?_, ?_⟩ }
    · intro next
      have h : run.rows.size + 1 < params.traceLength := by simpa only [Array.size_push] using next
      simpa only [extended, appendUntrustedRow, Array.size_push] using
        image _ (memory.1 h).1 (memory.1 h).2.1
    · intro last
      have h : run.rows.size + 1 = params.traceLength := by simpa only [Array.size_push] using last
      exact image _ (memory.2 h).1 (memory.2 h).2
  obtain ⟨atRow, _, _, _, _⟩ := state.selectedRow unfinished bound step.rowIndex indexIs
  obtain ⟨candidate, traceEq, answers, extendsRun, size, after⟩ := append_expansion_row_of_termination
    joltField witness context equations run first done state unfinished bound step 0 indexIs executes entry represented
    (fun next noStore => (memory.1 next).2.2 (by
      intro stored
      apply noStore
      apply (exists_fin_push run.rows step (fun row =>
        match run.bytecode[row.rowIndex].instruction with
        | .SD base _ imm => TouchesTermination row.preState.jolt_device (sourceValue base row.preState + imm)
        | _ => False)).mpr
      exact stored))
    (fun next => (registers next).mono (expansionLive_after context.bytecode first done _ atRow))
  refine ⟨step, 0, candidate, indexIs, entry, present, traceEq, executes, ?_, ?_,
    answers, extendsRun, size, after⟩
  · intro value member
    change value ∈ (run.bytecode[step.rowIndex].instruction.withRuntimeAdvice step.runtimeAdvice).adviceValue? at member
    rw [withRuntimeAdvice_eq_of_noAdvice _ _ noAdvice, noAdvice] at member
    cases member
  · intro dst width same
    exact False.elim (noTape dst width same)

end JoltInstance
