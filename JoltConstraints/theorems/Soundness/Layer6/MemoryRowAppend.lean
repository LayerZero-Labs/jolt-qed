import JoltConstraints.theorems.Soundness.Layer6.RamCutAgreement
import JoltConstraints.theorems.Soundness.Layer6.PlainRow
import JoltConstraints.theorems.Soundness.Layer5.CodeRegionFrame
import JoltConstraints.theorems.Soundness.Layer5.TapeDeviceFrame

open LeanRV64D

/-! Shared assembly of load/store execution into a represented row extension. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

/-- The represented cut supplies every shared-memory word at the prepared state.
For example, this supplies an input LD and a RAM LD with the same agreement. -/
theorem ExpansionState.memoryAt
    {F : Type} [Field F] {params : WitnessParams}
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    {witness : WitnessType F params} {context : ConstraintContext inst inputs params}
    {run : UntrustedAnswerRun inst inputs} {first : Fin context.bytecode.size} {done : Nat}
    (state : ExpansionState witness context run first done) (bound : run.rows.size < params.traceLength)
    {next : Fin run.bytecode.size} {pre : SailJoltState} (entry : RawRowEntry run next pre) :
    SharedRamAgreement context.io.memory_layout
      (fun index => witness.RamVal index ⟨run.rows.size, bound⟩) pre := by
  have ram := (ramAgreement_iff run.toTrace _).mp (state.represents.cutRam.1 bound)
  have prepared := rawEntry_prepared entry (state.registers bound)
  intro index
  rw [prepared.2.1]
  rw [initial_state_memory_layout context run.initialized] at ram
  exact ram index

/-- Preparing the next row retains the initialized layout and protected code span.
For example, source-boundary PC preparation changes neither memory invariant. -/
theorem rawEntry_memory_invariants
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (context : ConstraintContext inst inputs params) (run : UntrustedAnswerRun inst inputs)
    {next : Fin run.bytecode.size} {pre : SailJoltState} (entry : RawRowEntry run next pre) :
    pre.jolt_device.memory_layout = context.io.memory_layout ∧
      pre.codeRegion = ramCodeRegion context.bytecode context.io.memory_layout := by
  have initialLayout := initial_state_memory_layout context run.initialized
  have layout := run.final_device_same.1.trans initialLayout
  have bytecodeEq : run.bytecode = context.bytecode :=
    Option.some.inj (run.expands.symm.trans context.expands)
  have code := run.final_codeRegion
  rw [initialLayout, bytecodeEq] at code
  rcases rawEntry_state entry with rfl | ⟨address, compressed, rfl⟩
  · exact ⟨layout, code⟩
  · exact ⟨layout, code⟩

/-- A successful memory row extends the expansion with full shared-word agreement.
For example, an output SD and a RAM SD use the same append proof. -/
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
    (memory :
      (∀ next : run.rows.size + 1 < params.traceLength,
        SharedRamAgreement context.io.memory_layout
          (fun index => witness.RamVal index ⟨run.rows.size + 1, next⟩) step.postState) ∧
      (∀ _last : run.rows.size + 1 = params.traceLength,
        SharedRamAgreement context.io.memory_layout witness.RamValFinal step.postState)) :
    PlainRowExtension witness context run first done bound := by
  have image (values : Fin params.ramSize → F)
      (ram : SharedRamAgreement context.io.memory_layout values step.postState) :
      ∀ index, values index = ((TraceWitness.finalRamWord
        { run.toTrace with rows := run.rows.push step } index.val).toNat : F) := by
    intro index
    rw [finalRamWord_eq_ram_doubleword, finalTraceState_push,
      initial_state_memory_layout context run.initialized]
    exact ram index
  have represented : RepresentsPrefix witness {run.toTrace with rows := run.rows.push step} := by
    refine { rows with cutRam := ⟨?_, ?_⟩ }
    · intro next
      have h : run.rows.size + 1 < params.traceLength := by simpa only [Array.size_push] using next
      simpa only [Array.size_push] using image _ (memory.1 h)
    · intro last
      have h : run.rows.size + 1 = params.traceLength := by simpa only [Array.size_push] using last
      exact image _ (memory.2 h)
  obtain ⟨atRow, _, _, _, _⟩ := state.selectedRow unfinished bound step.rowIndex indexIs
  obtain ⟨candidate, traceEq, answers, extendsRun, size, after⟩ := append_expansion_row
    joltField witness context equations run first done state unfinished bound step 0 indexIs executes entry represented
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
