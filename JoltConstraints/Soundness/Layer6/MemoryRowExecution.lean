import JoltConstraints.Soundness.Layer6.MemoryRowAppend

open LeanRV64D

/-! Load and store executions with a uniform memory agreement result. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

section
variable {F : Type} [Field F] (joltField : JoltField F)
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (assumptions : inst.SoundnessAssumptions) (restrictions : inst.TemporaryRestrictions)
    (witness : WitnessType F params) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun inst inputs) (t : Fin params.traceLength)
    (next : Fin run.bytecode.size) (pre : SailJoltState) (ready : run.NextStep next pre)
    (slot : Fin (2 ^ params.logBytecodeK)) (selected : bytecodeRa witness slot t = 1)
    (slotIs : slot.val = next.val + 1)
    (rowIs : bytecodeRow context.bytecode slot.val = some run.bytecode[next])
    {live : Fin 128 → Prop} (registers : RegisterAgreementOn live witness t pre)
    (ram : OrdinaryRamAgreement context.io.memory_layout (fun index => witness.RamVal index t) pre)
    (device : DeviceRamAgreement (fun index => witness.RamVal index t) run.toTrace)
    (termination : (¬ ∃ i : Fin run.rows.size, run.StoresTerminationAt i) →
      TerminationTableZero run.initialState.jolt_device.memory_layout (fun index => witness.RamVal index t))
    (sameDevice : pre.jolt_device = (TraceWitness.finalTraceState run.toTrace).jolt_device)
    (advice : run.bytecode[next].instruction.RuntimeAdvice)

include joltField assumptions restrictions equations ready selected slotIs rowIs registers ram device termination sameDevice

/-- A load row in either address region executes with the same register-write
and memory-agreement contract at its accessed doubleword; for example, an input
LD, a RAM LD and a RAM VirtualLoadH all preserve the memory image and add the
destination to the live registers. -/
theorem load_row_execution
    {width : MemoryWidth} {destination : Dst} {base : Src} {imm : BitVec 64}
    (loadRow : LoadRow run.bytecode[next].instruction width destination base imm)
    (baseLive : live (TraceWitness.sourceRegisterAddress base))
    (encoded : witness.RamAddress t = ((width.accessed (sourceValue base pre + imm)).toNat : F)) :
    ∃ value : BitVec 64,
      let post := afterWriteDst destination value pre
      let step : TraceRow run.bytecode := ⟨next, advice, pre, post⟩
      execWithTapeAnswer (run.bytecode[next].instruction.withRuntimeAdvice advice) 0 pre =
        .ok RETIRE_SUCCESS post ∧
      (∀ bound : t.val + 1 < params.traceLength,
        RegisterAgreementOn (fun register => live register ∨
          register = TraceWitness.destinationRegisterAddress destination) witness ⟨t.val + 1, bound⟩ post) ∧
      DeviceMemoryStepAgreement witness t run.toTrace step
        (∃ i : Fin run.rows.size, run.StoresTerminationAt i) := by
  have layoutEq := initial_state_memory_layout context run.initialized
  by_cases inRam : RAM_START_ADDRESS ≤ (width.accessed (sourceValue base pre + imm)).toNat
  · obtain ⟨_, executes, nextRam, finalRam⟩ := load_ram_step joltField context equations selected rowIs
      loadRow assumptions.ramRegionFits registers baseLive ram inRam
      (loadRow.address_checks restrictions.tracerAddressChecks run next pre ready) 0 advice
    refine ⟨_, executes, fun next => (nextRam next).1, ?_⟩
    exact ordinary_memory_step joltField witness context equations run _ t _ encoded inRam device
      termination (by cases destination <;> exact sameDevice) (fun next => (nextRam next).2) finalRam
  · have bytecodeEq : run.bytecode = context.bytecode := Option.some.inj (run.expands.symm.trans context.expands)
    obtain ⟨value, _, _, _, _, executes, nextRegisters, memory⟩ := load_device_step joltField witness context
      equations assumptions.ramRegionFits restrictions.tracerAddressChecks restrictions.panicStoresOne
      restrictions.terminationThenStall run bytecodeEq t next pre ready slot selected slotIs
      loadRow live registers baseLive (by rw [layoutEq]; exact ram) device termination
      (Nat.lt_of_not_ge inRam) _ rfl 0 advice
    exact ⟨value, executes, nextRegisters, memory⟩

/-- A store row in either address region preserves the old live registers and
both memory agreements at its accessed doubleword, with termination zero
conditional on old and new stores.
For example, a RAM SD updates the byte map and an output VirtualStoreB updates
the device. -/
theorem store_row_execution
    {width : MemoryWidth} {base source : Src} {imm : BitVec 64}
    (storeRow : StoreRow run.bytecode[next].instruction width base source imm)
    (baseLive : live (TraceWitness.sourceRegisterAddress base))
    (sourceLive : live (TraceWitness.sourceRegisterAddress source))
    (encoded : witness.RamAddress t = ((width.accessed (sourceValue base pre + imm)).toNat : F)) :
    ∃ post : SailJoltState,
      let step : TraceRow run.bytecode := ⟨next, advice, pre, post⟩
      execWithTapeAnswer (run.bytecode[next].instruction.withRuntimeAdvice advice) 0 pre =
        .ok RETIRE_SUCCESS post ∧
      (∀ bound : t.val + 1 < params.traceLength,
        RegisterAgreementOn live witness ⟨t.val + 1, bound⟩ post) ∧
      DeviceMemoryStepAgreement witness t run.toTrace step
        ((∃ i : Fin run.rows.size, run.StoresTerminationAt i) ∨
          TouchesTermination pre.jolt_device (width.accessed (sourceValue base pre + imm))) := by
  have layoutEq := initial_state_memory_layout context run.initialized
  by_cases inRam : RAM_START_ADDRESS ≤ (width.accessed (sourceValue base pre + imm)).toNat
  · obtain ⟨_, executes, nextRam, finalRam⟩ := store_ram_step_agreement joltField context equations
      selected rowIs storeRow assumptions.ramRegionFits registers baseLive sourceLive ram inRam
      (storeRow.address_checks restrictions.tracerAddressChecks run next pre ready) 0 advice
    refine ⟨_, executes, fun next => (nextRam next).1, ?_⟩
    exact memory_step_mono (ordinary_memory_step joltField witness context equations run _ t _ encoded
      inRam device termination sameDevice (fun next => (nextRam next).2) finalRam) Or.inl
  · have bytecodeEq : run.bytecode = context.bytecode := Option.some.inj (run.expands.symm.trans context.expands)
    obtain ⟨post, _, _, _, _, _, executes, nextRegisters, memory⟩ := store_device_step joltField witness
      context equations assumptions.ramRegionFits restrictions.tracerAddressChecks
      restrictions.panicStoresOne run bytecodeEq t next pre ready slot selected slotIs storeRow live
      registers baseLive sourceLive (by rw [layoutEq]; exact ram) device termination
      (Nat.lt_of_not_ge inRam) _ rfl 0 advice
    exact ⟨post, executes, nextRegisters, memory⟩
end
end JoltInstance
