import JoltConstraints.Soundness.Layer6.MemoryRowAppend

/-! Load and store executions with a uniform memory agreement result. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

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

/-- A load in either address region executes with the same register-write and
memory-agreement contract; for example, an input LD and a RAM LD both preserve
the memory image and add the destination to the live registers. -/
theorem load_row_execution
    {fault : LoadFaultClass} {destination : Dst} {base : Src} {imm : BitVec 64}
    (instruction : run.bytecode[next].instruction = .LD fault destination base imm)
    (baseLive : live (TraceWitness.sourceRegisterAddress base))
    (encoded : witness.RamAddress t = ((sourceValue base pre + imm).toNat : F))
    (atCut : t.val = run.rows.size) :
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
  by_cases inRam : RAM_START_ADDRESS ≤ (sourceValue base pre + imm).toNat
  · obtain ⟨_, executes, nextRam, finalRam⟩ := ld_ram_step joltField context equations selected rowIs
      instruction assumptions.ramRegionFits registers baseLive ram inRam
      (ld_address_checks restrictions.tracerAddressChecks run next pre ready _ _ _ _ instruction) 0 advice
    refine ⟨_, executes, fun next => (nextRam next).1, ?_⟩
    exact ordinary_memory_step joltField witness context equations run _ t _ encoded inRam device
      termination (by cases destination <;> exact sameDevice) (fun next => (nextRam next).2) finalRam
  · have bytecodeEq : run.bytecode = context.bytecode := Option.some.inj (run.expands.symm.trans context.expands)
    obtain ⟨value, _, _, _, _, executes, nextRegisters, memory⟩ := ld_device_step joltField witness context
      equations assumptions.ramRegionFits restrictions.tracerAddressChecks restrictions.panicStoresOne
      restrictions.terminationThenStall run bytecodeEq t atCut next pre ready slot selected slotIs
      _ _ _ _ instruction live registers baseLive (by rw [layoutEq]; exact ram) device termination
      (Nat.lt_of_not_ge inRam) _ rfl 0 advice
    exact ⟨value, executes, nextRegisters, memory⟩

/-- A store in either address region preserves the old live registers and both
memory agreements, with termination zero conditional on old and new stores.
For example, a RAM SD updates the byte map and an output SD updates the device. -/
theorem store_row_execution
    {base source : Src} {imm : BitVec 64}
    (instruction : run.bytecode[next].instruction = .SD base source imm)
    (baseLive : live (TraceWitness.sourceRegisterAddress base))
    (sourceLive : live (TraceWitness.sourceRegisterAddress source))
    (encoded : witness.RamAddress t = ((sourceValue base pre + imm).toNat : F))
    (atCut : t.val = run.rows.size) :
    ∃ post : SailJoltState,
      let step : TraceRow run.bytecode := ⟨next, advice, pre, post⟩
      execWithTapeAnswer (run.bytecode[next].instruction.withRuntimeAdvice advice) 0 pre =
        .ok RETIRE_SUCCESS post ∧
      (∀ bound : t.val + 1 < params.traceLength,
        RegisterAgreementOn live witness ⟨t.val + 1, bound⟩ post) ∧
      DeviceMemoryStepAgreement witness t run.toTrace step
        ((∃ i : Fin run.rows.size, run.StoresTerminationAt i) ∨
          TouchesTermination pre.jolt_device (sourceValue base pre + imm)) := by
  have layoutEq := initial_state_memory_layout context run.initialized
  by_cases inRam : RAM_START_ADDRESS ≤ (sourceValue base pre + imm).toNat
  · obtain ⟨_, executes, nextRam, finalRam⟩ := sd_ram_step_agreement joltField context equations selected rowIs
      instruction assumptions.ramRegionFits registers baseLive sourceLive ram inRam
      (sd_address_checks restrictions.tracerAddressChecks run next pre ready _ _ _ instruction) 0 advice
    refine ⟨_, executes, fun next => (nextRam next).1, ?_⟩
    exact memory_step_mono (ordinary_memory_step joltField witness context equations run _ t _ encoded
      inRam device termination sameDevice (fun next => (nextRam next).2) finalRam) Or.inl
  · have bytecodeEq : run.bytecode = context.bytecode := Option.some.inj (run.expands.symm.trans context.expands)
    obtain ⟨post, _, _, _, _, _, executes, nextRegisters, memory⟩ := sd_device_step joltField witness context
      equations assumptions.ramRegionFits restrictions.tracerAddressChecks restrictions.panicStoresOne
      run bytecodeEq t atCut next pre ready slot selected slotIs _ _ _ instruction live registers
      baseLive sourceLive (by rw [layoutEq]; exact ram) device termination (Nat.lt_of_not_ge inRam) _ rfl 0 advice
    exact ⟨post, executes, nextRegisters, memory⟩
end
end JoltInstance
