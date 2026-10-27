import JoltConstraints.Soundness.Layer6.PlainRow
import JoltConstraints.Soundness.Layer5.DeviceMemory

/-! Ordinary RAM and device words together describe the represented cut. -/
set_option autoImplicit false
namespace JoltInstance
open JoltConstraints JoltConstraints.Soundness
open Sail PreSail LeanRV64D.Functions JoltISA

private theorem remap_below_ram (layout : MemoryLayout) (address : BitVec 64)
    (index : Nat) (below : address.toNat < RAM_START_ADDRESS)
    (inRam : RAM_START_ADDRESS ≤ ramLowestAddress layout + 8 * index) :
    TraceWitness.remapRamAddress layout address ≠ some index := by
  unfold TraceWitness.remapRamAddress
  dsimp only
  split
  · simp
  · intro equal
    have same := Option.some.inj equal
    unfold ramLowestAddress at inRam
    omega

/-- An initialized run's final image agrees with its byte map at ordinary-RAM
words: the device buffers and flags lie below them.
For example, an output store cannot overlay the first program RAM word.
See jolt/crates/jolt-witness/src/backend/trace/ram.rs (`final_ram_state`)
at 5def437f. -/
theorem finalRamWord_ordinary
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (context : ConstraintContext inst inputs params) (run : UntrustedAnswerRun inst inputs)
    (index : Nat)
    (inRam : RAM_START_ADDRESS ≤ ramLowestAddress run.initialState.jolt_device.memory_layout + 8 * index) :
    TraceWitness.finalRamWord run.toTrace index =
      Mmu.ram_doubleword (TraceWitness.finalTraceState run.toTrace).sail.mem
        (ramLowestAddress run.initialState.jolt_device.memory_layout + 8 * index) := by
  let layout := run.initialState.jolt_device.memory_layout
  have built := (initial_state_device inst inputs run.initialState run.initialized).1
  have ordered := new_io_ordered _ _ built
  have geometry := new_io_geometry _ _ built
  have inputsEnd := (new_outputs_after_inputs _ _ built).1
  have advice := initial_state_advice_below_input inst inputs run.initialState run.initialized
  have inputsIs := initial_state_inputs inst inputs run.initialState run.initialized
  have valid := context.validInputs
  unfold JoltInstance.validate_inputs at valid
  rw [built] at valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
  have inputsFit := valid.1.2
  have fixed := run.final_device_same
  have outputFit := run.final_outputs_fit_layout
  have overlays (start : BitVec 64) (bytes : Array (BitVec 8))
      (below : start.toNat + bytes.size ≤ RAM_START_ADDRESS) (previous : BitVec 64) :=
    overlayRamBytes_below_word layout start bytes index previous (by exact below.trans inRam)
  have panicOff := remap_below_ram layout layout.panic index (by dsimp [layout]; omega) inRam
  have termOff := remap_below_ram layout layout.termination index (by dsimp [layout]; omega) inRam
  dsimp only [layout] at panicOff termOff
  unfold TraceWitness.finalRamWord
  dsimp only
  rw [fixed.1, fixed.2.1, fixed.2.2.1, fixed.2.2.2]
  rw [show (TraceWitness.remapRamAddress layout layout.termination == some index) = false from
    beq_eq_false_iff_ne.mpr termOff]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg panicOff]
  rw [overlays _ _ (by omega), overlays _ _ (by rw [inputsIs]; omega),
    overlays _ _ (by omega), overlays _ _ (by omega)]
  change (if RAM_START_ADDRESS ≤ ramLowestAddress layout + 8 * index then _ else _) = _
  rw [if_pos inRam]
  rfl

private theorem ordinary_index_ne_termination
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun inst inputs) (index : Nat)
    (inRam : RAM_START_ADDRESS ≤ ramLowestAddress run.initialState.jolt_device.memory_layout + 8 * index) :
    index ≠ (run.initialState.jolt_device.memory_layout.termination.toNat -
      ramLowestAddress run.initialState.jolt_device.memory_layout) / 8 := by
  have built := (initial_state_device inst inputs run.initialState run.initialized).1
  have order := new_io_ordered _ _ built
  have geometry := new_io_geometry _ _ built
  rw [MemoryLayout.get_lowest_address_toNat] at order
  change ramLowestAddress _ ≤ _ ∧ _ at order
  omega

/-- At an initialized run's cut, full image agreement outside termination is
exactly ordinary-RAM agreement together with device agreement.
For example, the split combines a program RAM word with an output word while
leaving the synthetic termination word to the stopping argument. -/
theorem ramAgreement_iff
    {F : Type} [Field F] {size : Nat}
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs} {params : WitnessParams}
    (context : ConstraintContext inst inputs params) (run : UntrustedAnswerRun inst inputs)
    (values : Fin size → F) :
    (∀ index, index.val ≠ (run.initialState.jolt_device.memory_layout.termination.toNat -
        ramLowestAddress run.initialState.jolt_device.memory_layout) / 8 →
      values index = ((TraceWitness.finalRamWord run.toTrace index.val).toNat : F)) ↔
    OrdinaryRamAgreement run.initialState.jolt_device.memory_layout values
      (TraceWitness.finalTraceState run.toTrace) ∧ DeviceRamAgreement values run.toTrace := by
  constructor
  · intro image
    refine ⟨?_, fun index _ outside => image index outside⟩
    intro index inRam
    rw [← finalRamWord_ordinary context run index.val inRam]
    exact image index (ordinary_index_ne_termination run index.val inRam)
  · rintro ⟨ram, device⟩ index outside
    by_cases inRam : RAM_START_ADDRESS ≤ ramLowestAddress run.initialState.jolt_device.memory_layout + 8 * index.val
    · rw [finalRamWord_ordinary context run index.val inRam]
      exact ram index inRam
    · exact device index (Nat.lt_of_not_ge inRam) outside

/-- An access in ordinary RAM leaves every device table word unchanged and
preserves conditional termination zero, while its ordinary-RAM update is supplied
by the load or store rule; for example, an SD in RAM cannot change an output word. -/
theorem ordinary_memory_step
    {F : Type} [Field F] (joltField : JoltField F) {params : WitnessParams}
    {inst : JoltInstance SourceInstruction} {inputs : JoltPrivateInputs}
    (witness : WitnessType F params) (context : ConstraintContext inst inputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io context.entry witness)
    (run : UntrustedAnswerRun inst inputs) (step : TraceRow run.bytecode) (t : Fin params.traceLength)
    (address : BitVec 64) (encoded : witness.RamAddress t = (address.toNat : F))
    (inRam : RAM_START_ADDRESS ≤ address.toNat)
    (device : DeviceRamAgreement (fun index => witness.RamVal index t) run.toTrace)
    (termination : (¬ ∃ i : Fin run.rows.size, run.StoresTerminationAt i) →
      TerminationTableZero run.initialState.jolt_device.memory_layout (fun index => witness.RamVal index t))
    (sameDevice : step.postState.jolt_device = (TraceWitness.finalTraceState run.toTrace).jolt_device)
    (ramNext : ∀ next : t.val + 1 < params.traceLength,
      OrdinaryRamAgreement context.io.memory_layout
        (fun index => witness.RamVal index ⟨t.val + 1, next⟩) step.postState)
    (ramFinal : ∀ last : t.val + 1 = params.traceLength,
      OrdinaryRamAgreement context.io.memory_layout witness.RamValFinal step.postState) :
    DeviceMemoryStepAgreement witness t run.toTrace step
      (∃ i : Fin run.rows.size, run.StoresTerminationAt i) := by
  have layoutEq := initial_state_memory_layout context run.initialized
  have zero (index : Fin params.ramSize)
      (below : ramLowestAddress run.initialState.jolt_device.memory_layout + 8 * index.val < RAM_START_ADDRESS) :
      witness.RamRa index t * witness.RamInc t = 0 := by
    rcases ramRa_zero_or_one context equations index t with zero | one
    · rw [zero, zero_mul]
    · have atIndex := ramAddress_eq_of_selected (two_pow_127_lt_char joltField)
        context equations t index one address encoded
      rw [← layoutEq] at atIndex
      omega
  have nextSame (next : t.val + 1 < params.traceLength) (index : Fin params.ramSize)
      (below : ramLowestAddress run.initialState.jolt_device.memory_layout + 8 * index.val < RAM_START_ADDRESS) :
      witness.RamVal index ⟨t.val + 1, next⟩ = witness.RamVal index t := by
    rw [ramVal_succ equations.ramValEqInitialPlusPrefixRamInc index t next, zero index below, add_zero]
  have finalSame (last : t.val + 1 = params.traceLength) (index : Fin params.ramSize)
      (below : ramLowestAddress run.initialState.jolt_device.memory_layout + 8 * index.val < RAM_START_ADDRESS) :
      witness.RamValFinal index = witness.RamVal index t := by
    rw [ramValFinal_eq_last_update equations.ramValEqInitialPlusPrefixRamInc
      equations.ramValFinalEqInitialPlusRamInc index t last, zero index below, add_zero]
  have imageSame (index : Nat)
      (below : ramLowestAddress run.initialState.jolt_device.memory_layout + 8 * index < RAM_START_ADDRESS) :
      TraceWitness.finalRamWord {run.toTrace with rows := run.rows.push step} index =
        TraceWitness.finalRamWord run.toTrace index := by
    unfold ramLowestAddress at below
    simp only [TraceWitness.finalRamWord, finalTraceState_push, sameDevice, if_neg (Nat.not_le.mpr below)]
  constructor
  · intro next
    refine ⟨by rw [layoutEq]; exact ramNext next, ?_, ?_⟩
    · intro index below outside
      dsimp only
      rw [nextSame next index below, imageSame index.val below]
      exact device index below outside
    · intro noStore index atTermination
      have below : ramLowestAddress run.initialState.jolt_device.memory_layout + 8 * index.val < RAM_START_ADDRESS := by
        by_contra h
        exact ordinary_index_ne_termination run index.val (Nat.le_of_not_gt h) atTermination
      dsimp only
      rw [nextSame next index below]
      exact termination noStore index atTermination
  · intro last
    refine ⟨by rw [layoutEq]; exact ramFinal last, ?_⟩
    intro index below outside
    rw [finalSame last index below, imageSame index.val below]
    exact device index below outside

end JoltInstance
