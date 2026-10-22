import JoltConstraints.Soundness.Layer5.TapeDeviceFrame
import JoltConstraints.Soundness.Layer3.Layout
import JoltConstraints.Completeness.Helpers.RamOutputProofHelpers

set_option autoImplicit false

namespace JoltConstraints.Soundness

/-- Equality of the checked public I/O words determines the relaxed run's
trimmed outputs and panic flag.
The checked words have RAM indices from the input start up to
`RAM_START_ADDRESS`, excluding the termination word. -/
theorem public_words_determine_matches_outputs
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (trace : UntrustedAnswerTrace joltInstance privateInputs)
    (frame : JoltIOSetupFrame.Same trace.initialState.jolt_device
      (TraceWitness.finalTraceState trace).jolt_device)
    (outputBound : (TraceWitness.finalTraceState trace).jolt_device.outputs.size ≤
      trace.initialState.jolt_device.memory_layout.max_output_size.toNat)
    (runPublicWord : ∀ address : Fin params.ramSize,
      (trace.initialState.jolt_device.memory_layout.input_start.toNat -
        JoltConstraints.ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 ≤
          address.val →
      address.val < (JoltISA.RAM_START_ADDRESS -
        JoltConstraints.ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 →
      address.val ≠
        (trace.initialState.jolt_device.memory_layout.termination.toNat -
          JoltConstraints.ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 →
      JoltConstraints.ramPublicIoWord
        (TraceWitness.finalTraceState trace).jolt_device address.val =
      JoltConstraints.ramPublicIoWord context.io address.val) :
    trace.matches_outputs joltInstance := by
  let layout := trace.initialState.jolt_device.memory_layout
  let config := { joltInstance.memory_config with
    program_size := some joltInstance.program.program_size }
  have built : MemoryLayout.new config = some layout := by
    exact (initial_state_device joltInstance privateInputs
      trace.initialState trace.initialized).1
  have ioEq : context.io =
      { inputs := joltInstance.inputs, trusted_advice := #[], untrusted_advice := #[],
        outputs := trimTrailingZeros joltInstance.outputs, panic := joltInstance.panic,
        memory_layout := layout } := by
    have h := context.publicIo
    simp [JoltInstance.public_io, JoltInstance.memory_layout, config, built] at h
    exact h.symm
  have valid := context.validInputs
  unfold JoltInstance.validate_inputs at valid
  have layoutBuilt : joltInstance.memory_layout = some layout := built
  rw [layoutBuilt] at valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
  have inputBound : joltInstance.inputs.size ≤ layout.max_input_size.toNat := valid.1.2
  have claimedBound : context.io.outputs.size ≤ layout.max_output_size.toNat := by
    have trimmedBound := (JoltConstraints.trimTrailingZeros_spec joltInstance.outputs).1
    rw [ioEq]
    dsimp only
    omega
  let low := JoltConstraints.ramLowestAddress layout
  let inputFirst := (layout.input_start.toNat - low) / 8
  let outputFirst := (layout.output_start.toNat - low) / 8
  let panicFirst := (layout.panic.toNat - low) / 8
  let terminationFirst := (layout.termination.toNat - low) / 8
  have ⟨outputAfterInput, outputBeforePanic, terminationAfterPanic,
      panicBeforeRam⟩ := new_io_word_geometry config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at outputAfterInput
  rw [MemoryLayout.get_lowest_address_toNat] at outputBeforePanic
  rw [MemoryLayout.get_lowest_address_toNat] at terminationAfterPanic
  rw [MemoryLayout.get_lowest_address_toNat] at panicBeforeRam
  change outputFirst = inputFirst + layout.max_input_size.toNat / 8 at outputAfterInput
  change panicFirst = outputFirst + layout.max_output_size.toNat / 8 at outputBeforePanic
  change terminationFirst = panicFirst + 1 at terminationAfterPanic
  change panicFirst < (JoltISA.RAM_START_ADDRESS - low) / 8 at panicBeforeRam
  have outputMultiple := (new_io_geometry config layout built).2.1
  have ioCovered : (JoltISA.RAM_START_ADDRESS - low) / 8 ≤ params.ramSize := by
    simpa only [low, show context.io.memory_layout = layout by rw [ioEq]] using
      public_io_words_fit_ram context
  have runLayout : (TraceWitness.finalTraceState trace).jolt_device.memory_layout =
      layout := frame.1
  have runInputs : (TraceWitness.finalTraceState trace).jolt_device.inputs =
      joltInstance.inputs := by
    exact frame.2.2.2.trans
      (initial_state_inputs joltInstance privateInputs trace.initialState trace.initialized)
  have claimLayout : context.io.memory_layout = layout := by rw [ioEq]
  have claimInputs : context.io.inputs = joltInstance.inputs := by rw [ioEq]
  have runInputBound :
      (TraceWitness.finalTraceState trace).jolt_device.inputs.size ≤
        layout.max_input_size.toNat := by rw [runInputs]; exact inputBound
  have claimInputBound : context.io.inputs.size ≤ layout.max_input_size.toNat := by
    rw [claimInputs]
    exact inputBound
  have outputByteEq : ∀ i < layout.max_output_size.toNat,
      (TraceWitness.finalTraceState trace).jolt_device.outputs[i]?.getD 0 =
        context.io.outputs[i]?.getD 0 := by
    intro i hi
    let q := i / 8
    have hq : q < layout.max_output_size.toNat / 8 := by
      dsimp only [q]
      omega
    let address : Fin params.ramSize := ⟨outputFirst + q, by omega⟩
    have lower :
        (trace.initialState.jolt_device.memory_layout.input_start.toNat -
          JoltConstraints.ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 ≤
          address.val := by
      change inputFirst ≤ outputFirst + q
      omega
    have upper : address.val <
        (JoltISA.RAM_START_ADDRESS -
          JoltConstraints.ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 := by
      change outputFirst + q < (JoltISA.RAM_START_ADDRESS - low) / 8
      omega
    have nonTermination : address.val ≠
        (trace.initialState.jolt_device.memory_layout.termination.toNat -
          JoltConstraints.ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 := by
      change outputFirst + q ≠ terminationFirst
      omega
    have wordEq := runPublicWord address lower upper nonTermination
    have encodedEq : TraceWitness.ramImageWord
        (fun j => (TraceWitness.finalTraceState trace).jolt_device.outputs[j]?.getD 0)
        (8 * q) = TraceWitness.ramImageWord
        (fun j => context.io.outputs[j]?.getD 0) (8 * q) := by
      simpa only [address] using
        (ramPublicIoWord_output config layout built _ runLayout runInputBound q hq).symm.trans
          (wordEq.trans
            (ramPublicIoWord_output config layout built _ claimLayout claimInputBound q hq))
    have byteEq := TraceWitness.ramImageWord_injective_byte _ _ (8 * q) encodedEq
      (i % 8) (Nat.mod_lt _ (by decide))
    have indexEq : 8 * q + i % 8 = i := by dsimp only [q]; omega
    simpa only [indexEq] using byteEq
  have outputsMatch : trimTrailingZeros
      (TraceWitness.finalTraceState trace).jolt_device.outputs =
        trimTrailingZeros joltInstance.outputs := by
    have h := JoltConstraints.trimTrailingZeros_of_padded_eq _ _
      layout.max_output_size.toNat outputBound claimedBound outputByteEq
    rw [ioEq] at h
    simpa only [JoltConstraints.trimTrailingZeros_idempotent] using h
  let panicAddress : Fin params.ramSize := ⟨panicFirst, by omega⟩
  have panicLower :
      (trace.initialState.jolt_device.memory_layout.input_start.toNat -
        JoltConstraints.ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 ≤
        panicAddress.val := by
    change inputFirst ≤ panicFirst
    omega
  have panicUpper : panicAddress.val <
      (JoltISA.RAM_START_ADDRESS -
        JoltConstraints.ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 :=
    panicBeforeRam
  have panicNonTermination : panicAddress.val ≠
      (trace.initialState.jolt_device.memory_layout.termination.toNat -
        JoltConstraints.ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 := by
    change panicFirst ≠ terminationFirst
    omega
  have panicWords := runPublicWord panicAddress panicLower panicUpper panicNonTermination
  have panicEq : (TraceWitness.finalTraceState trace).jolt_device.panic =
      context.io.panic := by
    have encoded : (if (TraceWitness.finalTraceState trace).jolt_device.panic then
        (1 : BitVec 64) else 0) = (if context.io.panic then 1 else 0) := by
      change JoltConstraints.ramPublicIoWord
          (TraceWitness.finalTraceState trace).jolt_device panicFirst =
        JoltConstraints.ramPublicIoWord context.io panicFirst at panicWords
      rw [ramPublicIoWord_panic config layout built _ runLayout,
        ramPublicIoWord_panic config layout built _ claimLayout] at panicWords
      exact panicWords
    cases hrun : (TraceWitness.finalTraceState trace).jolt_device.panic <;>
      cases hclaim : context.io.panic <;> simp [hrun, hclaim] at encoded ⊢
  have claimedPanic : context.io.panic = joltInstance.panic := by rw [ioEq]
  have finalEq : (trace.rows.back?.map (·.postState)).getD trace.initialState =
      TraceWitness.finalTraceState trace := by
    unfold TraceWitness.finalTraceState
    rw [Array.back?_eq_getElem?]
    split
    · rename_i nonempty
      rw [Array.getElem?_eq_getElem (by omega)]
      rfl
    · rw [Array.getElem?_eq_none (by omega)]
      rfl
  unfold Trace.matches_outputs
  rw [finalEq]
  exact ⟨outputsMatch, panicEq.trans claimedPanic⟩

end JoltConstraints.Soundness
