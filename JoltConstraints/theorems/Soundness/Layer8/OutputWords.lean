import JoltConstraints.theorems.Soundness.Layer5.TapeDeviceFrame
import JoltConstraints.theorems.Soundness.Layer3.Layout
import JoltConstraints.theorems.Completeness.Helpers.RamOutputProofHelpers

open LeanRV64D
set_option autoImplicit false
namespace JoltConstraints.Soundness

/-- The checked shared output words and the separately checked halt claim determine
language output matching.
For example, a panic run with bytes `[1, 0]` matches public bytes `[1]` and panic true.
Jolt at `ff6fc6568`: `PublicIoMemory::new` and `Cpu::halt`. -/
theorem public_words_determine_matches_outputs
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (trace : UntrustedAnswerTrace joltInstance privateInputs)
    (panicEq : ((TraceWitness.finalTraceState trace).halted == some .panic) = context.io.panic)
    (runPublicWord : ∀ address : Fin params.ramSize,
      (context.io.memory_layout.input_start.toNat - ramLowestAddress context.io.memory_layout) / 8 ≤
        address.val →
      address.val < (context.io.memory_layout.output_end.toNat - ramLowestAddress context.io.memory_layout) / 8 →
      TraceWitness.finalRamWord trace address.val = ramPublicIoWord context.io address.val) :
    trace.matches_outputs joltInstance := by
  let layout := trace.initialState.jolt_device.memory_layout
  let config := { joltInstance.memory_config with
    program_size := some joltInstance.program.program_size }
  have built : MemoryLayout.new config = some layout := by
    exact (initial_state_device joltInstance privateInputs
      trace.initialState trace.initialized).1
  have ioEq : context.io =
      { inputs := joltInstance.inputs, outputs := trimTrailingZeros joltInstance.outputs,
        panic := joltInstance.panic, memory_layout := layout } := by
    have h := context.publicIo
    simp [JoltInstance.public_io, JoltInstance.memory_layout, config, built] at h
    exact h.symm
  have valid := context.validInputs
  unfold JoltInstance.validate_inputs at valid
  have layoutBuilt : joltInstance.memory_layout = some layout := built
  rw [layoutBuilt] at valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
  have valid := valid.1
  have inputBound : joltInstance.inputs.size ≤ layout.max_input_size.toNat := valid.1.2
  have claimedBound : context.io.outputs.size ≤ layout.max_output_size.toNat := by
    have trimmedBound := (trimTrailingZeros_spec joltInstance.outputs).1
    rw [ioEq]
    dsimp only
    omega
  let low := ramLowestAddress layout
  let inputFirst := (layout.input_start.toNat - low) / 8
  let outputFirst := (layout.output_start.toNat - low) / 8
  let outputEnd := (layout.output_end.toNat - low) / 8
  obtain ⟨outputAfterInput, outputLength, outputBeforeRam⟩ := new_io_word_geometry config layout built
  rw [MemoryLayout.get_lowest_address_toNat] at outputAfterInput outputLength outputBeforeRam
  change outputFirst = inputFirst + layout.max_input_size.toNat / 8 at outputAfterInput
  change outputEnd = outputFirst + layout.max_output_size.toNat / 8 at outputLength
  change outputEnd < (JoltISA.RAM_START_ADDRESS - low) / 8 at outputBeforeRam
  have outputMultiple := (new_io_geometry config layout built).2.1
  have claimLayout : context.io.memory_layout = layout := by rw [ioEq]
  have ioCovered : (JoltISA.RAM_START_ADDRESS - low) / 8 ≤ params.ramSize := by
    simpa only [low, claimLayout] using public_io_words_fit_ram context
  have runLayout : (TraceWitness.finalTraceState trace).jolt_device.memory_layout = layout :=
    trace.final_device_same.1
  have claimInputBound : context.io.inputs.size ≤ layout.max_input_size.toNat := by
    rw [ioEq]
    exact inputBound
  let runOutputs := (TraceWitness.finalTraceState trace).jolt_device.outputsOf
    (TraceWitness.finalTraceState trace).sail.mem
  have outputByteEq : ∀ i < layout.max_output_size.toNat,
      runOutputs[i]?.getD 0 = context.io.outputs[i]?.getD 0 := by
    intro i hi
    let q := i / 8
    have hq : q < layout.max_output_size.toNat / 8 := by
      dsimp only [q]
      omega
    let address : Fin params.ramSize := ⟨outputFirst + q, by omega⟩
    have lower : (context.io.memory_layout.input_start.toNat - ramLowestAddress context.io.memory_layout) / 8 ≤
        address.val := by
      rw [claimLayout]
      change inputFirst ≤ outputFirst + q
      omega
    have upper : address.val <
        (context.io.memory_layout.output_end.toNat - ramLowestAddress context.io.memory_layout) / 8 := by
      rw [claimLayout]
      change outputFirst + q < outputEnd
      omega
    have wordEq := runPublicWord address lower upper
    have encodedEq : TraceWitness.ramImageWord (fun j => runOutputs[j]?.getD 0) (8 * q) =
        TraceWitness.ramImageWord (fun j => context.io.outputs[j]?.getD 0) (8 * q) := by
      exact (finalRamWord_output trace config layout built rfl runLayout q hq).symm.trans
        (wordEq.trans (ramPublicIoWord_output config layout built _ claimLayout claimInputBound q hq))
    have byteEq := TraceWitness.ramImageWord_injective_byte _ _ (8 * q) encodedEq
      (i % 8) (Nat.mod_lt _ (by decide))
    have indexEq : 8 * q + i % 8 = i := by dsimp only [q]; omega
    simpa only [indexEq] using byteEq
  have outputBound : runOutputs.size ≤ layout.max_output_size.toNat := by
    dsimp only [runOutputs]
    rw [JoltDevice.outputsOf_size, runLayout]
  have outputsMatch : trimTrailingZeros runOutputs = trimTrailingZeros joltInstance.outputs := by
    have h := trimTrailingZeros_of_padded_eq _ _
      layout.max_output_size.toNat outputBound claimedBound outputByteEq
    rw [ioEq] at h
    simpa only [trimTrailingZeros_idempotent] using h
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
