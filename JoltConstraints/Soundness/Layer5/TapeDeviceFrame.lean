import JoltConstraints.Soundness.Layer5.TapeTrace
import JoltConstraints.Completeness.Helpers.IOSetupFrame
import JoltConstraints.layout_facts

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- A relaxed-answer trace carries any reflexive, transitive device relation
preserved by successful device byte stores to its final state. -/
theorem UntrustedAnswerTrace.device_relation
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerTrace joltInstance privateInputs)
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (store : ∀ io io' address value,
      JoltDevice.store? io address value = some io' → relation io io') :
    relation trace.initialState.jolt_device
      (TraceWitness.finalTraceState trace).jolt_device := by
  have startsDevice : ∀ first, trace.rows[0]? = some first →
      first.preState.jolt_device = trace.initialState.jolt_device := by
    intro first firstIs
    obtain ⟨_, _, firstState⟩ := trace.starts first firstIs
    rw [firstState]
    rfl
  have linkedDevice : ∀ i current next,
      trace.rows[i]? = some current → trace.rows[i + 1]? = some next →
      next.preState.jolt_device = current.postState.jolt_device := by
    intro i current next currentIs nextIs
    have link := trace.linked i current next currentIs nextIs
    split at link
    · exact congrArg SailJoltState.jolt_device link.2
    · obtain ⟨_, _, _, _, nextState⟩ := link
      rw [nextState]
      rfl
  have preserved : ∀ step : Fin trace.rows.size,
      relation (trace.rows[step]).preState.jolt_device
        (trace.rows[step]).postState.jolt_device := by
    intro step
    exact execWithTapeAnswer_rule_of_device_relation relation refl trans store
      (trace.bytecode[trace.rows[step].rowIndex].instruction.withRuntimeAdvice
        trace.rows[step].runtimeAdvice) (trace.answers step) _ _ _ (trace.executes step)
  exact Trace.finalTraceState_device_relation trace relation refl trans startsDevice
    linkedDevice preserved

/-- A relaxed-answer trace keeps its initial layout, inputs and advice buffers
in the final device. -/
theorem UntrustedAnswerTrace.final_device_same
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerTrace joltInstance privateInputs) :
    JoltIOSetupFrame.Same trace.initialState.jolt_device
      (TraceWitness.finalTraceState trace).jolt_device := by
  exact UntrustedAnswerTrace.device_relation trace JoltIOSetupFrame.Same
    JoltIOSetupFrame.Same.refl
    (fun _ _ _ first next => first.trans next) JoltIOSetupFrame.storeDeviceByte_same

/-- The final output byte count of a relaxed-answer trace is at most its
initial layout's `max_output_size.toNat`. -/
theorem UntrustedAnswerTrace.final_outputs_fit_layout
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerTrace joltInstance privateInputs) :
    (TraceWitness.finalTraceState trace).jolt_device.outputs.size ≤
      trace.initialState.jolt_device.memory_layout.max_output_size.toNat := by
  let layout := trace.initialState.jolt_device.memory_layout
  let config := { joltInstance.memory_config with
    program_size := some joltInstance.program.program_size }
  have built : MemoryLayout.new config = some layout :=
    (initial_state_device joltInstance privateInputs trace.initialState trace.initialized).1
  obtain ⟨outputSpan, _, _, _, _⟩ :=
    new_io_geometry config layout built
  let Fits (io : JoltDevice) : Prop :=
    io.memory_layout = layout ∧ io.outputs.size ≤ layout.max_output_size.toNat
  let Rel (a b : JoltDevice) : Prop := Fits a → Fits b
  have refl (io : JoltDevice) : Rel io io := fun fits => fits
  have trans (a b c : JoltDevice) (ab : Rel a b) (bc : Rel b c) :
      Rel a c := fun fits => bc (ab fits)
  have store (io io' : JoltDevice) (address : Nat) (value : BitVec 8)
      (stored : io.store? address value = some io') : Rel io io' := by
    intro fits
    exact JoltIOSetupFrame.storeDeviceByte_outputs_fit layout outputSpan
      io io' address value fits.1 fits.2 stored
  have initialEmpty : trace.initialState.jolt_device.outputs = #[] := by
    have initialized := trace.initialized
    unfold JoltInstance.initial_state at initialized
    rw [bind_some_iff] at initialized
    obtain ⟨_, _, initialized⟩ := initialized
    dsimp only at initialized
    split at initialized
    · cases initialized
    rw [bind_some_iff] at initialized
    obtain ⟨_, _, initialized⟩ := initialized
    split at initialized
    · cases initialized
    rw [bind_some_iff] at initialized
    obtain ⟨_, _, initialized⟩ := initialized
    split at initialized
    · cases initialized
    rw [bind_some_iff] at initialized
    obtain ⟨_, _, initialized⟩ := initialized
    have stateEq := Option.some.inj initialized
    rw [← stateEq]
    rw [init_state_jolt_device]
  have initialFits : Fits trace.initialState.jolt_device :=
    ⟨rfl, by simp [initialEmpty]⟩
  have finalRel : Rel trace.initialState.jolt_device
      (TraceWitness.finalTraceState trace).jolt_device :=
    UntrustedAnswerTrace.device_relation trace Rel refl trans store
  exact (finalRel initialFits).2

end JoltConstraints.Soundness
