import JoltConstraints.Soundness.Layer5.TapeTrace
import JoltConstraints.Completeness.Helpers.IOSetupFrame
import JoltConstraints.layout_facts

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail PreSail LeanRV64D.Functions JoltISA

/-- An execution prefix carries a reflexive, transitive relation on devices
from its initial device to its final device when every successful byte store
preserves the relation.
For example, equality of the input arrays holds even for an empty prefix.
See `jolt/common/src/jolt_device.rs` (`JoltDevice::store`) and
`jolt/tracer/src/emulator/cpu.rs` (`Cpu::tick`) at 5def437f. -/
theorem UntrustedAnswerRun.device_relation
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (store : ∀ io io' address value,
      JoltDevice.store? io address value = some io' → relation io io') :
    relation run.initialState.jolt_device
      (TraceWitness.finalTraceState run.toTrace).jolt_device := by
  have startsDevice : ∀ first, run.rows[0]? = some first →
      first.preState.jolt_device = run.initialState.jolt_device := by
    intro first firstIs
    obtain ⟨_, _, firstState⟩ := run.starts first firstIs
    rw [firstState]
    rfl
  have linkedDevice : ∀ i current next,
      run.rows[i]? = some current → run.rows[i + 1]? = some next →
      next.preState.jolt_device = current.postState.jolt_device := by
    intro i current next currentIs nextIs
    have link := run.linked i current next currentIs nextIs
    split at link
    · exact congrArg SailJoltState.jolt_device link.2
    · obtain ⟨_, _, _, _, nextState⟩ := link
      rw [nextState]
      rfl
  have preserved : ∀ step : Fin run.rows.size,
      relation (run.rows[step]).preState.jolt_device
        (run.rows[step]).postState.jolt_device := by
    intro step
    exact execWithTapeAnswer_rule_of_device_relation relation refl trans store
      (run.bytecode[run.rows[step].rowIndex].instruction.withRuntimeAdvice
        run.rows[step].runtimeAdvice) (run.answers step) _ _ _ (run.executes step)
  exact Trace.finalTraceState_device_relation run.toTrace relation refl trans startsDevice
    linkedDevice preserved


/-- An execution prefix preserves its initial memory layout, trusted and
untrusted advice arrays, and input array in its final device.
For example, an output store leaves the input array unchanged.
See `jolt/common/src/jolt_device.rs` (`JoltDevice::store`) at 5def437f. -/
theorem UntrustedAnswerRun.final_device_same
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs) :
    JoltIOSetupFrame.Same run.initialState.jolt_device
      (TraceWitness.finalTraceState run.toTrace).jolt_device := by
  exact UntrustedAnswerRun.device_relation run JoltIOSetupFrame.Same
    JoltIOSetupFrame.Same.refl
    (fun _ _ _ first next => first.trans next) JoltIOSetupFrame.storeDeviceByte_same


/-- An execution prefix's final output array fits within the output capacity
of its initial memory layout.
For example, extending an empty output array to its second word still respects
`max_output_size` when the device store succeeds.
See `jolt/common/src/jolt_device.rs` (`JoltDevice::store`, `MemoryLayout::try_new`)
at 5def437f. -/
theorem UntrustedAnswerRun.final_outputs_fit_layout
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs) :
    (TraceWitness.finalTraceState run.toTrace).jolt_device.outputs.size ≤
      run.initialState.jolt_device.memory_layout.max_output_size.toNat := by
  let layout := run.initialState.jolt_device.memory_layout
  let config := { joltInstance.memory_config with
    program_size := some joltInstance.program.program_size }
  have built : MemoryLayout.new config = some layout :=
    (initial_state_device joltInstance privateInputs run.initialState run.initialized).1
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
  have initialEmpty : run.initialState.jolt_device.outputs = #[] := by
    have initialized := run.initialized
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
  have initialFits : Fits run.initialState.jolt_device :=
    ⟨rfl, by simp [initialEmpty]⟩
  have finalRel : Rel run.initialState.jolt_device
      (TraceWitness.finalTraceState run.toTrace).jolt_device :=
    UntrustedAnswerRun.device_relation run Rel refl trans store
  exact (finalRel initialFits).2


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
  exact trace.toUntrustedAnswerRun.device_relation relation refl trans store


/-- A relaxed-answer trace keeps its initial layout, inputs and advice buffers
in the final device. -/
theorem UntrustedAnswerTrace.final_device_same
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerTrace joltInstance privateInputs) :
    JoltIOSetupFrame.Same trace.initialState.jolt_device
      (TraceWitness.finalTraceState trace).jolt_device := by
  exact trace.toUntrustedAnswerRun.final_device_same


/-- The final output byte count of a relaxed-answer trace is at most its
initial layout's `max_output_size.toNat`. -/
theorem UntrustedAnswerTrace.final_outputs_fit_layout
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerTrace joltInstance privateInputs) :
    (TraceWitness.finalTraceState trace).jolt_device.outputs.size ≤
      trace.initialState.jolt_device.memory_layout.max_output_size.toNat := by
  exact trace.toUntrustedAnswerRun.final_outputs_fit_layout

end JoltConstraints.Soundness
