import JoltConstraints.theorems.Soundness.Layer5.TapeTrace
import JoltConstraints.theorems.Completeness.Helpers.IOSetupFrame
import JoltConstraints.theorems.layout_facts

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints.Soundness

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

/-- An execution prefix carries any reflexive, transitive device relation
compatible with explicit halt updates.
For example, layout equality holds through stores and both halt kinds.
Jolt at `ff6fc6568`: `tracer/src/emulator/cpu.rs` (`Cpu::halt`, `Cpu::tick`). -/
theorem UntrustedAnswerRun.device_relation
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs)
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (halt : ∀ device kind,
      relation device { device with panic := (kind == JoltHaltKind.panic) }) :
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
    exact execWithTapeAnswer_device_relation relation refl trans halt
      (run.bytecode[run.rows[step].rowIndex].instruction.withRuntimeAdvice
        run.rows[step].runtimeAdvice) (run.answers step) _ _ _ (run.executes step)
  exact Trace.finalTraceState_device_relation run.toTrace relation refl trans startsDevice
    linkedDevice preserved


/-- An execution prefix preserves its initial memory layout.
For example, an output store updates shared bytes without changing the layout.
Jolt at `ff6fc6568`: `tracer/src/emulator/mmu.rs` (`store_doubleword`). -/
theorem UntrustedAnswerRun.final_device_same
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs) :
    JoltIOSetupFrame.Same run.initialState.jolt_device
      (TraceWitness.finalTraceState run.toTrace).jolt_device := by
  exact UntrustedAnswerRun.device_relation run JoltIOSetupFrame.Same
    JoltIOSetupFrame.Same.refl
    (fun _ _ _ first next => first.trans next) (fun _ _ => ⟨rfl⟩)


/-- Outputs extracted from final shared memory fit the initial output capacity.
For example, an untouched output window extracts zero bytes at every position.
Jolt at `ff6fc6568`: `common/src/jolt_device.rs` (`JoltDevice::outputs`). -/
theorem UntrustedAnswerRun.final_outputs_fit_layout
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (run : UntrustedAnswerRun joltInstance privateInputs) :
    ((TraceWitness.finalTraceState run.toTrace).jolt_device.outputsOf
      (TraceWitness.finalTraceState run.toTrace).sail.mem).size ≤
      run.initialState.jolt_device.memory_layout.max_output_size.toNat := by
  have fixed := run.final_device_same
  rw [JoltDevice.outputsOf_size, fixed.1]


/-- A relaxed-answer trace carries device relations compatible with both halts.
For example, its final layout equals its initial layout. -/
theorem UntrustedAnswerTrace.device_relation
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (trace : UntrustedAnswerTrace joltInstance privateInputs)
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (halt : ∀ device kind,
      relation device { device with panic := (kind == JoltHaltKind.panic) }) :
    relation trace.initialState.jolt_device
      (TraceWitness.finalTraceState trace).jolt_device := by
  exact trace.toUntrustedAnswerRun.device_relation relation refl trans halt


/-- A relaxed-answer trace keeps its initial layout.
For example, a panic halt changes the claim without changing output capacity. -/
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
    ((TraceWitness.finalTraceState trace).jolt_device.outputsOf
      (TraceWitness.finalTraceState trace).sail.mem).size ≤
      trace.initialState.jolt_device.memory_layout.max_output_size.toNat := by
  exact trace.toUntrustedAnswerRun.final_outputs_fit_layout

end JoltConstraints.Soundness
