import JoltConstraints.honest_witness
import JoltConstraints.Constraints.RamReadData
import JoltBytecode.InstructionEquivalence.ProofSupport.DeviceFrame

/-!
Execution never changes the device fields fixed when Rust builds its emulator:
the memory layout, the inputs and both advice buffers. Sail steps do not touch the device,
device stores only change `outputs` and `panic`, and HostIO only appends to the
advice tape. The trace-level result carries this from the program's initial
state to the final recorded state.
-/

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions


namespace JoltConstraints

open JoltIOSetupFrame

/-- Carry a device relation from a plain trace's initial state to every
recorded row's pre-state using the start, linkage and per-row preservation facts. -/
theorem Trace.preState_device_relation (trace : Trace)
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (starts : ∀ first, trace.rows[0]? = some first →
      first.preState.jolt_device = trace.initialState.jolt_device)
    (linked : ∀ i current next,
      trace.rows[i]? = some current → trace.rows[i + 1]? = some next →
      next.preState.jolt_device = current.postState.jolt_device)
    (preserved : ∀ step : Fin trace.rows.size,
      relation (trace.rows[step]).preState.jolt_device
        (trace.rows[step]).postState.jolt_device)
    (i : Nat) (hi : i < trace.rows.size) :
    relation trace.initialState.jolt_device (trace.rows[i]).preState.jolt_device := by
  induction i with
  | zero =>
    have first := starts (trace.rows[0])
      (Array.getElem?_eq_getElem hi)
    rw [first]
    exact refl _
  | succ n ih =>
    have currentIs : trace.rows[n]? = some (trace.rows[n]'(by omega)) :=
      Array.getElem?_eq_getElem (by omega)
    have nextIs : trace.rows[n + 1]? = some (trace.rows[n + 1]'hi) :=
      Array.getElem?_eq_getElem hi
    have step := preserved ⟨n, by omega⟩
    have link := linked n _ _ currentIs nextIs
    rw [link]
    exact trans _ _ _ (ih (by omega)) step

/-- Carry a device relation from a plain trace's initial state to its final
state using its first-row, row-linkage and execution facts. -/
theorem Trace.finalTraceState_device_relation (trace : Trace)
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (starts : ∀ first, trace.rows[0]? = some first →
      first.preState.jolt_device = trace.initialState.jolt_device)
    (linked : ∀ i current next,
      trace.rows[i]? = some current → trace.rows[i + 1]? = some next →
      next.preState.jolt_device = current.postState.jolt_device)
    (preserved : ∀ step : Fin trace.rows.size,
      relation (trace.rows[step]).preState.jolt_device
        (trace.rows[step]).postState.jolt_device) :
    relation trace.initialState.jolt_device
      (TraceWitness.finalTraceState trace).jolt_device := by
  unfold TraceWitness.finalTraceState
  split
  · rename_i nonempty
    exact trans _ _ _
      (Trace.preState_device_relation trace relation refl trans starts linked preserved
        (trace.rows.size - 1) (by omega))
      (preserved ⟨trace.rows.size - 1, by omega⟩)
  · exact refl _

/-- An honest fixed-tape trace carries any reflexive, transitive device
relation preserved by successful device byte stores to every pre-state and
to the final state. -/
theorem HonestTrace.device_relation
    {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    (relation : JoltDevice → JoltDevice → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (store : ∀ io io' address value,
      JoltDevice.store? io address value = some io' → relation io io') :
    (∀ (i : Nat) (hi : i < trace.rows.size),
      relation trace.initialState.jolt_device (trace.rows[i]).preState.jolt_device) ∧
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
    exact JoltIOSetupFrame.execInstr_rule_of_device_relation relation refl trans store
      (trace.bytecode[trace.rows[step].rowIndex].instruction.withRuntimeAdvice
        trace.rows[step].runtimeAdvice) _ _ _
      (trace.executes trace.rows[step] (Array.getElem_mem step.isLt))
  exact ⟨Trace.preState_device_relation trace relation refl trans startsDevice
    linkedDevice preserved,
    Trace.finalTraceState_device_relation trace relation refl trans startsDevice
      linkedDevice preserved⟩

/-- Every recorded pre-state has the program's initial device setup. -/
theorem trace_preState_ioSame {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (hi : i < trace.rows.size) :
    Same trace.initialState.jolt_device (getElem trace.rows i hi).preState.jolt_device := by
  exact (HonestTrace.device_relation trace Same Same.refl
    (fun _ _ _ first next => first.trans next) storeDeviceByte_same).1 i hi

/-- The final recorded state has the program's initial device setup. -/
theorem finalTraceState_ioSame {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    Same trace.initialState.jolt_device (TraceWitness.finalTraceState trace).jolt_device := by
  exact (HonestTrace.device_relation trace Same Same.refl
    (fun _ _ _ first next => first.trans next) storeDeviceByte_same).2

end JoltConstraints
