import JoltConstraints.translation.honest_witness
import JoltConstraints.translation.Constraints.RamReadData
import JoltConstraints.theorems.DeviceFrame

open LeanRV64D

/-!
Execution preserves the checked memory layout.
Input, advice, output and gap bytes are in shared Sail memory, rather than device fields.
The halt primitive updates the device's panic claim.
The trace-level results carry a halt-compatible device relation from the initial state
through recorded rows to the final state.
-/

set_option autoImplicit false

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions


namespace JoltConstraints

open JoltIOSetupFrame

/-- Carry a relation on a state projection from a plain trace's initial state to every
recorded row's pre-state using the start, linkage and per-row preservation facts. -/
theorem Trace.preState_projection_relation {α : Type} (trace : Trace) (project : SailJoltState → α)
    (relation : α → α → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (starts : ∀ first, trace.rows[0]? = some first →
      (project first.preState) = (project trace.initialState))
    (linked : ∀ i current next,
      trace.rows[i]? = some current → trace.rows[i + 1]? = some next →
      (project next.preState) = (project current.postState))
    (preserved : ∀ step : Fin trace.rows.size,
      relation (project (trace.rows[step]).preState)
        (project (trace.rows[step]).postState))
    (i : Nat) (hi : i < trace.rows.size) :
    relation (project trace.initialState) (project (trace.rows[i]).preState) := by
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

/-- Carry a relation on a state projection from a plain trace's initial state to its final
state using its first-row, row-linkage and execution facts. -/
theorem Trace.finalTraceState_projection_relation {α : Type} (trace : Trace) (project : SailJoltState → α)
    (relation : α → α → Prop)
    (refl : ∀ io, relation io io)
    (trans : ∀ a b c, relation a b → relation b c → relation a c)
    (starts : ∀ first, trace.rows[0]? = some first →
      (project first.preState) = (project trace.initialState))
    (linked : ∀ i current next,
      trace.rows[i]? = some current → trace.rows[i + 1]? = some next →
      (project next.preState) = (project current.postState))
    (preserved : ∀ step : Fin trace.rows.size,
      relation (project (trace.rows[step]).preState)
        (project (trace.rows[step]).postState)) :
    relation (project trace.initialState)
      (project (TraceWitness.finalTraceState trace)) := by
  unfold TraceWitness.finalTraceState
  split
  · rename_i nonempty
    exact trans _ _ _
      (Trace.preState_projection_relation trace project relation refl trans starts linked preserved
        (trace.rows.size - 1) (by omega))
      (preserved ⟨trace.rows.size - 1, by omega⟩)
  · exact refl _

/-- Carry a device relation to each recorded pre-state.
For example, equality of memory layouts follows from row preservation and linkage. -/
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
    relation trace.initialState.jolt_device (trace.rows[i]).preState.jolt_device :=
  Trace.preState_projection_relation trace SailJoltState.jolt_device relation
    refl trans starts linked preserved i hi

/-- Carry a device relation to the final recorded state.
For example, stores and halts retain the initialized memory layout. -/
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
      (TraceWitness.finalTraceState trace).jolt_device :=
  Trace.finalTraceState_projection_relation trace SailJoltState.jolt_device relation
    refl trans starts linked preserved

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
    (halt : ∀ device kind,
      relation device { device with panic := (kind == JoltHaltKind.panic) }) :
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
    exact execInstr_device_relation relation refl trans halt
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
    (fun _ _ _ first next => first.trans next) (fun _ _ => ⟨rfl⟩)).1 i hi

/-- The final recorded state has the program's initial device setup. -/
theorem finalTraceState_ioSame {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    Same trace.initialState.jolt_device (TraceWitness.finalTraceState trace).jolt_device := by
  exact (HonestTrace.device_relation trace Same Same.refl
    (fun _ _ _ first next => first.trans next) (fun _ _ => ⟨rfl⟩)).2

end JoltConstraints
