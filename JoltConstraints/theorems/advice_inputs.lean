import JoltConstraints.translation.Constraints.All
import JoltConstraints.theorems.layout_facts

open LeanRV64D

set_option autoImplicit false

-- Replacing the execution tape changes only the tape in the initial state.
theorem JoltInstance.initial_state_with_advice_tape {Source : Type}
    (joltInstance : JoltInstance Source) (privateInputs : JoltPrivateInputs)
    (tape : Array (BitVec 8)) :
    joltInstance.initial_state { privateInputs with advice_tape := tape } =
      (joltInstance.initial_state privateInputs).map
        (fun state => { state with adviceTape := { bytes := tape, readPosition := 0 } }) := by
  unfold JoltInstance.initial_state
  cases joltInstance.memory_layout with
  | none => rfl
  | some layout =>
    dsimp only [Option.bind_some]
    split_ifs <;> try rfl
    exact JoltConstraints.initialState_with_adviceTape
      (init_state joltInstance.program.entry_address
        (initialRam layout joltInstance.program.memory_init)
        { panic := false, memory_layout := layout }
        { bytes := privateInputs.advice_tape, readPosition := 0 })
      _ _ _ _ { bytes := tape, readPosition := 0 }

-- A successful initialization starts the execution tape at its first byte.
theorem JoltInstance.initial_state_adviceTape_readPosition_zero {Source : Type}
    (joltInstance : JoltInstance Source) (privateInputs : JoltPrivateInputs)
    (state : SailJoltState)
    (initialized : joltInstance.initial_state privateInputs = some state) :
    state.adviceTape.readPosition = 0 := by
  obtain ⟨_, _, _, _, _, built⟩ := initial_state_build joltInstance privateInputs state initialized
  obtain ⟨_, _, _, _, shape⟩ := JoltConstraints.initialState_shape _ _ _ _ _ _ built
  rw [shape]
  rfl

namespace JoltConstraints

-- The context binds the same RAM words after changing the execution tape.
noncomputable def ConstraintContext.withAdviceTape
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams} (context : ConstraintContext joltInstance privateInputs params)
    (tape : Array (BitVec 8)) :
    ConstraintContext joltInstance { privateInputs with advice_tape := tape } params :=
  { context with
    initialized := by
      obtain ⟨state, initialized, ram⟩ := context.initialized
      refine ⟨{ state with adviceTape := { bytes := tape, readPosition := 0 } }, ?_, ?_⟩
      · rw [JoltInstance.initial_state_with_advice_tape, initialized]
        rfl
      · exact ram }

-- The relation cannot distinguish two choices of execution tape. This is an
-- invariance result; it does not establish that any satisfying witness admits
-- an execution consistent with a single tape. That is a soundness obligation.
theorem AllConstraints.advice_tape_irrelevant {F : Type} [Field F] {params : WitnessParams}
    (joltInstance : JoltInstance SourceInstruction) (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) (tape : Array (BitVec 8)) :
    AllConstraints joltInstance { privateInputs with advice_tape := tape } witness ↔
      AllConstraints joltInstance privateInputs witness := by
  constructor
  · rintro ⟨context, equations⟩
    refine ⟨context.withAdviceTape privateInputs.advice_tape, equations⟩
  · rintro ⟨context, equations⟩
    exact ⟨context.withAdviceTape tape, equations⟩

end JoltConstraints
