import JoltConstraints.Constraints.All
import JoltConstraints.layout_facts

set_option autoImplicit false

-- For one fixed instance, varying any prover input cannot change the trusted
-- advice loaded by initialization. ConstraintContext binds initial RAM to it.
theorem JoltInstance.initial_states_agree_on_trusted_advice {Source : Type}
    (joltInstance : JoltInstance Source) (a b : JoltPrivateInputs)
    (stateA stateB : SailJoltState)
    (initializedA : joltInstance.initial_state a = some stateA)
    (initializedB : joltInstance.initial_state b = some stateB) :
    stateA.jolt_device.trusted_advice = stateB.jolt_device.trusted_advice := by
  exact (initial_state_device joltInstance a stateA initializedA).2.1.trans
    (initial_state_device joltInstance b stateB initializedB).2.1.symm

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
    split_ifs <;> rfl

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
