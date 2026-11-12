import JoltConstraints.Constraints.All
import JoltConstraints.layout_facts

open LeanRV64D

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

-- A successful initialization starts the execution tape at its first byte.
theorem JoltInstance.initial_state_adviceTape_readPosition_zero {Source : Type}
    (joltInstance : JoltInstance Source) (privateInputs : JoltPrivateInputs)
    (state : SailJoltState)
    (initialized : joltInstance.initial_state privateInputs = some state) :
    state.adviceTape.readPosition = 0 := by
  unfold JoltInstance.initial_state at initialized
  cases layout : joltInstance.memory_layout with
  | none => simp [layout] at initialized
  | some layout =>
      simp only [layout] at initialized
      split_ifs at initialized <;> simp_all [init_state]
      simpa using congrArg (fun state : SailJoltState =>
        state.adviceTape.readPosition) initialized.symm

/-- Replacing the untrusted advice by bytes that pass the tracer's size check changes only
the untrusted advice in the starting device: the Sail state, the execution tape and every
other device field stay the same. For example, with a configured maximum of 16 bytes,
replacing 3 advice bytes by 16 zero bytes gives the same Sail state.
See `jolt/tracer/src/lib.rs` (`create_emulator`). -/
theorem JoltInstance.initial_state_with_untrusted_advice {Source : Type}
    (joltInstance : JoltInstance Source) (privateInputs : JoltPrivateInputs)
    (bytes : Array (BitVec 8))
    (fits : bytes.size ≤ joltInstance.memory_config.max_untrusted_advice_size.toNat)
    (state : SailJoltState)
    (initialized : joltInstance.initial_state privateInputs = some state) :
    ∃ state' : SailJoltState,
      joltInstance.initial_state { privateInputs with untrusted_advice := bytes } =
        some state' ∧
      state'.sail = state.sail ∧ state'.adviceTape = state.adviceTape ∧
      state'.jolt_device = { state.jolt_device with untrusted_advice := bytes } := by
  unfold JoltInstance.initial_state at initialized ⊢
  cases layout : joltInstance.memory_layout with
  | none => simp [layout] at initialized
  | some layout =>
    simp only [layout] at initialized ⊢
    by_cases trusted : joltInstance.memory_config.max_trusted_advice_size.toNat <
      joltInstance.trusted_advice.size
    · simp [trusted] at initialized
    by_cases untrusted : joltInstance.memory_config.max_untrusted_advice_size.toNat <
      privateInputs.untrusted_advice.size
    · simp [untrusted] at initialized
    by_cases inputs : joltInstance.memory_config.max_input_size.toNat <
      joltInstance.inputs.size
    · simp [inputs] at initialized
    have notBytes := Nat.not_lt.mpr fits
    simp only [trusted, untrusted, inputs, notBytes, ite_false] at initialized ⊢
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
      at initialized ⊢
    subst initialized
    exact ⟨_, rfl, rfl, rfl, rfl⟩

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

/-- The context binds the same RAM words after changing the inline advice words, because
initialization does not read them. For example, a context for `inline_advice = #[]` is
also one for `inline_advice = #[5]`. -/
def ConstraintContext.withInlineAdvice
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams} (context : ConstraintContext joltInstance privateInputs params)
    (words : Array (BitVec 64)) :
    ConstraintContext joltInstance { privateInputs with inline_advice := words } params :=
  { context with initialized := context.initialized }

-- The relation cannot distinguish two choices of execution tape. This is an
-- invariance result; it does not establish that any satisfying witness admits
-- an execution consistent with a single tape. That is a soundness obligation.
theorem AllConstraintsOnBytes.advice_tape_irrelevant {F : Type} [Field F]
    {params : WitnessParams}
    (joltInstance : JoltInstance SourceInstruction) (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) (tape : Array (BitVec 8)) :
    AllConstraintsOnBytes joltInstance { privateInputs with advice_tape := tape } witness ↔
      AllConstraintsOnBytes joltInstance privateInputs witness := by
  constructor
  · rintro ⟨context, equations⟩
    refine ⟨context.withAdviceTape privateInputs.advice_tape, equations⟩
  · rintro ⟨context, equations⟩
    exact ⟨context.withAdviceTape tape, equations⟩

/-- The relation cannot distinguish two choices of inline advice words, because
initialization does not read them. For example, a witness satisfies the relation for
`inline_advice = #[]` exactly when it does for `inline_advice = #[5]`.
`AllConstraints` takes no private inputs, so this is the form in which the constraints
ignore `inline_advice`. -/
theorem AllConstraintsOnBytes.inline_advice_irrelevant {F : Type} [Field F]
    {params : WitnessParams}
    (joltInstance : JoltInstance SourceInstruction) (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) (words : Array (BitVec 64)) :
    AllConstraintsOnBytes joltInstance { privateInputs with inline_advice := words } witness ↔
      AllConstraintsOnBytes joltInstance privateInputs witness := by
  constructor
  · rintro ⟨context, equations⟩
    exact ⟨context.withInlineAdvice privateInputs.inline_advice, equations⟩
  · rintro ⟨context, equations⟩
    exact ⟨context.withInlineAdvice words, equations⟩

/-- The untrusted-advice words of a 64-bit initial RAM: word `index` of the
untrusted-advice block, cast into the field. For example, if `untrusted_advice_start`
remaps to word 100, then `adviceBlockWords layout initialRam 1` is the field cast of
`initialRam 101`. If `untrusted_advice_start` does not remap, every word is zero. -/
noncomputable def adviceBlockWords {F : Type} [Field F] (layout : MemoryLayout)
    (initialRam : Nat → BitVec 64) (index : Nat) : F :=
  match TraceWitness.remapRamAddress layout layout.untrusted_advice_start with
  | none => 0
  | some first => ramInitialValue initialRam (first + index)

/-- Outside the untrusted-advice block, the untrusted-advice overlay
(`TraceWitness.overlayRamBytes` at `untrusted_advice_start`) keeps the previous word, for
any advice that fits the block. The block is the `max_untrusted_advice_size / 8` words
from the remapped `untrusted_advice_start` (`untrustedAdviceWordIndex?`). For example,
with a 16-byte block at remapped word 100, the overlay keeps word 102. -/
theorem overlay_untrusted_outside (layout : MemoryLayout)
    (aligned : layout.max_untrusted_advice_size.toNat % 8 = 0)
    (bytes : Array (BitVec 8)) (small : bytes.size ≤ layout.max_untrusted_advice_size.toNat)
    {address : Nat} (outside : untrustedAdviceWordIndex? layout address = none)
    (previous : BitVec 64) :
    TraceWitness.overlayRamBytes layout layout.untrusted_advice_start bytes address previous =
      previous := by
  unfold TraceWitness.overlayRamBytes
  unfold untrustedAdviceWordIndex? at outside
  cases firstIs : TraceWitness.remapRamAddress layout layout.untrusted_advice_start with
  | none => rfl
  | some first =>
    rw [firstIs] at outside
    dsimp only at outside ⊢
    apply ite_eq_right
    split_ifs at outside with inBlock
    omega

/-- Outside the untrusted-advice block, the initial RAM word
(`TraceWitness.initialRamWordFromState`) does not depend on the untrusted advice: two
states that differ only in their untrusted-advice bytes, both within the block, agree on
every word outside it. For example, a program word below the block is the same for empty
advice and for 16 bytes of advice. -/
theorem initialRamWordFromState_outside_untrustedAdvice (state state' : SailJoltState)
    (bytes : Array (BitVec 8))
    (sail : state'.sail = state.sail)
    (device : state'.jolt_device = { state.jolt_device with untrusted_advice := bytes })
    (aligned : state.jolt_device.memory_layout.max_untrusted_advice_size.toNat % 8 = 0)
    (small : state.jolt_device.untrusted_advice.size ≤
      state.jolt_device.memory_layout.max_untrusted_advice_size.toNat)
    (small' : bytes.size ≤ state.jolt_device.memory_layout.max_untrusted_advice_size.toNat)
    {address : Nat}
    (outside : untrustedAdviceWordIndex? state.jolt_device.memory_layout address = none) :
    TraceWitness.initialRamWordFromState state' address =
      TraceWitness.initialRamWordFromState state address := by
  unfold TraceWitness.initialRamWordFromState
  rw [sail, device]
  dsimp only
  rw [overlay_untrusted_outside _ aligned bytes small' outside,
    overlay_untrusted_outside _ aligned _ small outside]

/-- The actual initializer and the constraint context use the same RAM layout,
so their remapping bases and device regions agree. Here `initialState` is the state that
`joltInstance.initial_state` builds from the private inputs of `context`. For example,
both see the same `untrusted_advice_start`, so the untrusted-advice block of the run is
the block the constraints use. -/
theorem Soundness.initial_state_memory_layout
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {params : WitnessParams} (context : ConstraintContext joltInstance privateInputs params)
    {initialState : SailJoltState}
    (built : joltInstance.initial_state privateInputs = some initialState) :
    initialState.jolt_device.memory_layout = context.io.memory_layout := by
  have initialLayout := (initial_state_device joltInstance privateInputs initialState built).1
  have publicIo := context.publicIo
  unfold JoltInstance.public_io at publicIo
  obtain ⟨layout, hasLayout, sameIo⟩ := Option.bind_eq_some_iff.mp publicIo
  have publicLayout : layout = context.io.memory_layout :=
    congrArg JoltDevice.memory_layout (Option.some.inj sameIo)
  have same : layout = initialState.jolt_device.memory_layout :=
    Option.some.inj (hasLayout.symm.trans initialLayout)
  exact same.symm.trans publicLayout

/-- The byte relation gives the relation Jolt's verifier checks: commit to the words of
the untrusted-advice block of the context's initial RAM.
For example, an honest run's witness satisfies `AllConstraints` with the words of its
initial RAM. -/
theorem allConstraints_of_onBytes {F : Type} [Field F] {params : WitnessParams}
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    {witness : WitnessType F params}
    (context : ConstraintContext joltInstance privateInputs params)
    (equations : ConstraintEquations context.bytecode context.initialRam context.io
      context.entry witness) :
    AllConstraints joltInstance (adviceBlockWords context.io.memory_layout context.initialRam)
      witness := by
  obtain ⟨state, initialized, ramIs⟩ := context.initialized
  obtain ⟨layoutBuilt, -, untrustedIs, -, untrustedFits⟩ :=
    initial_state_device joltInstance privateInputs state initialized
  have layoutEq := (Soundness.initial_state_memory_layout context initialized).symm
  obtain ⟨-, -, configFits, aligned, -⟩ := new_advice_regions _ _ layoutBuilt
  -- drop the untrusted advice, then the execution tape
  obtain ⟨state', built', sail, -, device⟩ :=
    joltInstance.initial_state_with_untrusted_advice privateInputs #[] (by simp) state
      initialized
  have built'' : joltInstance.initial_state JoltPrivateInputs.noUntrustedAdvice =
      some { state' with adviceTape := { bytes := #[], readPosition := 0 } } := by
    have dropTape := joltInstance.initial_state_with_advice_tape
      { privateInputs with untrusted_advice := #[] } #[]
    rw [built'] at dropTape
    exact dropTape
  refine ⟨{ context with
    initialRam := TraceWitness.initialRamWordFromState
      { state' with adviceTape := { bytes := #[], readPosition := 0 } }
    initialized := ⟨_, built'', rfl⟩ }, ?_⟩
  have same : committedInitialValue (F := F) context.io.memory_layout
      (TraceWitness.initialRamWordFromState
        { state' with adviceTape := { bytes := #[], readPosition := 0 } })
      (adviceBlockWords context.io.memory_layout context.initialRam) =
      ramInitialValue (F := F) context.initialRam := by
    funext address
    rw [layoutEq]
    unfold committedInitialValue
    cases indexIs : untrustedAdviceWordIndex? state.jolt_device.memory_layout address with
    | none =>
      dsimp only
      unfold ramInitialValue
      rw [ramIs, initialRamWordFromState_outside_untrustedAdvice state
        { state' with adviceTape := { bytes := #[], readPosition := 0 } } #[] sail device
        aligned (by rw [untrustedIs]; exact untrustedFits.trans configFits) (by simp)
        indexIs]
    | some index =>
      dsimp only
      unfold untrustedAdviceWordIndex? at indexIs
      unfold adviceBlockWords
      cases firstIs : TraceWitness.remapRamAddress state.jolt_device.memory_layout
          state.jolt_device.memory_layout.untrusted_advice_start with
      | none => simp only [firstIs, reduceCtorEq] at indexIs
      | some first =>
        rw [firstIs] at indexIs
        dsimp only at indexIs ⊢
        split_ifs at indexIs with inBlock
        · simp only [Option.some.injEq] at indexIs
          subst indexIs
          rw [Nat.add_sub_cancel' inBlock.1]
  change FieldConstraintEquations context.bytecode
    (committedInitialValue (F := F) context.io.memory_layout
      (TraceWitness.initialRamWordFromState
        { state' with adviceTape := { bytes := #[], readPosition := 0 } })
      (adviceBlockWords context.io.memory_layout context.initialRam))
    context.io context.entry witness
  rw [same]
  exact equations

end JoltConstraints
