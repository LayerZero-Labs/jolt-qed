/-
The immediate obligations below `JoltInstance.soundness`. Each unfinished helper
has a name and a concrete statement so the main theorem can be assembled without
adding premises. See `JoltConstraints/model_review.md`, "Proofs owed".
-/
import JoltConstraints.Constraints.All
import JoltConstraints.Soundness.Assumptions
import JoltConstraints.Soundness.Layer0.Words
import JoltConstraints.Soundness.Layer5.PowerOfTwo
import JoltConstraints.Completeness.Helpers.RamOutputProofHelpers
import JoltConstraints.Completeness.All
import JoltConstraints.language
import JoltConstraints.Soundness.Layer5.TapeTrace
import JoltConstraints.Soundness.Layer6.PrefixAgreement
import JoltConstraints.Soundness.Layer7.Stopping
import JoltConstraints.Soundness.Layer8.OutputWords
import JoltConstraints.witness_helpers.pc
import JoltConstraints.witness_helpers.rs1_value
import JoltConstraints.witness_helpers.rs2_value
import JoltConstraints.witness_helpers.ram_address

set_option autoImplicit false

namespace JoltInstance

open Sail PreSail LeanRV64D.Functions JoltISA

/-- A. Reconstruct a relaxed-answer trace whose every executed row and every
nontermination final RAM word agrees with the witness. -/
theorem soundness_reconstruct_trace {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (assumptions : joltInstance.SoundnessAssumptions)
    (restrictions : joltInstance.TemporaryRestrictions)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness) :
    ∃ trace : JoltConstraints.Soundness.UntrustedAnswerTrace joltInstance privateInputs,
      trace.bytecode = context.bytecode ∧
        Represents witness trace.toUntrustedAnswerRun.toTrace := by
  obtain ⟨run, bytecodeEq, representedRows, realRows, noEarlierStop, cut, advice⟩ :=
    soundness_execution_prefix_agreement joltField joltInstance assumptions restrictions
      privateInputs witness context equations
  obtain ⟨stops, nonempty, finalRam⟩ :=
    soundness_stopping joltField joltInstance assumptions restrictions
      privateInputs witness context equations run bytecodeEq representedRows realRows
      noEarlierStop cut advice
  have accepted : joltInstance.bytecode.isSome := by
    obtain ⟨slots, preprocessed, entry⟩ := context.entryIsRust
    simp [JoltInstance.bytecode, context.expands, preprocessed, entry]
  let trace : JoltConstraints.Soundness.UntrustedAnswerTrace joltInstance privateInputs := {
    toUntrustedAnswerRun := run
    accepted := accepted
    valid_inputs := context.validInputs
    advice_from_honest_tracer := advice
    stops := stops
    runs_until_stop := noEarlierStop
    nonempty := nonempty
  }
  exact ⟨trace, bytecodeEq,
    { toRepresentsRows := representedRows.toRepresentsRows, finalRam := finalRam }⟩

/-- B. Constraint 26 checks the relaxed trace's output and panic words, while
`Represents.finalRam` connects those words to the witness. -/
theorem soundness_matches_outputs {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (trace : JoltConstraints.Soundness.UntrustedAnswerTrace joltInstance privateInputs)
    (represented : Represents witness trace.toUntrustedAnswerRun.toTrace) :
    trace.matches_outputs joltInstance := by
  have publicWord : ∀ address : Fin params.ramSize,
      (context.io.memory_layout.input_start.toNat -
        JoltConstraints.ramLowestAddress context.io.memory_layout) / 8 ≤ address.val →
      address.val < (JoltISA.RAM_START_ADDRESS -
        JoltConstraints.ramLowestAddress context.io.memory_layout) / 8 →
      address.val ≠
        (trace.initialState.jolt_device.memory_layout.termination.toNat -
          JoltConstraints.ramLowestAddress trace.initialState.jolt_device.memory_layout) / 8 →
      TraceWitness.finalRamWord trace address.val =
        JoltConstraints.ramPublicIoWord context.io address.val := by
    intro address lower upper nonTermination
    have checked := equations.ramOutputEqPublicIo address
    have selected : JoltConstraints.ramPublicIoMask (F := F) context.io address.val = 1 := by
      simp [JoltConstraints.ramPublicIoMask, lower, upper]
    rw [selected, one_mul] at checked
    have encoded : ((TraceWitness.finalRamWord trace address.val).toNat : F) =
        ((JoltConstraints.ramPublicIoWord context.io address.val).toNat : F) := by
      rw [← represented.finalRam address nonTermination]
      exact sub_eq_zero.mp checked
    exact JoltConstraints.Soundness.word_eq_of_field_eq
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField) encoded
  have initialLayout :=
    (initial_state_device joltInstance
      privateInputs trace.initialState trace.initialized).1
  have ioEq : context.io =
      { inputs := joltInstance.inputs, trusted_advice := #[], untrusted_advice := #[],
        outputs := trimTrailingZeros joltInstance.outputs, panic := joltInstance.panic,
        memory_layout := trace.initialState.jolt_device.memory_layout } := by
    have h := context.publicIo
    simp [JoltInstance.public_io, initialLayout] at h
    exact h.symm
  have layoutEq : context.io.memory_layout = trace.initialState.jolt_device.memory_layout := by
    rw [ioEq]
  have adviceBelowInput : trace.initialState.jolt_device.AdviceBelowInput := by
    obtain ⟨aligned, trustedBelow, untrustedBelow⟩ :=
      initial_state_advice_below_input joltInstance
        privateInputs trace.initialState trace.initialized
    rw [MemoryLayout.get_lowest_address_toNat] at aligned
    exact ⟨aligned, trustedBelow, untrustedBelow⟩
  have finalFrame := trace.final_device_same
  have runPublicWord : ∀ address : Fin params.ramSize,
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
        JoltConstraints.ramPublicIoWord context.io address.val := by
    intro address lower upper nonTermination
    have finalRamPublic : TraceWitness.finalRamWord trace address.val =
        JoltConstraints.ramPublicIoWord
          (TraceWitness.finalTraceState trace).jolt_device address.val := by
      exact JoltConstraints.finalRamWord_eq_ramPublicIoWord trace finalFrame
        adviceBelowInput address.val lower upper
    calc
      JoltConstraints.ramPublicIoWord
          (TraceWitness.finalTraceState trace).jolt_device address.val =
          TraceWitness.finalRamWord trace address.val :=
        finalRamPublic.symm
      _ = JoltConstraints.ramPublicIoWord context.io address.val :=
        publicWord address (by simpa only [layoutEq] using lower)
          (by simpa only [layoutEq] using upper) nonTermination
  exact JoltConstraints.Soundness.public_words_determine_matches_outputs
    joltInstance privateInputs context trace finalFrame
      trace.final_outputs_fit_layout runPublicWord

/-- C. The represented rows and verifier bounds give Jolt prover acceptance.
The proof will use the last-jump check, the RAM-address check, and the padded
length derived from the 256-cycle verifier floor, the witness length bound and
`NoMaxLengthTrace`. For example, under a maximum of 1024, a 256-row run may
be padded to 512, while the restriction excludes a 1024-row run. -/
theorem soundness_prover_accepts {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    (noMaxLengthTrace : joltInstance.NoMaxLengthTrace)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (trace : JoltConstraints.Soundness.UntrustedAnswerTrace joltInstance privateInputs)
    (bytecodeEq : trace.bytecode = context.bytecode)
    (represented : Represents witness trace.toUntrustedAnswerRun.toTrace) :
    (trace.prover_config joltInstance).isSome := by
  sorry

/-- D. Each executed spoil assert uses its row's pre-state operands. The row
observations and lookup constraints must rule out a failing assertion. -/
theorem soundness_spoil_asserts_pass {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (trace : JoltConstraints.Soundness.UntrustedAnswerTrace joltInstance privateInputs)
    (bytecodeEq : trace.bytecode = context.bytecode)
    (represented : Represents witness trace.toUntrustedAnswerRun.toTrace) :
    trace.SpoilAssertsPass := by
  sorry

end JoltInstance
