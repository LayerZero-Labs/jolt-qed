/-
The immediate obligations below `JoltInstance.soundness`. Each unfinished helper
has a name and a concrete statement so the main theorem can be assembled without
adding premises. See `JoltConstraints/documentation/model_review.md`, "Proofs owed".
-/
import JoltConstraints.theorems.Soundness.Layer6.PrefixAgreement
import JoltConstraints.theorems.Soundness.Layer7.Stopping
import JoltConstraints.theorems.Soundness.Layer7.ProverAccepts
import JoltConstraints.theorems.Soundness.Layer7.SpoilAsserts
import JoltConstraints.theorems.Soundness.Layer8.OutputWords

open LeanRV64D

set_option autoImplicit false

namespace JoltInstance

open Sail Sail.ConcurrencyInterfaceV1 Sail.ConcurrencyInterfaceV1.PreSail LeanRV64D LeanRV64D.Functions JoltISA

/-- A. Reconstruct a relaxed-answer trace whose every executed row and every
final shared RAM word agrees with the witness. -/
theorem soundness_reconstruct_trace {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness) :
    ∃ trace : JoltConstraints.Soundness.UntrustedAnswerTrace joltInstance privateInputs,
      trace.bytecode = context.bytecode ∧
        Represents witness trace.toUntrustedAnswerRun.toTrace := by
  obtain ⟨run, bytecodeEq, representedRows, realRows, noEarlierStop, cut, advice⟩ :=
    soundness_execution_prefix_agreement joltField joltInstance
      privateInputs witness context equations
  obtain ⟨stops, nonempty, finalRam⟩ :=
    soundness_stopping joltField joltInstance
      privateInputs witness context equations run bytecodeEq representedRows cut
  have accepted : joltInstance.bytecode.isSome := by
    obtain ⟨slots, preprocessed, entry⟩ := context.entryIsRust
    have valid := context.validInputs
    unfold JoltInstance.validate_inputs at valid
    cases configured : joltInstance.memory_layout with
    | none => simp only [configured, Bool.false_eq_true] at valid
    | some layout =>
      rw [configured] at valid
      simp only [Bool.and_eq_true] at valid
      have addressNonzero : joltInstance.program.entry_address ≠ 0#64 := by
        simpa only [bne_iff_ne, show (0 : BitVec 64) = 0#64 from rfl] using valid.2.1
      have region := valid.2.2
      rw [← expand_program_source_extents
        joltInstance.program context.bytecode context.expands] at region
      cases checked : checkedCodeRegion layout (bytecode_source_extents context.bytecode) with
      | none => simp only [checked, Option.isSome_none, Bool.false_eq_true] at region
      | some bounds =>
        simp [JoltInstance.bytecode, context.expands, preprocessed, entry,
          addressNonzero, configured, checked, guard]
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

/-- B. Constraint 26 checks the relaxed trace's shared output words, and row 21
binds the halt kind to the public panic claim.
For example, both success and panic traces can match their respective claims. -/
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
      address.val < (context.io.memory_layout.output_end.toNat -
        JoltConstraints.ramLowestAddress context.io.memory_layout) / 8 →
      TraceWitness.finalRamWord trace address.val =
        JoltConstraints.ramPublicIoWord context.io address.val := by
    intro address lower upper
    have checked := equations.ramOutputEqPublicIo address
    have selected : JoltConstraints.ramPublicIoMask (F := F) context.io address.val = 1 := by
      simp [JoltConstraints.ramPublicIoMask, lower, upper]
    rw [selected, one_mul] at checked
    have encoded : ((TraceWitness.finalRamWord trace address.val).toNat : F) =
        ((JoltConstraints.ramPublicIoWord context.io address.val).toNat : F) := by
      rw [← represented.finalRam address]
      exact sub_eq_zero.mp checked
    exact JoltConstraints.Soundness.word_eq_of_field_eq
      (JoltConstraints.Soundness.two_pow_127_lt_char joltField) encoded
  have bytecodeEq : trace.bytecode = context.bytecode :=
    Option.some.inj (trace.expands.symm.trans context.expands)
  have panicEq := represented_final_panic joltField context equations trace bytecodeEq
    represented.toRepresentsRows
  exact JoltConstraints.Soundness.public_words_determine_matches_outputs
    joltInstance privateInputs context trace panicEq publicWord

/-- C. The represented rows and verifier bounds give Jolt prover acceptance.
The proof uses the terminal-halt certificate, the RAM-address check and exact
power-of-two padding with the 256-cycle floor.
For example, 1024 real rows fit a public maximum of 1024.
Jolt at `ff6fc6568`: `ProverConfig::derive_from_dimensions`. -/
theorem soundness_prover_accepts {F : Type} [Field F] (joltField : JoltField F)
    (joltInstance : JoltInstance SourceInstruction)
    {params : WitnessParams} (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params)
    (context : JoltConstraints.ConstraintContext joltInstance privateInputs params)
    (equations : JoltConstraints.ConstraintEquations context.bytecode context.initialRam
      context.io context.entry witness)
    (trace : JoltConstraints.Soundness.UntrustedAnswerTrace joltInstance privateInputs)
    (bytecodeEq : trace.bytecode = context.bytecode)
    (represented : Represents witness trace.toUntrustedAnswerRun.toTrace) :
    (trace.prover_config joltInstance).isSome := by
  have halt := relaxed_trace_ends_in_halt trace
  have nonemptyRows : trace.rows ≠ #[] := by
    intro empty
    exact halt.1 (by rw [empty]; rfl)
  obtain ⟨padded, padding, fits⟩ := checked_trace_length_fits trace.rows.size
    params.logT joltInstance.max_padded_trace_length represented.rowsBound
    context.traceLengthBound (context.traceLengthFloor.trans context.traceLengthBound)
  obtain ⟨ramK, ramSize⟩ := represented_ram_size_computes joltField joltInstance
    privateInputs witness context equations trace.toUntrustedAnswerRun.toTrace
    trace.initialized represented.rowsBound represented.ramAddress
  unfold Trace.prover_config ProverConfig.deriveFromDimensions
  change (do
    guard (trace.rows.size ≠ 0 ∧ trace.execution_dimensions.ends_in_halt = true)
    let traceLength ← ProverConfig.checkedTraceLength trace.rows.size
    let ramSize ← ProverConfig.checkedRamSize trace.execution_dimensions
      trace.initialState.jolt_device.memory_layout
      (min_bytecode_address joltInstance.program.memory_init)
      (program_image_len_words joltInstance.program.memory_init)
    guard (traceLength ≤ joltInstance.max_padded_trace_length.toNat)
    pure ({ trace_length := traceLength, ram_K := ramSize } : ProverConfig)).isSome
  simp only [halt]
  simp [padding, ramSize, fits, nonemptyRows]

/-- D. Each executed spoil assert uses its row's pre-state operands.
Representation supplies those operands because they are not instruction
temporaries, and the lookup and Assert constraints force equality.
For example, a custom equality assertion with immediate 2 must have equal sides.
See jolt/tracer/src/instruction/virtual_assert_eq.rs (`VirtualAssertEQ::exec`)
at ff6fc6568. -/
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
  exact represented_spoil_asserts_pass joltField joltInstance privateInputs witness
    context equations trace.toUntrustedAnswerRun bytecodeEq represented.toRepresentsRows

end JoltInstance
