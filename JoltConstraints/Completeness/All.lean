import JoltConstraints.Constraints.All
import JoltConstraints.Completeness

set_option autoImplicit false

namespace JoltConstraints

/-- Assemble the individual honest-witness completeness results. It inherits the
`sorry`s listed in model_review.md (Proofs owed). -/
theorem honestWitness_constraintEquations
    {F : Type} [Field F] (params : WitnessParams)
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor trace.bytecode.size)
    (entry : Fin (2 ^ params.logBytecodeK))
    (startsAtEntry : TraceWitness.bytecodePc trace 0 = entry.val)
    (validAccesses : ramAccessesValid trace)
    (hAssertEqPasses : assertEqPasses trace)
    (adviceBelowInput : trace.initialState.jolt_device.AdviceBelowInput)
    (initialRegistersZero : ∀ src : JoltISA.Src,
      JoltISA.sourceValue src trace.initialState = 0)
    (ramChunksPos : 0 < params.ramChunks)
    (noWrap : joltInstance.program.NextPCNoWrap)
    (lastIsJump : (trace.rows.back?.all fun last =>
      trace.bytecode[last.rowIndex].instruction.is_jump) = true) :
    ConstraintEquations trace.bytecode (TraceWitness.initialRamWord trace)
      (TraceWitness.finalTraceState trace).jolt_device entry
      (HonestTrace.honestWitness (F := F) params trace) := by
  have hlayout := (finalTraceState_ioSame trace).1
  refine {
    -- Stage 1: base RV64 relations
    ramAddrEqRs1PlusImmIfLoadStore := honestWitness_ramAddrEqRs1PlusImmIfLoadStore params trace ramFits traceFits bytecodeDomain
    ramAddrEqZeroIfNotLoadStore := honestWitness_ramAddrEqZeroIfNotLoadStore params trace ramFits traceFits bytecodeDomain
    ramReadEqRamWriteIfLoad := honestWitness_ramReadEqRamWriteIfLoad params trace ramFits traceFits bytecodeDomain
    ramReadEqRdWriteIfLoad := honestWitness_ramReadEqRdWriteIfLoad params trace ramFits traceFits bytecodeDomain
    rs2EqRamWriteIfStore := honestWitness_rs2EqRamWriteIfStore params trace ramFits traceFits bytecodeDomain
    leftLookupZeroIfAddSubMul := honestWitness_leftLookupZeroIfAddSubMul params trace ramFits traceFits bytecodeDomain
    leftLookupEqLeftInputOtherwise := honestWitness_leftLookupEqLeftInputOtherwise params trace ramFits traceFits bytecodeDomain
    rightLookupAdd := honestWitness_rightLookupAdd params trace ramFits traceFits bytecodeDomain
    rightLookupSub := honestWitness_rightLookupSub params trace ramFits traceFits bytecodeDomain
    rightLookupEqProductIfMul := honestWitness_rightLookupEqProductIfMul params trace ramFits traceFits bytecodeDomain
    rightLookupEqRightInputOtherwise := honestWitness_rightLookupEqRightInputOtherwise params trace ramFits traceFits bytecodeDomain
    assertLookupOne := honestWitness_assertLookupOne params trace ramFits traceFits bytecodeDomain hAssertEqPasses
    rdWriteEqLookupIfWriteLookupToRd := honestWitness_rdWriteEqLookupIfWriteLookupToRd params trace ramFits traceFits bytecodeDomain
    rdWriteEqPCPlusConstIfJump := honestWitness_rdWriteEqPCPlusConstIfJump params trace ramFits traceFits bytecodeDomain noWrap
    nextUnexpandedPCEqLookupIfShouldJump := honestWitness_nextUnexpandedPCEqLookupIfShouldJump params trace ramFits traceFits bytecodeDomain
    nextUnexpandedPCEqPCPlusImmIfShouldBranch :=
      honestWitness_nextUnexpandedPCEqPCPlusImmIfShouldBranch
        params trace ramFits traceFits bytecodeDomain lastIsJump
    nextUnexpandedPCUpdateOtherwise := honestWitness_nextUnexpandedPCUpdateOtherwise params trace ramFits traceFits bytecodeDomain noWrap
    nextPCEqPCPlusOneIfInline := honestWitness_nextPCEqPCPlusOneIfInline params trace ramFits traceFits bytecodeDomain
    mustStartSequenceFromBeginning := honestWitness_mustStartSequenceFromBeginning params trace ramFits traceFits bytecodeDomain
    -- Stage 2: product and RAM relations
    productEqLeftInputMulRightInput := honestWitness_productEqLeftInputMulRightInput params trace ramFits traceFits bytecodeDomain
    shouldBranchEqLookupOutputMulBranch := honestWitness_shouldBranchEqLookupOutputMulBranch params trace ramFits traceFits bytecodeDomain
    shouldJumpEqJumpMulNotNextIsNoop := honestWitness_shouldJumpEqJumpMulNotNextIsNoop params trace ramFits traceFits bytecodeDomain
    ramReadValueEqRamRead := honestWitness_ramReadValueEqRamRead params trace ramFits traceFits bytecodeDomain
    ramWriteValueEqRamReadWrite := honestWitness_ramWriteValueEqRamReadWrite params trace ramFits traceFits bytecodeDomain
    ramAddressEqRamRaf := by simpa only [hlayout] using
      (honestWitness_ramAddressEqRamRaf params trace ramFits traceFits bytecodeDomain validAccesses)
    ramOutputEqPublicIo := honestWitness_ramOutputEqPublicIo params trace ramFits traceFits bytecodeDomain adviceBelowInput
    -- Stage 3: shifts and instruction inputs
    nextUnexpandedPCEqShift := honestWitness_nextUnexpandedPCEqShift params trace ramFits traceFits bytecodeDomain
    nextPCEqShift := honestWitness_nextPCEqShift params trace ramFits traceFits bytecodeDomain
    nextIsVirtualEqShift := honestWitness_nextIsVirtualEqShift params trace ramFits traceFits bytecodeDomain
    nextIsFirstInSequenceEqShift := honestWitness_nextIsFirstInSequenceEqShift params trace ramFits traceFits bytecodeDomain
    nextIsNoopEqShift := honestWitness_nextIsNoopEqShift params trace ramFits traceFits bytecodeDomain
    leftInstructionInputEqSelection := honestWitness_leftInstructionInputEqSelection params trace ramFits traceFits bytecodeDomain
    rightInstructionInputEqSelection := honestWitness_rightInstructionInputEqSelection params trace ramFits traceFits bytecodeDomain
    -- Stage 4: register and RAM histories
    rdWriteValueEqRegistersReadWrite := honestWitness_rdWriteValueEqRegistersReadWrite params trace ramFits traceFits bytecodeDomain initialRegistersZero
    rs1ValueEqRegistersRead := honestWitness_rs1ValueEqRegistersRead params trace ramFits traceFits bytecodeDomain initialRegistersZero
    rs2ValueEqRegistersRead := honestWitness_rs2ValueEqRegistersRead params trace ramFits traceFits bytecodeDomain initialRegistersZero
    ramValEqInitialPlusPrefixRamInc := honestWitness_ramValEqInitialPlusPrefixRamInc params trace ramFits traceFits bytecodeDomain validAccesses
    ramValFinalEqInitialPlusRamInc := honestWitness_ramValFinalEqInitialPlusRamInc params trace ramFits validAccesses traceFits bytecodeDomain
    -- Stage 5: instruction lookup and register history
    lookupOutputEqInstructionReadRaf := honestWitness_lookupOutputEqInstructionReadRaf params trace ramFits traceFits bytecodeDomain
    leftLookupOperandEqInstructionRaf := honestWitness_leftLookupOperandEqInstructionRaf params trace ramFits traceFits bytecodeDomain
    rightLookupOperandEqInstructionRaf := honestWitness_rightLookupOperandEqInstructionRaf params trace ramFits traceFits bytecodeDomain
    registersValEqPrefixRdInc := honestWitness_registersValEqPrefixRdInc params trace ramFits traceFits bytecodeDomain initialRegistersZero
    -- Stage 6: bytecode and selector relations
    pcEqBytecodeRead := honestWitness_pcEqBytecodeRead params trace ramFits traceFits bytecodeDomain
    unexpandedPCEqBytecodeRead := honestWitness_unexpandedPCEqBytecodeRead params trace ramFits traceFits bytecodeDomain
    immEqBytecodeRead := honestWitness_immEqBytecodeRead params trace ramFits traceFits bytecodeDomain
    opFlagsEqBytecodeRead := honestWitness_opFlagsEqBytecodeRead params trace ramFits traceFits bytecodeDomain
    instructionFlagsEqBytecodeRead := honestWitness_instructionFlagsEqBytecodeRead params trace ramFits traceFits bytecodeDomain
    rs1RaEqBytecodeRead := honestWitness_rs1RaEqBytecodeRead params trace ramFits traceFits bytecodeDomain
    rs2RaEqBytecodeRead := honestWitness_rs2RaEqBytecodeRead params trace ramFits traceFits bytecodeDomain
    rdWaEqBytecodeRead := honestWitness_rdWaEqBytecodeRead params trace ramFits traceFits bytecodeDomain
    lookupTableFlagEqBytecodeRead := honestWitness_lookupTableFlagEqBytecodeRead params trace ramFits traceFits bytecodeDomain
    instructionRafFlagEqBytecodeRead := honestWitness_instructionRafFlagEqBytecodeRead params trace ramFits traceFits bytecodeDomain
    bytecodeRaAtEntryEqOne := honestWitness_bytecodeRaAtEntryEqOne params trace ramFits traceFits bytecodeDomain entry startsAtEntry
    instructionRaChunkBooleanity := honestWitness_instructionRaChunkBooleanity params trace ramFits traceFits bytecodeDomain
    bytecodeRaChunkBooleanity := honestWitness_bytecodeRaChunkBooleanity params trace ramFits traceFits bytecodeDomain
    ramRaChunkBooleanity := honestWitness_ramRaChunkBooleanity params trace ramFits traceFits bytecodeDomain
    ramHammingWeightBooleanity := honestWitness_ramHammingWeightBooleanity params trace ramFits traceFits bytecodeDomain
    ramRaEqChunkProduct := honestWitness_ramRaEqChunkProduct params trace ramFits traceFits bytecodeDomain ramChunksPos
    instructionRaEqChunkProduct := honestWitness_instructionRaEqChunkProduct params trace ramFits traceFits bytecodeDomain
    -- Stage 7: hamming weights
    instructionRaChunkHammingWeight := honestWitness_instructionRaChunkHammingWeight params trace ramFits traceFits bytecodeDomain
    bytecodeRaChunkHammingWeight := honestWitness_bytecodeRaChunkHammingWeight params trace ramFits traceFits bytecodeDomain
    ramRaChunkHammingWeight := honestWitness_ramRaChunkHammingWeight params trace ramFits traceFits bytecodeDomain
  }

-- Every assert in the run has equal sides: an ordinary one (imm = 0) executed, so its
-- sides were equal; a spoil one (imm ≠ 0) is assumed to pass.
theorem _root_.HonestTrace.assert_eq_passes {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (spoilAssertsPass : trace.SpoilAssertsPass) : assertEqPasses trace := by
  intro t
  dsimp only
  split
  · rename_i lhs rhs imm isAssert
    by_cases zero : imm = 0
    · -- an ordinary assert
      subst zero
      have runs := trace.executes trace.rows[t] (Array.getElem_mem t.isLt)
      rw [withRuntimeAdvice_assert (instruction := trace.bytecode[trace.rows[t].rowIndex].instruction)
        _ lhs rhs 0 isAssert] at runs
      exact assert_eq_holds lhs rhs _ _ _ runs
    · -- a spoil assert
      exact spoilAssertsPass _ (Array.getElem_mem t.isLt) lhs rhs imm isAssert zero
  · trivial

-- Both advice buffers of the starting device lie below the inputs, which start a whole
-- number of 64-bit words above the lowest address.
theorem _root_.HonestTrace.advice_below_input {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    trace.initialState.jolt_device.AdviceBelowInput := by
  have below := initial_state_advice_below_input joltInstance privateInputs trace.initialState
    trace.initialized
  rw [MemoryLayout.get_lowest_address_toNat] at below
  exact ⟨below.1, below.2.1, below.2.2⟩

-- Rust's entry slot is where the witness starts: the first row's slot, or the NoOp's
-- slot 0 when the trace is empty (the entry address is then 0).
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:218-226 (get_first_pc)
theorem _root_.HonestTrace.entry_slot {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (slots : Array BytecodeSlot) (preprocessed : preprocess trace.bytecode = some slots)
    (entrySlot : Nat)
    (entryIsRust : get_first_pc slots joltInstance.program.entry_address = some entrySlot) :
    TraceWitness.bytecodePc trace 0 = entrySlot := by
  by_cases nonempty : 0 < trace.rows.size
  · -- the trace starts at the entry slot
    have first := trace.starts_at_entry slots preprocessed (getElem trace.rows 0 nonempty)
      (Array.getElem?_eq_getElem nonempty)
    rw [first] at entryIsRust
    rw [TraceWitness.bytecodePc, dif_pos nonempty]
    exact Option.some.inj entryIsRust
  · -- with no rows the entry address is 0, which get_first_pc maps to the NoOp
    have zero : joltInstance.program.entry_address = 0 := by
      by_contra notZero
      exact nonempty (trace.nonempty notZero)
    rw [zero] at entryIsRust
    unfold get_first_pc at entryIsRust
    rw [if_pos rfl] at entryIsRust
    rw [TraceWitness.bytecodePc, dif_neg nonempty]
    exact Option.some.inj entryIsRust

-- The run's final state, as matches_outputs reads it, is the witness's final state.
theorem _root_.HonestTrace.final_state_eq {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs) :
    (trace.rows.back?.map (·.postState)).getD trace.initialState =
      TraceWitness.finalTraceState trace := by
  unfold TraceWitness.finalTraceState
  rw [Array.back?_eq_getElem?]
  split
  · rename_i nonempty
    rw [Array.getElem?_eq_getElem (by omega)]
    rfl
  · rw [Array.getElem?_eq_none (by omega)]
    rfl

-- Every constraint holds for the honest witness at the sizes Rust's prover picks for the
-- run, against the public I/O the verifier checks, when the instance claims the outputs
-- the run produced. What is assumed: Rust's prover accepts the run (`accepted`; the open
-- issues that stop it are in model_review.md), no spoil assert fails, the PC does not wrap
-- (a16z), and, inside the trace and the witness, the code does not change during the run
-- (`code_unchanged`, a16z) and the run uses no RAM 2 GiB or more above RAM_START
-- (`finalRamWord`, a16z). `slots`, `entry` and `io` name what Rust computes; they always
-- exist.
theorem _root_.HonestTrace.allConstraints_rust_sizes
    {F : Type} [Field F]
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    -- Rust's prover accepts the run and picks these sizes
    (config : ProverConfig) (accepted : trace.prover_config = some config)
    -- Rust's preprocessed bytecode, and the entry slot its verifier uses
    (slots : Array BytecodeSlot) (preprocessed : preprocess trace.bytecode = some slots)
    (entry : Fin (2 ^ (trace.witness_params config accepted).logBytecodeK))
    (entryIsRust : get_first_pc slots joltInstance.program.entry_address = some entry.val)
    -- assumed: no spoil assert fails
    (spoilAssertsPass : trace.SpoilAssertsPass)
    -- assumed: a legal ELF's PC does not wrap (a16z confirmed)
    (noWrap : joltInstance.program.NextPCNoWrap)
    -- the instance claims the outputs the run produced
    (claimsRunOutputs : trace.matches_outputs)
    -- the public I/O the verifier checks the proof against
    (io : JoltDevice) (publicIo : joltInstance.public_io = some io) :
    AllConstraints joltInstance privateInputs
      (trace.honestWitness (F := F) (trace.witness_params config accepted)) := by
  refine ⟨{
    bytecode := trace.bytecode
    initialRam := TraceWitness.initialRamWord trace
    io := io
    entry := entry
    expands := trace.expands
    initialized := ⟨trace.initialState, trace.initialized, rfl⟩
    publicIo := publicIo
    entryIsRust := ⟨slots, preprocessed, entryIsRust⟩ }, ?_⟩
  change ConstraintEquations trace.bytecode (TraceWitness.initialRamWord trace) io entry
    (trace.honestWitness (F := F) (trace.witness_params config accepted))
  have all := honestWitness_constraintEquations (F := F) (trace.witness_params config accepted) trace
    (trace.witness_params_ram_fits config accepted)
    (trace.witness_params_padded config accepted)
    (trace.witness_params_bytecode_domain config accepted)
    entry
    (trace.entry_slot slots preprocessed entry.val entryIsRust)
    trace.ram_accesses_valid
    (trace.assert_eq_passes spoilAssertsPass)
    trace.advice_below_input
    trace.initialRegistersZero
    (trace.witness_params_ram_chunks_pos config accepted)
    noWrap
    (trace.prover_config_last_jump config accepted)
  -- the verifier's I/O: the instance's layout, inputs, trimmed outputs and panic flag
  obtain ⟨layoutBuilt, _⟩ := initial_state_device joltInstance privateInputs trace.initialState
    trace.initialized
  unfold JoltInstance.public_io at publicIo
  rw [bind_some_iff] at publicIo
  obtain ⟨layout, isLayout, publicIo⟩ := publicIo
  rw [layoutBuilt] at isLayout
  cases isLayout
  cases publicIo
  -- the run's final device has the same layout and inputs, and the claimed outputs and
  -- panic flag
  obtain ⟨sameLayout, _, _, sameInputs⟩ := finalTraceState_ioSame trace
  have startInputs := initial_state_inputs joltInstance privateInputs trace.initialState
    trace.initialized
  obtain ⟨sameOutputs, samePanic⟩ := claimsRunOutputs
  rw [trace.final_state_eq] at sameOutputs samePanic
  -- the instance's inputs fit their region (validate_inputs)
  have valid := trace.valid_inputs
  unfold JoltInstance.validate_inputs at valid
  rw [layoutBuilt] at valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
  unfold JoltInstance.memory_layout at layoutBuilt
  refine { all with ramAddressEqRamRaf := ?_, ramOutputEqPublicIo := ?_ }
  · -- the RAM-address constraint reads only the layout
    simpa only [sameLayout] using all.ramAddressEqRamRaf
  · -- constraint (26): the verifier's public words are the run's
    intro address
    have runs := all.ramOutputEqPublicIo address
    have maskSame : ramPublicIoMask (F := F)
        { inputs := joltInstance.inputs, trusted_advice := #[], untrusted_advice := #[],
          outputs := trimTrailingZeros joltInstance.outputs, panic := joltInstance.panic,
          memory_layout := trace.initialState.jolt_device.memory_layout } address.val =
        ramPublicIoMask (F := F) (TraceWitness.finalTraceState trace).jolt_device address.val := by
      unfold ramPublicIoMask
      rw [sameLayout]
    have wordSame := ramPublicIoWord_trimmed
      { inputs := joltInstance.inputs, trusted_advice := #[], untrusted_advice := #[],
        outputs := trimTrailingZeros joltInstance.outputs, panic := joltInstance.panic,
        memory_layout := trace.initialState.jolt_device.memory_layout }
      (TraceWitness.finalTraceState trace).jolt_device _
      (by rw [sameLayout]; exact layoutBuilt)
      (by rw [sameInputs, startInputs, sameLayout]; exact valid.1.2)
      sameLayout.symm (by rw [sameInputs, startInputs]) samePanic.symm sameOutputs.symm
      address.val
    rw [maskSame, wordSame]
    exact runs

end JoltConstraints
