import JoltConstraints.theorems.Completeness.AssertLookupOne
import JoltConstraints.theorems.Completeness.BytecodeRaAtEntryEqOne
import JoltConstraints.theorems.Completeness.BytecodeRaChunkBooleanity
import JoltConstraints.theorems.Completeness.BytecodeRaChunkHammingWeight
import JoltConstraints.theorems.Completeness.HaltEndRule
import JoltConstraints.theorems.Completeness.ImmEqBytecodeRead
import JoltConstraints.theorems.Completeness.InstructionAddressCanonical
import JoltConstraints.theorems.Completeness.InstructionFlagsEqBytecodeRead
import JoltConstraints.theorems.Completeness.InstructionRaChunkBooleanity
import JoltConstraints.theorems.Completeness.InstructionRaChunkHammingWeight
import JoltConstraints.theorems.Completeness.InstructionRaEqChunkProduct
import JoltConstraints.theorems.Completeness.InstructionRafFlagEqBytecodeRead
import JoltConstraints.theorems.Completeness.LeftInstructionInputEqSelection
import JoltConstraints.theorems.Completeness.LeftLookupEqLeftInputOtherwise
import JoltConstraints.theorems.Completeness.LeftLookupOperandEqInstructionRaf
import JoltConstraints.theorems.Completeness.LeftLookupZeroIfAddSubMul
import JoltConstraints.theorems.Completeness.LookupOutputEqInstructionReadRaf
import JoltConstraints.theorems.Completeness.LookupTableFlagEqBytecodeRead
import JoltConstraints.theorems.Completeness.MustStartSequenceFromBeginning
import JoltConstraints.theorems.Completeness.NextIsFirstInSequenceEqShift
import JoltConstraints.theorems.Completeness.NextIsNoopEqShift
import JoltConstraints.theorems.Completeness.NextIsVirtualEqShift
import JoltConstraints.theorems.Completeness.NextPCEqPCPlusOneIfInline
import JoltConstraints.theorems.Completeness.NextPCEqShift
import JoltConstraints.theorems.Completeness.NextUnexpandedPCEqLookupIfJump
import JoltConstraints.theorems.Completeness.NextUnexpandedPCEqPCPlusImmIfShouldBranch
import JoltConstraints.theorems.Completeness.NextUnexpandedPCEqShift
import JoltConstraints.theorems.Completeness.OpFlagsEqBytecodeRead
import JoltConstraints.theorems.Completeness.PCEqBytecodeRead
import JoltConstraints.theorems.Completeness.ProductEqLeftInputMulRightInput
import JoltConstraints.theorems.Completeness.RamAccessCount
import JoltConstraints.theorems.Completeness.RamAddrEqRs1PlusImmMinusLookupIfLoadStore
import JoltConstraints.theorems.Completeness.RamAddrEqZeroIfNotLoadStore
import JoltConstraints.theorems.Completeness.RamAddressEqRamRaf
import JoltConstraints.theorems.Completeness.RamOutputEqPublicIo
import JoltConstraints.theorems.Completeness.RamRaChunkBooleanity
import JoltConstraints.theorems.Completeness.RamRaEqChunkProduct
import JoltConstraints.theorems.Completeness.RamReadEqRamWriteIfLoad
import JoltConstraints.theorems.Completeness.RamReadEqRdWriteIfLoad
import JoltConstraints.theorems.Completeness.RamReadValueEqRamRead
import JoltConstraints.theorems.Completeness.RamValEqInitialPlusPrefixRamInc
import JoltConstraints.theorems.Completeness.RamValFinalEqInitialPlusRamInc
import JoltConstraints.theorems.Completeness.RamWriteProtected
import JoltConstraints.theorems.Completeness.RamWriteValueEqRamReadWrite
import JoltConstraints.theorems.Completeness.RdWaEqBytecodeRead
import JoltConstraints.theorems.Completeness.RdWriteEqLookupIfWriteLookupToRd
import JoltConstraints.theorems.Completeness.RdWriteEqPCPlusConstIfJump
import JoltConstraints.theorems.Completeness.RdWriteValueEqRegistersReadWrite
import JoltConstraints.theorems.Completeness.RegistersValEqPrefixRdInc
import JoltConstraints.theorems.Completeness.RightInstructionInputEqSelection
import JoltConstraints.theorems.Completeness.RightLookupEqProductIfMul
import JoltConstraints.theorems.Completeness.RightLookupEqRightInputOtherwise
import JoltConstraints.theorems.Completeness.RightLookupOperandEqInstructionRaf
import JoltConstraints.theorems.Completeness.RightLookupSub
import JoltConstraints.theorems.Completeness.Rs1RaEqBytecodeRead
import JoltConstraints.theorems.Completeness.Rs1ValueEqRegistersRead
import JoltConstraints.theorems.Completeness.Rs2EqRamWriteIfStore
import JoltConstraints.theorems.Completeness.Rs2RaEqBytecodeRead
import JoltConstraints.theorems.Completeness.Rs2ValueEqRegistersRead
import JoltConstraints.theorems.Completeness.ShouldBranchEqLookupOutputMulBranch
import JoltConstraints.theorems.Completeness.UnexpandedPCEqBytecodeRead

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- Assemble the 63 honest-witness equations, for example the RAM-address
equation (01) and operand selection (33), under their existing trace premises.
The bundle inherits the gaps listed in `model_review.md`, "Proofs owed".
Jolt's verifier: `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`
(`rv64_trace_constraints`) at `ff6fc6568`. -/
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
    (initialRegistersZero : ∀ src : JoltISA.Src,
      JoltISA.sourceValue src trace.initialState = 0)
    (ramChunksPos : 0 < params.ramChunks)
    (noWrap : joltInstance.program.NextPCNoWrap)
    (lastIsJump : (trace.rows.back?.all fun last =>
      trace.bytecode[last.rowIndex].instruction.is_jump) = true)
    -- the chunk widths Jolt's prover picks; Jolt's sizes satisfy this
    (chunkConfig : params.ProverChunkConfig) :
    ConstraintEquations trace.bytecode (TraceWitness.initialRamWord trace)
      trace.publicIo entry
      (HonestTrace.honestWitness (F := F) params trace) := by
  have hlayout := (finalTraceState_ioSame trace).1
  refine {
    -- Stage 1: base RV64 relations
    ramAddrEqRs1PlusImmMinusLookupIfLoadStore := honestWitness_ramAddrEqRs1PlusImmMinusLookupIfLoadStore params trace ramFits traceFits bytecodeDomain
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
    nextUnexpandedPCEqLookupIfJump := honestWitness_nextUnexpandedPCEqLookupIfJump params trace ramFits traceFits bytecodeDomain
    nextUnexpandedPCEqPCPlusImmIfShouldBranch :=
      honestWitness_nextUnexpandedPCEqPCPlusImmIfShouldBranch
        params trace ramFits traceFits bytecodeDomain lastIsJump
    nextUnexpandedPCUpdateOtherwise := honestWitness_nextUnexpandedPCUpdateOtherwise params trace ramFits traceFits bytecodeDomain noWrap
    nextPCEqPCPlusOneIfInline := honestWitness_nextPCEqPCPlusOneIfInline params trace ramFits traceFits bytecodeDomain
    mustStartSequenceFromBeginning := honestWitness_mustStartSequenceFromBeginning params trace ramFits traceFits bytecodeDomain
    haltEndRule := honestWitness_haltEndRule params trace traceFits
    ramAccessCount := honestWitness_ramAccessCount params trace ramFits
    ramWriteProtected := by simpa only [HonestTrace.publicIo, hlayout] using
      honestWitness_ramWriteProtected (F := F) params trace ramFits validAccesses
    -- Stage 2: product and RAM relations
    productEqLeftInputMulRightInput := honestWitness_productEqLeftInputMulRightInput params trace ramFits traceFits bytecodeDomain
    shouldBranchEqLookupOutputMulBranch := honestWitness_shouldBranchEqLookupOutputMulBranch params trace ramFits traceFits bytecodeDomain
    ramReadValueEqRamRead := honestWitness_ramReadValueEqRamRead params trace ramFits traceFits bytecodeDomain
    ramWriteValueEqRamReadWrite := honestWitness_ramWriteValueEqRamReadWrite params trace ramFits traceFits bytecodeDomain
    ramAddressEqRamRaf := by simpa only [HonestTrace.publicIo, hlayout] using
      (honestWitness_ramAddressEqRamRaf params trace ramFits traceFits bytecodeDomain validAccesses)
    ramOutputEqPublicIo := honestWitness_ramOutputEqPublicIo params trace ramFits traceFits bytecodeDomain
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
    instructionAddressCanonical := honestWitness_instructionAddressCanonical params trace ramFits traceFits bytecodeDomain
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
    ramRaEqChunkProduct := honestWitness_ramRaEqChunkProduct params trace ramFits traceFits bytecodeDomain ramChunksPos
    instructionRaEqChunkProduct := honestWitness_instructionRaEqChunkProduct params trace ramFits traceFits bytecodeDomain chunkConfig
    -- Stage 7: hamming weights
    instructionRaChunkHammingWeight := honestWitness_instructionRaChunkHammingWeight params trace ramFits traceFits bytecodeDomain
    bytecodeRaChunkHammingWeight := honestWitness_bytecodeRaChunkHammingWeight params trace ramFits traceFits bytecodeDomain
  }

end JoltConstraints

open JoltConstraints

-- Rust's entry slot is where the witness starts: the first row's slot, or the NoOp's
-- slot 0 when the trace is empty (the entry address is then 0).
-- See : jolt/crates/jolt-program/src/preprocess/bytecode.rs:246-254 (get_first_pc)
theorem HonestTrace.entry_slot {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (slots : Array BytecodeSlot) (preprocessed : preprocess trace.bytecode = some slots)
    (entrySlot : Nat)
    (entryIsRust : get_first_pc slots joltInstance.program.entry_address = some entrySlot) :
    TraceWitness.bytecodePc trace 0 = entrySlot := by
  have nonempty := trace.nonempty
  have first := trace.starts_at_entry slots preprocessed (getElem trace.rows 0 nonempty)
    (Array.getElem?_eq_getElem nonempty)
  rw [first] at entryIsRust
  rw [TraceWitness.bytecodePc, dite_eq_left nonempty]
  exact Option.some.inj entryIsRust

-- The run's final state, as matches_outputs reads it, is the witness's final state.
theorem HonestTrace.final_state_eq {joltInstance : JoltInstance SourceInstruction}
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

/-- Completeness at Jolt's sizes: when Jolt's prover accepts the honest trace with
config `config` (`proverAccepts`), the honest witness at Jolt's witness sizes
(`HonestTrace.witness_params`) satisfies every constraint, against Jolt's preprocessed
bytecode `slots`, the verifier's entry slot `entry` and the public I/O `io` the verifier
checks the proof against.
It needs the existing premises below and inherits the gaps listed in `model_review.md`
("Proofs owed").
For example, a 300-row run that touches RAM word 1000 is checked on a 512-cycle witness
with a 1024-word RAM table. -/
theorem HonestTrace.allConstraints_prover_sizes
    {F : Type} [Field F]
    {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs)
    -- Jolt's prover accepts the run and picks these sizes
    (config : ProverConfig) (proverAccepts : trace.prover_config joltInstance = some config)
    -- Jolt's preprocessed bytecode, and the entry slot its verifier uses
    (slots : Array BytecodeSlot) (preprocessed : preprocess trace.bytecode = some slots)
    (entry : Fin (2 ^ (trace.witness_params config proverAccepts).logBytecodeK))
    (entryIsRust : get_first_pc slots joltInstance.program.entry_address = some entry.val)
    -- assumed: no spoil assert fails
    (spoilAssertsPass : trace.SpoilAssertsPass)
    -- assumed: a legal ELF's PC does not wrap (a16z confirmed)
    (noWrap : joltInstance.program.NextPCNoWrap)
    -- assumed: a16z told us by phone on 2026-10-08 that Jolt can assume a program is
    -- never empty, so its memory image loads at least one byte. Jolt's prover does not
    -- reject an empty ELF; only its verifier does (bug-report/verifier-ram-minimum).
    (imageNonempty : joltInstance.program.ImageNonempty)
    -- the instance claims the outputs the run produced
    (claimsRunOutputs : trace.matches_outputs joltInstance)
    -- the public I/O the verifier checks the proof against
    (io : JoltPublicIo) (publicIo : joltInstance.public_io = some io) :
    AllConstraints joltInstance privateInputs
      (trace.honestWitness (F := F) (trace.witness_params config proverAccepts)) := by
  refine ⟨{
    bytecode := trace.bytecode
    initialRam := TraceWitness.initialRamWord trace
    io := io
    entry := entry
    expands := trace.expands
    initialized := ⟨trace.initialState, trace.initialized, rfl⟩
    publicIo := publicIo
    validInputs := trace.valid_inputs
    traceLengthBound := by
      obtain ⟨isPadded, bounded⟩ := trace.prover_config_trace_length config proverAccepts
      simpa only [trace.witness_params_trace_length config proverAccepts, isPadded] using bounded
    traceLengthFloor := by
      obtain ⟨base | akita, _⟩ := trace.witness_params_padded config proverAccepts
      · rw [base, WitnessParams.proverTraceLength]
        exact Nat.le_max_left _ _
      · rw [akita, WitnessParams.proverTraceLength]
        exact le_trans (by decide : 256 ≤ 2 ^ 12) (Nat.le_max_left _ _)
    bytecodeDomain := trace.witness_params_bytecode_domain config proverAccepts
    ramSizeBounds := trace.witness_params_ram_bounds config proverAccepts imageNonempty
    oneHotFitsSetup := by
      cases hasLayout : joltInstance.memory_layout with
      | none =>
        unfold JoltInstance.public_io at publicIo
        rw [hasLayout] at publicIo
        contradiction
      | some layout => exact trace.witness_params_one_hot_fits_setup config proverAccepts layout hasLayout
    entryIsRust := ⟨slots, preprocessed, entryIsRust⟩ }, ?_⟩
  change ConstraintEquations trace.bytecode (TraceWitness.initialRamWord trace) io entry
    (trace.honestWitness (F := F) (trace.witness_params config proverAccepts))
  have all := honestWitness_constraintEquations (F := F) (trace.witness_params config proverAccepts) trace
    (trace.witness_params_ram_fits config proverAccepts)
    (trace.witness_params_padded config proverAccepts)
    (trace.witness_params_bytecode_domain config proverAccepts)
    entry
    (trace.entry_slot slots preprocessed entry.val entryIsRust)
    trace.ram_accesses_valid
    (trace.assert_eq_passes spoilAssertsPass)
    trace.initialRegistersZero
    (trace.witness_params_ram_chunks_pos config proverAccepts)
    noWrap
    (trace.prover_config_last_jump config proverAccepts)
    (trace.witness_params_chunk_config config proverAccepts)
  -- the verifier's I/O: the instance's layout, inputs, trimmed outputs and panic flag
  obtain ⟨layoutBuilt, _⟩ := initial_state_device joltInstance privateInputs trace.initialState
    trace.initialized
  unfold JoltInstance.public_io at publicIo
  rw [bind_some_iff] at publicIo
  obtain ⟨layout, isLayout, publicIo⟩ := publicIo
  rw [layoutBuilt] at isLayout
  cases isLayout
  cases publicIo
  have sameLayout := (finalTraceState_ioSame trace).1
  obtain ⟨sameOutputs, samePanic⟩ := claimsRunOutputs
  rw [trace.final_state_eq] at sameOutputs samePanic
  have valid := trace.valid_inputs
  unfold JoltInstance.validate_inputs at valid
  rw [layoutBuilt] at valid
  simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
  unfold JoltInstance.memory_layout at layoutBuilt
  refine { all with
    haltEndRule := ?_
    ramWriteProtected := ?_
    ramAddressEqRamRaf := ?_
    ramOutputEqPublicIo := ?_ }
  · simpa only [HonestTrace.publicIo, samePanic] using all.haltEndRule
  · simpa only [HonestTrace.publicIo, sameLayout] using all.ramWriteProtected
  · simpa only [HonestTrace.publicIo, sameLayout] using all.ramAddressEqRamRaf
  · intro address
    have runs := all.ramOutputEqPublicIo address
    have maskSame : ramPublicIoMask (F := F)
        { inputs := joltInstance.inputs, outputs := trimTrailingZeros joltInstance.outputs,
          panic := joltInstance.panic, memory_layout := trace.initialState.jolt_device.memory_layout } address.val =
        ramPublicIoMask (F := F) trace.publicIo address.val := by
      simp only [ramPublicIoMask, HonestTrace.publicIo, sameLayout]
    have wordSame := ramPublicIoWord_trimmed
      { inputs := joltInstance.inputs, outputs := trimTrailingZeros joltInstance.outputs,
        panic := joltInstance.panic, memory_layout := trace.initialState.jolt_device.memory_layout }
      trace.publicIo _ (by dsimp only [HonestTrace.publicIo]; rw [sameLayout]; exact layoutBuilt)
      (by dsimp only [HonestTrace.publicIo]; rw [sameLayout]; exact valid.1.1.2)
      (by dsimp only [HonestTrace.publicIo]; exact sameLayout.symm) rfl sameOutputs.symm address.val
    rw [maskSame, wordSame]
    exact runs
