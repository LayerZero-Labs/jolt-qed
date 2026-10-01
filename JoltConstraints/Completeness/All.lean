import JoltConstraints.Constraints.All
import JoltConstraints.Completeness

set_option autoImplicit false

namespace JoltConstraints

/-- Assemble the individual honest-witness completeness results.
The branch completeness result currently uses `sorry`; this theorem inherits
that admission until its proof and the Lean model are completed. -/
theorem honestWitness_allConstraints
    {F : Type} [Field F] (params : WitnessParams)
    {program : JoltProgram} (trace : JoltTrace program)
    (ramFits : params.RamFits trace)
    (traceFits : params.ProverPaddedFor trace.rows.size)
    (bytecodeDomain : params.BytecodeDomainFor program.expandedBytecode.size)
    (entry : Fin (2 ^ params.logBytecodeK))
    (terminated : trace.Terminated)
    (startsAtEntry : (getElem trace.rows 0 terminated.nonempty).rowIndex.val + 1 = entry.val)
    (validAccesses : ramAccessesValid trace)
    (hAssertEqPasses : assertEqPasses trace)
    (adviceBelowInput : program.initialState.io.AdviceBelowInput)
    (initialRegistersZero : ∀ src : JoltISA.Src,
      JoltISA.sourceValue src program.initialState = 0)
    (ramChunksPos : 0 < params.ramChunks) :
    AllConstraints program (HonestWitness.finalTraceState trace).io entry
      (JoltProgram.honestWitness (F := F) params trace ramFits traceFits bytecodeDomain) := by
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
    rdWriteEqPCPlusConstIfJump := honestWitness_rdWriteEqPCPlusConstIfJump params trace ramFits traceFits bytecodeDomain
    nextUnexpandedPCEqLookupIfShouldJump := honestWitness_nextUnexpandedPCEqLookupIfShouldJump params trace ramFits terminated traceFits bytecodeDomain
    nextUnexpandedPCEqPCPlusImmIfShouldBranch :=
      honestWitness_nextUnexpandedPCEqPCPlusImmIfShouldBranch
        params trace ramFits terminated traceFits bytecodeDomain
    nextUnexpandedPCUpdateOtherwise := honestWitness_nextUnexpandedPCUpdateOtherwise params trace ramFits terminated traceFits bytecodeDomain
    nextPCEqPCPlusOneIfInline := honestWitness_nextPCEqPCPlusOneIfInline params trace ramFits terminated traceFits bytecodeDomain
    mustStartSequenceFromBeginning := honestWitness_mustStartSequenceFromBeginning params trace ramFits traceFits bytecodeDomain
    -- Stage 2: product and RAM relations
    productEqLeftInputMulRightInput := honestWitness_productEqLeftInputMulRightInput params trace ramFits traceFits bytecodeDomain
    shouldBranchEqLookupOutputMulBranch := honestWitness_shouldBranchEqLookupOutputMulBranch params trace ramFits traceFits bytecodeDomain
    shouldJumpEqJumpMulNotNextIsNoop := honestWitness_shouldJumpEqJumpMulNotNextIsNoop params trace ramFits traceFits bytecodeDomain
    ramReadValueEqRamRead := honestWitness_ramReadValueEqRamRead params trace ramFits traceFits bytecodeDomain validAccesses
    ramWriteValueEqRamReadWrite := honestWitness_ramWriteValueEqRamReadWrite params trace ramFits traceFits bytecodeDomain validAccesses
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
    bytecodeRaAtEntryEqOne := honestWitness_bytecodeRaAtEntryEqOne params trace ramFits traceFits bytecodeDomain entry terminated.nonempty startsAtEntry
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

end JoltConstraints
