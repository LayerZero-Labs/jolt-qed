import JoltConstraints.translation.constraint_context
import JoltConstraints.translation.Constraints.AssertLookupOne
import JoltConstraints.translation.Constraints.BytecodeRaAtEntryEqOne
import JoltConstraints.translation.Constraints.BytecodeRaChunkBooleanity
import JoltConstraints.translation.Constraints.BytecodeRaChunkHammingWeight
import JoltConstraints.translation.Constraints.ImmEqBytecodeRead
import JoltConstraints.translation.Constraints.InstructionAddressCanonical
import JoltConstraints.translation.Constraints.InstructionFlagsEqBytecodeRead
import JoltConstraints.translation.Constraints.InstructionRaChunkBooleanity
import JoltConstraints.translation.Constraints.InstructionRaChunkHammingWeight
import JoltConstraints.translation.Constraints.InstructionRaEqChunkProduct
import JoltConstraints.translation.Constraints.InstructionRafFlagEqBytecodeRead
import JoltConstraints.translation.Constraints.LeftInstructionInputEqSelection
import JoltConstraints.translation.Constraints.LeftLookupEqLeftInputOtherwise
import JoltConstraints.translation.Constraints.LeftLookupOperandEqInstructionRaf
import JoltConstraints.translation.Constraints.LeftLookupZeroIfAddSubMul
import JoltConstraints.translation.Constraints.LookupOutputEqInstructionReadRaf
import JoltConstraints.translation.Constraints.LookupTableFlagEqBytecodeRead
import JoltConstraints.translation.Constraints.MustStartSequenceFromBeginning
import JoltConstraints.translation.Constraints.NextIsFirstInSequenceEqShift
import JoltConstraints.translation.Constraints.NextIsNoopEqShift
import JoltConstraints.translation.Constraints.NextIsVirtualEqShift
import JoltConstraints.translation.Constraints.NextPCEqPCPlusOneIfInline
import JoltConstraints.translation.Constraints.NextPCEqShift
import JoltConstraints.translation.Constraints.NextUnexpandedPCEqLookupIfJump
import JoltConstraints.translation.Constraints.NextUnexpandedPCEqPCPlusImmIfShouldBranch
import JoltConstraints.translation.Constraints.NextUnexpandedPCEqShift
import JoltConstraints.translation.Constraints.NextUnexpandedPCUpdateOtherwise
import JoltConstraints.translation.Constraints.OpFlagsEqBytecodeRead
import JoltConstraints.translation.Constraints.PCEqBytecodeRead
import JoltConstraints.translation.Constraints.ProductEqLeftInputMulRightInput
import JoltConstraints.translation.Constraints.RamAddrEqRs1PlusImmMinusLookupIfLoadStore
import JoltConstraints.translation.Constraints.RamAddrEqZeroIfNotLoadStore
import JoltConstraints.translation.Constraints.RamAddressEqRamRaf
import JoltConstraints.translation.Constraints.RamOutputEqPublicIo
import JoltConstraints.translation.Constraints.RamRaChunkBooleanity
import JoltConstraints.translation.Constraints.RamRaEqChunkProduct
import JoltConstraints.translation.Constraints.RamReadEqRamWriteIfLoad
import JoltConstraints.translation.Constraints.RamReadEqRdWriteIfLoad
import JoltConstraints.translation.Constraints.RamReadValueEqRamRead
import JoltConstraints.translation.Constraints.RamValEqInitialPlusPrefixRamInc
import JoltConstraints.translation.Constraints.RamValFinalEqInitialPlusRamInc
import JoltConstraints.translation.Constraints.RamWriteValueEqRamReadWrite
import JoltConstraints.translation.Constraints.RdWaEqBytecodeRead
import JoltConstraints.translation.Constraints.RdWriteEqLookupIfWriteLookupToRd
import JoltConstraints.translation.Constraints.RdWriteEqPCPlusConstIfJump
import JoltConstraints.translation.Constraints.RdWriteValueEqRegistersReadWrite
import JoltConstraints.translation.Constraints.RegistersValEqPrefixRdInc
import JoltConstraints.translation.Constraints.RightInstructionInputEqSelection
import JoltConstraints.translation.Constraints.RightLookupAdd
import JoltConstraints.translation.Constraints.RightLookupEqProductIfMul
import JoltConstraints.translation.Constraints.RightLookupEqRightInputOtherwise
import JoltConstraints.translation.Constraints.RightLookupOperandEqInstructionRaf
import JoltConstraints.translation.Constraints.RightLookupSub
import JoltConstraints.translation.Constraints.Rs1RaEqBytecodeRead
import JoltConstraints.translation.Constraints.Rs1ValueEqRegistersRead
import JoltConstraints.translation.Constraints.Rs2EqRamWriteIfStore
import JoltConstraints.translation.Constraints.Rs2RaEqBytecodeRead
import JoltConstraints.translation.Constraints.Rs2ValueEqRegistersRead
import JoltConstraints.translation.Constraints.ShouldBranchEqLookupOutputMulBranch
import JoltConstraints.translation.Constraints.HaltEndRule
import JoltConstraints.translation.Constraints.RamAccessCount
import JoltConstraints.translation.Constraints.RamWriteProtected
import JoltConstraints.translation.Constraints.UnexpandedPCEqBytecodeRead

open LeanRV64D

set_option autoImplicit false

namespace JoltConstraints

/-- The modeled equations over bytecode, initial RAM, public I/O and one witness.
`AllConstraints` below binds these data to the instance and private inputs. -/
structure ConstraintEquations {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow)
    (initialRam : Nat → BitVec 64)
    (io : JoltPublicIo)
    (entry : Fin (2 ^ params.logBytecodeK))
    (witness : WitnessType F params) : Prop where
  -- Stage 1: base RV64 relations
  ramAddrEqRs1PlusImmMinusLookupIfLoadStore : JoltConstraints.ramAddrEqRs1PlusImmMinusLookupIfLoadStore witness
  ramAddrEqZeroIfNotLoadStore : JoltConstraints.ramAddrEqZeroIfNotLoadStore witness
  ramReadEqRamWriteIfLoad : JoltConstraints.ramReadEqRamWriteIfLoad witness
  ramReadEqRdWriteIfLoad : JoltConstraints.ramReadEqRdWriteIfLoad witness
  rs2EqRamWriteIfStore : JoltConstraints.rs2EqRamWriteIfStore witness
  leftLookupZeroIfAddSubMul : JoltConstraints.leftLookupZeroIfAddSubMul witness
  leftLookupEqLeftInputOtherwise : JoltConstraints.leftLookupEqLeftInputOtherwise witness
  rightLookupAdd : JoltConstraints.rightLookupAdd witness
  rightLookupSub : JoltConstraints.rightLookupSub witness
  rightLookupEqProductIfMul : JoltConstraints.rightLookupEqProductIfMul witness
  rightLookupEqRightInputOtherwise : JoltConstraints.rightLookupEqRightInputOtherwise witness
  assertLookupOne : JoltConstraints.assertLookupOne witness
  rdWriteEqLookupIfWriteLookupToRd : JoltConstraints.rdWriteEqLookupIfWriteLookupToRd witness
  rdWriteEqPCPlusConstIfJump : JoltConstraints.rdWriteEqPCPlusConstIfJump witness
  nextUnexpandedPCEqLookupIfJump : JoltConstraints.nextUnexpandedPCEqLookupIfJump witness
  nextUnexpandedPCEqPCPlusImmIfShouldBranch : JoltConstraints.nextUnexpandedPCEqPCPlusImmIfShouldBranch witness
  nextUnexpandedPCUpdateOtherwise : JoltConstraints.nextUnexpandedPCUpdateOtherwise witness
  nextPCEqPCPlusOneIfInline : JoltConstraints.nextPCEqPCPlusOneIfInline witness
  mustStartSequenceFromBeginning : JoltConstraints.mustStartSequenceFromBeginning witness
  -- Stage 2: product and RAM relations
  productEqLeftInputMulRightInput : JoltConstraints.productEqLeftInputMulRightInput witness
  shouldBranchEqLookupOutputMulBranch : JoltConstraints.shouldBranchEqLookupOutputMulBranch witness
  haltEndRule : JoltConstraints.haltEndRule io.panic witness
  ramWriteProtected : JoltConstraints.ramWriteProtected
    (fun k => ramWriteProtectedMask bytecode io.memory_layout k.val) witness
  ramAccessCount : JoltConstraints.ramAccessCount witness
  ramReadValueEqRamRead : JoltConstraints.ramReadValueEqRamRead witness
  ramWriteValueEqRamReadWrite : JoltConstraints.ramWriteValueEqRamReadWrite witness
  ramAddressEqRamRaf : JoltConstraints.ramAddressEqRamRaf io.memory_layout witness
  ramOutputEqPublicIo : JoltConstraints.ramOutputEqPublicIo io witness
  -- Stage 3: shifts and instruction inputs
  nextUnexpandedPCEqShift : JoltConstraints.nextUnexpandedPCEqShift witness
  nextPCEqShift : JoltConstraints.nextPCEqShift witness
  nextIsVirtualEqShift : JoltConstraints.nextIsVirtualEqShift witness
  nextIsFirstInSequenceEqShift : JoltConstraints.nextIsFirstInSequenceEqShift witness
  nextIsNoopEqShift : JoltConstraints.nextIsNoopEqShift witness
  leftInstructionInputEqSelection : JoltConstraints.leftInstructionInputEqSelection witness
  rightInstructionInputEqSelection : JoltConstraints.rightInstructionInputEqSelection witness
  -- Stage 4: register and RAM histories
  rdWriteValueEqRegistersReadWrite : JoltConstraints.rdWriteValueEqRegistersReadWrite witness
  rs1ValueEqRegistersRead : JoltConstraints.rs1ValueEqRegistersRead witness
  rs2ValueEqRegistersRead : JoltConstraints.rs2ValueEqRegistersRead witness
  ramValEqInitialPlusPrefixRamInc : JoltConstraints.ramValEqInitialPlusPrefixRamInc initialRam witness
  ramValFinalEqInitialPlusRamInc : JoltConstraints.ramValFinalEqInitialPlusRamInc initialRam witness
  -- Stage 5: instruction lookup and register history
  lookupOutputEqInstructionReadRaf : JoltConstraints.lookupOutputEqInstructionReadRaf witness
  leftLookupOperandEqInstructionRaf : JoltConstraints.leftLookupOperandEqInstructionRaf witness
  rightLookupOperandEqInstructionRaf : JoltConstraints.rightLookupOperandEqInstructionRaf witness
  -- Akita build only (characteristic below 2^128): canonical identity-RAF addresses.
  instructionAddressCanonical : JoltConstraints.instructionAddressCanonical witness
  registersValEqPrefixRdInc : JoltConstraints.registersValEqPrefixRdInc witness
  -- Stage 6: bytecode and selector relations
  pcEqBytecodeRead : JoltConstraints.pcEqBytecodeRead witness
  unexpandedPCEqBytecodeRead : JoltConstraints.unexpandedPCEqBytecodeRead bytecode witness
  immEqBytecodeRead : JoltConstraints.immEqBytecodeRead bytecode witness
  opFlagsEqBytecodeRead : JoltConstraints.opFlagsEqBytecodeRead bytecode witness
  instructionFlagsEqBytecodeRead : JoltConstraints.instructionFlagsEqBytecodeRead bytecode witness
  rs1RaEqBytecodeRead : JoltConstraints.rs1RaEqBytecodeRead bytecode witness
  rs2RaEqBytecodeRead : JoltConstraints.rs2RaEqBytecodeRead bytecode witness
  rdWaEqBytecodeRead : JoltConstraints.rdWaEqBytecodeRead bytecode witness
  lookupTableFlagEqBytecodeRead : JoltConstraints.lookupTableFlagEqBytecodeRead bytecode witness
  instructionRafFlagEqBytecodeRead : JoltConstraints.instructionRafFlagEqBytecodeRead bytecode witness
  bytecodeRaAtEntryEqOne : JoltConstraints.bytecodeRaAtEntryEqOne entry witness
  instructionRaChunkBooleanity : JoltConstraints.instructionRaChunkBooleanity witness
  bytecodeRaChunkBooleanity : JoltConstraints.bytecodeRaChunkBooleanity witness
  ramRaChunkBooleanity : JoltConstraints.ramRaChunkBooleanity witness
  ramRaEqChunkProduct : JoltConstraints.ramRaEqChunkProduct witness
  instructionRaEqChunkProduct : JoltConstraints.instructionRaEqChunkProduct witness
  -- Stage 7: hamming weights
  instructionRaChunkHammingWeight : JoltConstraints.instructionRaChunkHammingWeight witness
  bytecodeRaChunkHammingWeight : JoltConstraints.bytecodeRaChunkHammingWeight witness

/-- The relation for a fixed instance and explicit prover inputs. Trusted advice
is part of the instance; Jolt's verifier holds a commitment to it, and we model
its contents directly. The execution tape in `privateInputs` is irrelevant to
this relation; see `AllConstraints.advice_tape_irrelevant`.
The context is existential only to name preprocessing results: its certificates
bind every bytecode row, initial RAM word, public I/O value and entry slot to
these inputs. No execution trace or honest-witness construction is an input. -/
def AllConstraints {F : Type} [Field F] {params : WitnessParams}
    (joltInstance : JoltInstance SourceInstruction) (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) : Prop :=
  ∃ context : ConstraintContext joltInstance privateInputs params,
    ConstraintEquations context.bytecode context.initialRam context.io context.entry witness

end JoltConstraints
