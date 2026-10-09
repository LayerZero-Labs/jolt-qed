import Mathlib.Algebra.Field.Defs
import JoltConstraints.constraint_context
import JoltConstraints.Constraints.AssertLookupOne
import JoltConstraints.Constraints.BytecodeRaAtEntryEqOne
import JoltConstraints.Constraints.BytecodeRaChunkBooleanity
import JoltConstraints.Constraints.BytecodeRaChunkHammingWeight
import JoltConstraints.Constraints.ImmEqBytecodeRead
import JoltConstraints.Constraints.InstructionFlagsEqBytecodeRead
import JoltConstraints.Constraints.InstructionRaChunkBooleanity
import JoltConstraints.Constraints.InstructionRaChunkHammingWeight
import JoltConstraints.Constraints.InstructionRaEqChunkProduct
import JoltConstraints.Constraints.InstructionRafFlagEqBytecodeRead
import JoltConstraints.Constraints.LeftInstructionInputEqSelection
import JoltConstraints.Constraints.LeftLookupEqLeftInputOtherwise
import JoltConstraints.Constraints.LeftLookupOperandEqInstructionRaf
import JoltConstraints.Constraints.LeftLookupZeroIfAddSubMul
import JoltConstraints.Constraints.LookupOutputEqInstructionReadRaf
import JoltConstraints.Constraints.LookupTableFlagEqBytecodeRead
import JoltConstraints.Constraints.MustStartSequenceFromBeginning
import JoltConstraints.Constraints.NextIsFirstInSequenceEqShift
import JoltConstraints.Constraints.NextIsNoopEqShift
import JoltConstraints.Constraints.NextIsVirtualEqShift
import JoltConstraints.Constraints.NextPCEqPCPlusOneIfInline
import JoltConstraints.Constraints.NextPCEqShift
import JoltConstraints.Constraints.NextUnexpandedPCEqLookupIfShouldJump
import JoltConstraints.Constraints.NextUnexpandedPCEqPCPlusImmIfShouldBranch
import JoltConstraints.Constraints.NextUnexpandedPCEqShift
import JoltConstraints.Constraints.NextUnexpandedPCUpdateOtherwise
import JoltConstraints.Constraints.OpFlagsEqBytecodeRead
import JoltConstraints.Constraints.PCEqBytecodeRead
import JoltConstraints.Constraints.ProductEqLeftInputMulRightInput
import JoltConstraints.Constraints.RamAddrEqRs1PlusImmIfLoadStore
import JoltConstraints.Constraints.RamAddrEqZeroIfNotLoadStore
import JoltConstraints.Constraints.RamAddressEqRamRaf
import JoltConstraints.Constraints.RamHammingWeightBooleanity
import JoltConstraints.Constraints.RamOutputEqPublicIo
import JoltConstraints.Constraints.RamRaChunkBooleanity
import JoltConstraints.Constraints.RamRaChunkHammingWeight
import JoltConstraints.Constraints.RamRaEqChunkProduct
import JoltConstraints.Constraints.RamReadEqRamWriteIfLoad
import JoltConstraints.Constraints.RamReadEqRdWriteIfLoad
import JoltConstraints.Constraints.RamReadValueEqRamRead
import JoltConstraints.Constraints.RamValEqInitialPlusPrefixRamInc
import JoltConstraints.Constraints.RamValFinalEqInitialPlusRamInc
import JoltConstraints.Constraints.RamWriteValueEqRamReadWrite
import JoltConstraints.Constraints.RdWaEqBytecodeRead
import JoltConstraints.Constraints.RdWriteEqLookupIfWriteLookupToRd
import JoltConstraints.Constraints.RdWriteEqPCPlusConstIfJump
import JoltConstraints.Constraints.RdWriteValueEqRegistersReadWrite
import JoltConstraints.Constraints.RegistersValEqPrefixRdInc
import JoltConstraints.Constraints.RightInstructionInputEqSelection
import JoltConstraints.Constraints.RightLookupAdd
import JoltConstraints.Constraints.RightLookupEqProductIfMul
import JoltConstraints.Constraints.RightLookupEqRightInputOtherwise
import JoltConstraints.Constraints.RightLookupOperandEqInstructionRaf
import JoltConstraints.Constraints.RightLookupSub
import JoltConstraints.Constraints.Rs1RaEqBytecodeRead
import JoltConstraints.Constraints.Rs1ValueEqRegistersRead
import JoltConstraints.Constraints.Rs2EqRamWriteIfStore
import JoltConstraints.Constraints.Rs2RaEqBytecodeRead
import JoltConstraints.Constraints.Rs2ValueEqRegistersRead
import JoltConstraints.Constraints.ShouldBranchEqLookupOutputMulBranch
import JoltConstraints.Constraints.ShouldJumpEqJumpMulNotNextIsNoop
import JoltConstraints.Constraints.UnexpandedPCEqBytecodeRead

set_option autoImplicit false

namespace JoltConstraints

/-- The modeled equations over bytecode, initial RAM, public I/O and one witness.
`AllConstraints` below binds these data to the instance and private inputs. -/
structure ConstraintEquations {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow)
    (initialRam : Nat → BitVec 64)
    (io : JoltDevice)
    (entry : Fin (2 ^ params.logBytecodeK))
    (witness : WitnessType F params) : Prop where
  -- Stage 1: base RV64 relations
  ramAddrEqRs1PlusImmIfLoadStore : JoltConstraints.ramAddrEqRs1PlusImmIfLoadStore witness
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
  nextUnexpandedPCEqLookupIfShouldJump : JoltConstraints.nextUnexpandedPCEqLookupIfShouldJump witness
  nextUnexpandedPCEqPCPlusImmIfShouldBranch : JoltConstraints.nextUnexpandedPCEqPCPlusImmIfShouldBranch witness
  nextUnexpandedPCUpdateOtherwise : JoltConstraints.nextUnexpandedPCUpdateOtherwise witness
  nextPCEqPCPlusOneIfInline : JoltConstraints.nextPCEqPCPlusOneIfInline witness
  mustStartSequenceFromBeginning : JoltConstraints.mustStartSequenceFromBeginning witness
  -- Stage 2: product and RAM relations
  productEqLeftInputMulRightInput : JoltConstraints.productEqLeftInputMulRightInput witness
  shouldBranchEqLookupOutputMulBranch : JoltConstraints.shouldBranchEqLookupOutputMulBranch witness
  shouldJumpEqJumpMulNotNextIsNoop : JoltConstraints.shouldJumpEqJumpMulNotNextIsNoop witness
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
  ramHammingWeightBooleanity : JoltConstraints.ramHammingWeightBooleanity witness
  ramRaEqChunkProduct : JoltConstraints.ramRaEqChunkProduct witness
  instructionRaEqChunkProduct : JoltConstraints.instructionRaEqChunkProduct witness
  -- Stage 7: hamming weights
  instructionRaChunkHammingWeight : JoltConstraints.instructionRaChunkHammingWeight witness
  bytecodeRaChunkHammingWeight : JoltConstraints.bytecodeRaChunkHammingWeight witness
  ramRaChunkHammingWeight : JoltConstraints.ramRaChunkHammingWeight witness

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
