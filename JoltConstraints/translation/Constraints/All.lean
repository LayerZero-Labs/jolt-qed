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

/-- The modeled equations over bytecode, initial RAM values, public I/O and one
witness. `initialValue address` is the field element that Jolt's verifier uses as
the initial value of RAM word `address` in constraints (37) and (38).
For example, a word in the untrusted-advice block is a committed field element,
which need not be the cast of a 64-bit word.
`AllConstraints` below binds these data to the instance and the advice. -/
structure FieldConstraintEquations {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow)
    (initialValue : Nat → F)
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
  ramValEqInitialPlusPrefixRamInc : JoltConstraints.ramValEqInitialPlusPrefixRamInc initialValue witness
  ramValFinalEqInitialPlusRamInc : JoltConstraints.ramValFinalEqInitialPlusRamInc initialValue witness
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

/-- The equations with every initial RAM word a 64-bit value, cast into the field.
For example, an honest run's initial RAM has this form, and so does every
initial word outside the untrusted-advice block. -/
abbrev ConstraintEquations {F : Type} [Field F] {params : WitnessParams}
    (bytecode : Array JoltInstructionRow)
    (initialRam : Nat → BitVec 64)
    (io : JoltPublicIo)
    (entry : Fin (2 ^ params.logBytecodeK))
    (witness : WitnessType F params) : Prop :=
  FieldConstraintEquations bytecode (ramInitialValue initialRam) io entry witness

/-- The private inputs with no untrusted advice and an empty advice tape.
`AllConstraints` builds the instance's fixed initial RAM from these inputs and takes
the untrusted-advice words separately, as field elements.
For example, `JoltPrivateInputs.noUntrustedAdvice.untrusted_advice` is `#[]`, so the
untrusted-advice block of the fixed initial RAM holds zeros. -/
def _root_.JoltPrivateInputs.noUntrustedAdvice : JoltPrivateInputs :=
  { untrusted_advice := #[], advice_tape := #[] }

/-- The index of RAM word `address` within the untrusted-advice block, if it lies there.
The block starts at the remapped word of `untrusted_advice_start` and holds
`max_untrusted_advice_size / 8` words.
For example, if `untrusted_advice_start` remaps to word 100 and
`max_untrusted_advice_size` is 16, then word 101 has index `some 1` and word 102 has
index `none`.
Jolt at `ff6fc6568`: `crates/jolt-verifier/src/stages/stage4/ram_val_check.rs`
(`ram_val_check_advice_block`). -/
def untrustedAdviceWordIndex? (layout : MemoryLayout) (address : Nat) : Option Nat :=
  match TraceWitness.remapRamAddress layout layout.untrusted_advice_start with
  | none => none
  | some first =>
      if first ≤ address ∧ address - first < layout.max_untrusted_advice_size.toNat / 8 then
        some (address - first)
      else none

/-- The initial RAM values Jolt's verifier uses when the prover commits to untrusted
advice: the committed word `untrustedAdvice index` in the untrusted-advice block, and the
fixed 64-bit word `fixedRam address` elsewhere.
Jolt's verifier adds the committed block's evaluation to the evaluation of the public
initial RAM, which is zero in the block, so the sum equals this replacement.
For example, if `untrusted_advice_start` remaps to word 100 and the block holds 2 words,
then the value at word 101 is `untrustedAdvice 1`, and the value at word 102 is the cast
of `fixedRam 102`.
Jolt at `ff6fc6568`: `crates/jolt-verifier/src/stages/stage4/ram_val_check.rs`
(`ram_val_check_init_structure`). -/
noncomputable def committedInitialValue {F : Type} [Field F] (layout : MemoryLayout)
    (fixedRam : Nat → BitVec 64) (untrustedAdvice : Nat → F) (address : Nat) : F :=
  match untrustedAdviceWordIndex? layout address with
  | some index => untrustedAdvice index
  | none => ramInitialValue fixedRam address

/-- The untrusted-advice words of a 64-bit initial RAM: word `index` of the
untrusted-advice block, cast into the field. An honest prover commits to these words.
For example, if `untrusted_advice_start` remaps to word 100, then
`adviceBlockWords layout initialRam 1` is the cast of `initialRam 101`. If
`untrusted_advice_start` does not remap, every word is zero.
Jolt at `ff6fc6568`: `crates/jolt-verifier/src/stages/stage4/ram_val_check.rs`
(`ram_val_check_advice_block`). -/
noncomputable def adviceBlockWords {F : Type} [Field F] (layout : MemoryLayout)
    (initialRam : Nat → BitVec 64) (index : Nat) : F :=
  match TraceWitness.remapRamAddress layout layout.untrusted_advice_start with
  | none => 0
  | some first => ramInitialValue initialRam (first + index)

/-- The relation with untrusted advice given as bytes, as the tracer receives it.
The soundness proof goes through this relation; the headline theorems use
`AllConstraints` below.
Trusted advice is part of the instance; Jolt's verifier holds a commitment to it, and we
model its contents directly. The execution tape in `privateInputs` is irrelevant to
this relation; see `AllConstraintsOnBytes.advice_tape_irrelevant`.
The context is existential only to name preprocessing results: its certificates
bind every bytecode row, initial RAM word, public I/O value and entry slot to
these inputs. No execution trace or honest-witness construction is an input.
For example, `privateInputs.untrusted_advice = #[1, 2]` puts the word `0x0201` at the
start of the untrusted-advice block of the initial RAM the constraints use. -/
def AllConstraintsOnBytes {F : Type} [Field F] {params : WitnessParams}
    (joltInstance : JoltInstance SourceInstruction) (privateInputs : JoltPrivateInputs)
    (witness : WitnessType F params) : Prop :=
  ∃ context : ConstraintContext joltInstance privateInputs params,
    ConstraintEquations context.bytecode context.initialRam context.io context.entry witness

/-- The relation for a fixed instance, committed untrusted-advice words and a witness.
Jolt's verifier holds only a commitment to the untrusted advice, so each advice word
is an arbitrary field element: `untrustedAdvice index` is the word at index `index` of
the untrusted-advice block.
The context fixes the rest of the initial RAM from the instance alone, with no
untrusted advice and an empty advice tape.
Trusted advice is part of the instance; Jolt's verifier holds a commitment to it, and we
model its contents as packed bytes.
The context is existential only to name preprocessing results: its certificates
bind every bytecode row, initial RAM word, public I/O value and entry slot to the
instance. No execution trace or honest-witness construction is an input.
For example, an honest run with advice bytes `#[1, 2]` satisfies the relation with
`untrustedAdvice 0 = 0x0201` and every other advice word zero. -/
def AllConstraints {F : Type} [Field F] {params : WitnessParams}
    (joltInstance : JoltInstance SourceInstruction) (untrustedAdvice : Nat → F)
    (witness : WitnessType F params) : Prop :=
  ∃ context : ConstraintContext joltInstance JoltPrivateInputs.noUntrustedAdvice params,
    FieldConstraintEquations context.bytecode
      (committedInitialValue context.io.memory_layout context.initialRam untrustedAdvice)
      context.io context.entry witness

end JoltConstraints
