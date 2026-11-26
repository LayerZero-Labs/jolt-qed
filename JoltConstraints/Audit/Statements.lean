import JoltConstraints.Audit.Premises
import JoltConstraints.Audit.Necessity
import JoltConstraints.theorems.layout_facts
import JoltConstraints.theorems.prover_config_facts
import JoltConstraints.theorems.Soundness.Layer3.Layout

/-!
# The full statements of the audited theorems, checked by the build

`#expect_binders` in `JoltConstraints/Audit/Premises.lean` checks the binders of the headline
theorems. A restriction can also hide below a binder: in a conclusion, or in a definition the
statement mentions, such as `JoltInstance.initial_state` inside `HonestTrace`, or
`WholeRun.Related`. This file closes that gap.

`#audit_statements` lists the audited theorems, each with a label:

* `headline`: the headline theorems (the theorems `Premises.lean` checks);
* `witness`: the necessity witnesses of `JoltConstraints/Audit/Necessity.lean` (`witness` in
  `assumptions.toml`);
* `derived`: theorems that prove a fact that used to be a premise or an image field
  (`derived_by` in `assumptions.toml`).

For each one the command

1. fails unless the declaration exists under exactly that name (no `open`, no namespace);
2. fails unless its axioms are among `propext`, `Classical.choice` and `Quot.sound`;
3. compares its statement, pretty-printed, with the table after `expect`;
4. compares the fingerprint of every definition in the dependency closure of its statement,
   restricted to this repository's declarations, with the table (see
   `JoltConstraints/Audit/Commands.lean` for what the closure and the fingerprints are).

On a mismatch the error names each changed statement and each changed, new or removed
definition, with the audited theorems that depend on it. A changed definition below a headline
statement changes what the theorem says, so review it as a statement change. If the change is
intended, run `scripts/update-audit-tables.py`, which rewrites the table from the build, and
check whether a registry entry needs updating.

`scripts/check-assumptions.py` checks that the `witness` and `derived` lines here are exactly the
`witness` and `derived_by` names in `assumptions.toml`, and that the `headline` lines are the
theorems `Premises.lean` lists.
-/

#audit_statements
  headline JoltInstance.soundness
  headline JoltInstance.completeness
  headline JoltInstance.completeness_someWitness
  headline WholeRun.HonestTrace.sail_reproduces
  headline JoltInstance.sail_soundness
  witness JoltConstraints.Audit.joltField_not_implied
  witness JoltConstraints.Audit.blockConformsRiscv_not_implied
  witness JoltConstraints.Audit.memoryInitInProgram_not_derived
  derived Rv64ProgramImage.DecodedFrom.programEndGeRamStart
  derived Rv64ProgramImage.DecodedFrom.nextPCNoWrap
  derived Rv64ProgramImage.DecodedFrom.instructionLoaded
  derived new_heap_end_le
  derived HonestTrace.prover_config_image_nonempty
  derived JoltInstance.ramRegionFits
expect r#"
statement JoltInstance.soundness
  ∀ {F : Type} [inst : Field F],
    JoltField F →
      ∀ (joltInstance : JoltInstance SourceInstruction) {params : WitnessParams} (privateInputs : JoltPrivateInputs)
        (witness : WitnessType F params),
        JoltConstraints.AllConstraints joltInstance privateInputs witness → joltInstance.InLanguage
statement JoltInstance.completeness
  ∀ {F : Type} [inst : Field F] (joltInstance : JoltInstance SourceInstruction) (privateInputs : JoltPrivateInputs)
    (trace : HonestTrace joltInstance privateInputs),
    Trace.matches_outputs joltInstance trace.toTrace →
      trace.SpoilAssertsPass →
        ∀ (config : ProverConfig) (proverAccepts : Trace.prover_config joltInstance trace.toTrace = some config),
          joltInstance.max_padded_trace_length.toNat ≤ 2 ^ 63 →
            JoltConstraints.AllConstraints joltInstance privateInputs
              (HonestTrace.honestWitness (trace.witness_params config proverAccepts) trace)
statement JoltInstance.completeness_someWitness
  ∀ {F : Type} [inst : Field F] (joltInstance : JoltInstance SourceInstruction),
    joltInstance.InLanguage →
      joltInstance.max_padded_trace_length.toNat ≤ 2 ^ 63 →
        ∃ privateInputs params witness, JoltConstraints.AllConstraints joltInstance privateInputs witness
statement WholeRun.HonestTrace.sail_reproduces
  ∀ {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) {elf : WholeRun.ElfSections},
    joltInstance.program.DecodedFrom elf →
      ∀ {pre : List WholeRun.Block} {halt final : SailJoltState},
        WholeRun.HaltPrefix trace pre halt final →
          (∀ b ∈ pre, WholeRun.BlockConforms joltInstance.program b) →
            ∃ s,
              WholeRun.sailRun pre.length (WholeRun.sailInit trace.initialState) = EStateM.Result.ok () s ∧
                WholeRun.Related halt s ∧
                  trimTrailingZeros (halt.jolt_device.outputsOf s.mem) =
                      trimTrailingZeros (final.jolt_device.outputsOf final.sail.mem) ∧
                    ∃ kind,
                      final.halted = some kind ∧
                        final.jolt_device.panic = (kind == JoltHaltKind.panic) ∧
                          (WholeRun.SailHalted joltInstance.program s kind ∨ halt = final)
statement JoltInstance.sail_soundness
  ∀ {F : Type} [inst : Field F],
    JoltField F →
      ∀ (joltInstance : JoltInstance SourceInstruction) {params : WitnessParams} (givenInputs : JoltPrivateInputs)
        (witness : WitnessType F params),
        JoltConstraints.AllConstraints joltInstance givenInputs witness →
          ∀ {elf : WholeRun.ElfSections},
            joltInstance.program.DecodedFrom elf →
              ∃ privateInputs trace,
                Trace.matches_outputs joltInstance trace.toTrace ∧
                  (Trace.prover_config joltInstance trace.toTrace).isSome = true ∧
                    trace.SpoilAssertsPass ∧
                      ∃ pre halt final,
                        WholeRun.HaltPrefix trace pre halt final ∧
                          ((∀ b ∈ pre, WholeRun.BlockConforms joltInstance.program b) →
                            ∃ s,
                              WholeRun.sailRun pre.length (WholeRun.sailInit trace.initialState) =
                                  EStateM.Result.ok () s ∧
                                WholeRun.Related halt s ∧
                                  trimTrailingZeros (halt.jolt_device.outputsOf s.mem) =
                                      trimTrailingZeros joltInstance.outputs ∧
                                    ∃ kind,
                                      final.halted = some kind ∧
                                        joltInstance.panic = (kind == JoltHaltKind.panic) ∧
                                          (WholeRun.SailHalted joltInstance.program s kind ∨ halt = final))
statement JoltConstraints.Audit.joltField_not_implied
  ¬JoltField (ZMod 2)
statement JoltConstraints.Audit.blockConformsRiscv_not_implied
  ∃ elf program,
    program.DecodedFrom elf ∧
      ∃ row ∈ program.instructions, ∀ (i : RiscvInstruction), row.instruction ≠ SourceInstruction.riscv i
statement JoltConstraints.Audit.memoryInitInProgram_not_derived
  ∃ elf layout, elf.layout? = some layout ∧ ∃ entry ∈ layout.memory_init, layout.program_end.toNat ≤ entry.1.toNat
statement Rv64ProgramImage.DecodedFrom.programEndGeRamStart
  ∀ {program : Rv64ProgramImage SourceInstruction} {elf : WholeRun.ElfSections},
    program.DecodedFrom elf → JoltISA.RAM_START_ADDRESS ≤ program.program_end.toNat
statement Rv64ProgramImage.DecodedFrom.nextPCNoWrap
  ∀ {program : Rv64ProgramImage SourceInstruction} {elf : WholeRun.ElfSections},
    program.DecodedFrom elf → program.NextPCNoWrap
statement Rv64ProgramImage.DecodedFrom.instructionLoaded
  ∀ {program : Rv64ProgramImage SourceInstruction} {elf : WholeRun.ElfSections},
    program.DecodedFrom elf →
      ∀ row ∈ program.instructions,
        ∃ entry ∈ program.memory_init, row.address.toNat ≤ entry.1.toNat ∧ entry.1.toNat < row.address.toNat + 2
statement new_heap_end_le
  ∀ (config : MemoryConfig) (layout : MemoryLayout),
    MemoryLayout.new config = some layout → layout.heap_end.toNat ≤ 2 ^ 64 - 8
statement HonestTrace.prover_config_image_nonempty
  ∀ {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs}
    (trace : HonestTrace joltInstance privateInputs) (config : ProverConfig),
    Trace.prover_config joltInstance trace.toTrace = some config → joltInstance.program.ImageNonempty
statement JoltInstance.ramRegionFits
  ∀ {Source : Type} (joltInstance : JoltInstance Source), joltInstance.RamRegionFits
fingerprint b77e899f1e60533e Assumptions.SailRegReadable
fingerprint a86368c70bfa6cea BytecodeSlot
fingerprint 72a4eeef75f367e4 CircuitFlags
fingerprint 7d9ce938d1ef8e6a CircuitFlags.ctorIdx
fingerprint da8c3d52ca4769aa Decode.branchImmediates
fingerprint 3dab7c4ee2e5d5d8 Decode.csr
fingerprint f8ec423e7d15f705 Decode.funct3
fingerprint 6710d23ea07c0123 Decode.funct7
fingerprint 266d37a786c9cbef Decode.immB
fingerprint 2c76625929b10f19 Decode.immI
fingerprint c5c403fce113053d Decode.immJ
fingerprint d1704272ab22e01f Decode.immS
fingerprint 2661e934ca5cc807 Decode.immU
fingerprint 96fc446b2918d37b Decode.jOffset
fingerprint 76724bd16f758302 Decode.joltDecode
fingerprint 3a3e3a8b4fc5342b Decode.joltSuccessWord
fingerprint c65caf28b62e3099 Decode.joltUncompress
fingerprint 48ab4190292fbb56 Decode.rd
fingerprint c19749b930918b70 Decode.resetMisa
fingerprint 68233f1e52ee5354 Decode.rs1
fingerprint 67349130699d6c96 Decode.rs2
fingerprint 69de50c65a35df71 Decode.signBitMask
fingerprint 8db21dc1350b75a1 ExecutionDimensions
fingerprint 43b58529093bce2a ExecutionDimensions.observe
fingerprint cd550b7b54b09b60 ExpandedSource
fingerprint 22e81a9e7293fde5 ExpandedSource.ofNative
fingerprint c886611651d0f990 ExpandedSource.ofProgram
fingerprint cdc3482ea91a52e6 ExpandedSource.ofPureProgram
fingerprint fea738a65d7a595f HonestTrace
fingerprint 7f70efdc6361ef3c HonestTrace.honestWitness
fingerprint 49ba2cef386a6a4c HonestTrace.log_bytecode_size_lt
fingerprint b89a678844af48a0 HonestTrace.prover_config_image_nonempty
fingerprint 9d2ff4e32549641b HonestTrace.prover_config_log_ram_K_lt
fingerprint 9ff8456497ac860e HonestTrace.prover_config_log_trace_length_lt
fingerprint 606896efac8525de HonestTrace.row
fingerprint 95bdc948d00903d1 HonestTrace.witness_params
fingerprint b6fd46cab918e022 HonestTraceRow
fingerprint 42d9711eb3bf5f3a HonestWitness.RamInc
fingerprint e7f3151d09e69b79 HonestWitness.RamReadValue
fingerprint 8888146fe7865c67 HonestWitness.RamVal
fingerprint 4d08a04362f5dd5a InstructionFlags
fingerprint 1ba9089b05439314 InstructionFlags.ctorIdx
fingerprint 3a97234127a9dfb3 JoltAdviceTape
fingerprint 82c234d2ae61b7da JoltConstraints.AllConstraints
fingerprint b4b4f81063df92ef JoltConstraints.Audit.blockConformsRiscv_not_implied
fingerprint 7532bd5d075703d2 JoltConstraints.Audit.joltField_not_implied
fingerprint 5be478c9737dd4b6 JoltConstraints.Audit.memoryInitInProgram_not_derived
fingerprint d5bf9c571a9d14ee JoltConstraints.CanonicalInstructionAddress
fingerprint 1b4536ee680ef4d9 JoltConstraints.ConstraintContext
fingerprint cdba7d85142ccfc6 JoltConstraints.ConstraintEquations
fingerprint e7522cd82290f336 JoltConstraints.VerifierSizes.adviceVars
fingerprint 5d807eece99a4241 JoltConstraints.VerifierSizes.checkedNextPowerOfTwo
fingerprint 19cc0c72019617ac JoltConstraints.VerifierSizes.committedLogKChunk
fingerprint bcb0f1af1b19c197 JoltConstraints.VerifierSizes.dorySetupLogN
fingerprint 412704d2ac96f7f7 JoltConstraints.VerifierSizes.maxRamSize
fingerprint 0c4269fe5b9fc7a8 JoltConstraints.VerifierSizes.minRamSize
fingerprint f889ef9e793c7e7c JoltConstraints.VerifierSizes.remapWordAddress
fingerprint a4b1c104eb8ccad9 JoltConstraints.addressOffsetTableEntry
fingerprint c3ed2bf8efe1198b JoltConstraints.andTableEntry
fingerprint 55ff1082f2e16941 JoltConstraints.andnTableEntry
fingerprint b153467c03a26bb9 JoltConstraints.assertLookupOne
fingerprint 2a7adaf0c247df38 JoltConstraints.bytecodeAddress
fingerprint e9c0a0956eaadbcb JoltConstraints.bytecodeAddressChunk
fingerprint 650f669e3bd3c1db JoltConstraints.bytecodeCircuitFlag
fingerprint 2b483d9e27bfb7aa JoltConstraints.bytecodeImmediate
fingerprint f7333f0f0ffb58a6 JoltConstraints.bytecodeInstructionFlag
fingerprint dbac44dfa1632784 JoltConstraints.bytecodeLookupTableFlag
fingerprint 48c6a320354c3d2c JoltConstraints.bytecodeRa
fingerprint 9a39038d34bcb943 JoltConstraints.bytecodeRaAtEntryEqOne
fingerprint ae37be25d6c6512b JoltConstraints.bytecodeRaChunkBooleanity
fingerprint 9e7373ff42c26fb4 JoltConstraints.bytecodeRaChunkHammingWeight
fingerprint fd4aafc4385a8c04 JoltConstraints.bytecodeRafFlag
fingerprint f6a8e3c1323e4809 JoltConstraints.bytecodeRdRegister
fingerprint 352c8f984924d9b5 JoltConstraints.bytecodeRegisterSelector
fingerprint d4280a3ff4d6893e JoltConstraints.bytecodeRow
fingerprint 31eb01df39c4d29b JoltConstraints.bytecodeRs1Register
fingerprint 30160db270b41fe7 JoltConstraints.bytecodeRs2Register
fingerprint ac772f6900ce83a6 JoltConstraints.equalTableEntry
fingerprint eab8fcc7c98c4262 JoltConstraints.haltEndRule
fingerprint 51d8a085d273a35e JoltConstraints.immEqBytecodeRead
fingerprint 62e2e3284129cd51 JoltConstraints.instructionAddressCanonical
fingerprint a8beeb44e2c07ad4 JoltConstraints.instructionFlagsEqBytecodeRead
fingerprint 37772c8c9bee6e2d JoltConstraints.instructionLookupChunk
fingerprint e7a2cb5e146f8dc9 JoltConstraints.instructionLookupRa
fingerprint 955e441e7ed9c168 JoltConstraints.instructionRaChunkBooleanity
fingerprint 0b40529b84c3c30b JoltConstraints.instructionRaChunkHammingWeight
fingerprint 1d2e26b11f630afb JoltConstraints.instructionRaEqChunkProduct
fingerprint 63ffdac75355611f JoltConstraints.instructionRafFlagEqBytecodeRead
fingerprint e2746b3eda77ad7d JoltConstraints.instructionSmallChunkIndex
fingerprint 375e6f61bf1510dd JoltConstraints.instructionVirtualAddressDigit
fingerprint bc3a7304f6e0031b JoltConstraints.leftInstructionInputEqSelection
fingerprint 87717c20509b62d5 JoltConstraints.leftLookupEqLeftInputOtherwise
fingerprint 9f1bca4e13bf9e7d JoltConstraints.leftLookupOperandEqInstructionRaf
fingerprint 00bcbede78b2a0e0 JoltConstraints.leftLookupZeroIfAddSubMul
fingerprint 7bdc44cc49acca5f JoltConstraints.lookupAddressLeft
fingerprint ba6a0eda8e4740fe JoltConstraints.lookupAddressRight
fingerprint d9d294013b5d3ecf JoltConstraints.lookupOutputEqInstructionReadRaf
fingerprint e81314892e2101bf JoltConstraints.lookupTableEntry
fingerprint f714f6a6d8fb9f9f JoltConstraints.lookupTableFlagEqBytecodeRead
fingerprint aaa04ced68e41365 JoltConstraints.lowerHalfWordTableEntry
fingerprint 32a9fd93a9aa841b JoltConstraints.mulUNoOverflowTableEntry
fingerprint cc2b341d4404d7d2 JoltConstraints.mustStartSequenceFromBeginning
fingerprint e2d7dbfc3b323f21 JoltConstraints.nextIsFirstInSequenceEqShift
fingerprint a88b11dc88970f07 JoltConstraints.nextIsNoopEqShift
fingerprint 8709cd062f4d45be JoltConstraints.nextIsVirtualEqShift
fingerprint e284127c98fe9be4 JoltConstraints.nextPCEqPCPlusOneIfInline
fingerprint 4f34fd700aef5b69 JoltConstraints.nextPCEqShift
fingerprint d369dbdd87668a10 JoltConstraints.nextUnexpandedPCEqLookupIfJump
fingerprint 46a60d5e02a4c02a JoltConstraints.nextUnexpandedPCEqPCPlusImmIfShouldBranch
fingerprint 0ad7eb53adf26bef JoltConstraints.nextUnexpandedPCEqShift
fingerprint 2553936a4d0baded JoltConstraints.nextUnexpandedPCUpdateOtherwise
fingerprint 75b9a57559576e78 JoltConstraints.notEqualTableEntry
fingerprint b306602c355d9689 JoltConstraints.opFlagsEqBytecodeRead
fingerprint e55d11a7fd0e245d JoltConstraints.orTableEntry
fingerprint b5d4f2fe67d0a484 JoltConstraints.pcEqBytecodeRead
fingerprint b7adda158183ae83 JoltConstraints.pext
fingerprint 0340dc64991eecf3 JoltConstraints.pextSigned
fingerprint 23a1e7bed005b449 JoltConstraints.pextSignedTableEntry
fingerprint 06423cc056fb5b8a JoltConstraints.pextTableEntry
fingerprint 90bef5468be3525f JoltConstraints.pow2TableEntry
fingerprint 0f89553b5023924a JoltConstraints.pow2WTableEntry
fingerprint 18803b7fb2ed7622 JoltConstraints.productEqLeftInputMulRightInput
fingerprint b3c4ae4e378acbf7 JoltConstraints.ramAccessCount
fingerprint c0ea9a503965a769 JoltConstraints.ramAddrEqRs1PlusImmMinusLookupIfLoadStore
fingerprint 24ee1870b33898fe JoltConstraints.ramAddrEqZeroIfNotLoadStore
fingerprint d927d6bbf9fa2db6 JoltConstraints.ramAddressChunk
fingerprint 92d90c52c7371563 JoltConstraints.ramAddressEqRamRaf
fingerprint 46f54bb093f746b8 JoltConstraints.ramCodeRegion
fingerprint 289988aa568e66fb JoltConstraints.ramInitialValue
fingerprint 0bff417cd61de6f9 JoltConstraints.ramLowestAddress
fingerprint d2eb75e8466c6862 JoltConstraints.ramOutputEqPublicIo
fingerprint ac05d6c4a48a0e54 JoltConstraints.ramPublicIoMask
fingerprint b699e3bd8b468838 JoltConstraints.ramPublicIoWord
fingerprint ca56b6843fd015ff JoltConstraints.ramRaChunkBooleanity
fingerprint 3dcb42277c9d40fc JoltConstraints.ramRaEqChunkProduct
fingerprint 8a60a96fed37c973 JoltConstraints.ramReadEqRamWriteIfLoad
fingerprint 84d1614d2449a81c JoltConstraints.ramReadEqRdWriteIfLoad
fingerprint 76e382d8c6503145 JoltConstraints.ramReadValueEqRamRead
fingerprint bc5a6857577a3f53 JoltConstraints.ramValEqInitialPlusPrefixRamInc
fingerprint 680c631d5ab18106 JoltConstraints.ramValFinalEqInitialPlusRamInc
fingerprint 8a16bf20598ef097 JoltConstraints.ramWriteProtected
fingerprint e7b04517dafe9843 JoltConstraints.ramWriteProtectedMask
fingerprint bc63a8c4868911fc JoltConstraints.ramWriteValueEqRamReadWrite
fingerprint a1268caf90369311 JoltConstraints.rangeCheckAlignedTableEntry
fingerprint 62713360da25b9f0 JoltConstraints.rangeCheckTableEntry
fingerprint 1317f815752e2961 JoltConstraints.rdWaEqBytecodeRead
fingerprint fab394977a9dcfd8 JoltConstraints.rdWriteEqLookupIfWriteLookupToRd
fingerprint 9096194219681896 JoltConstraints.rdWriteEqPCPlusConstIfJump
fingerprint 34fcc1e25caf524b JoltConstraints.rdWriteValueEqRegistersReadWrite
fingerprint 4a3540a10580695b JoltConstraints.registersValEqPrefixRdInc
fingerprint 7c7ae6a8a34203db JoltConstraints.rev8w
fingerprint f0a0fae5b42ce522 JoltConstraints.rightInstructionInputEqSelection
fingerprint d03561fae9f7ca09 JoltConstraints.rightLookupAdd
fingerprint 9a2960dc03513f52 JoltConstraints.rightLookupEqProductIfMul
fingerprint 529b4f46531c0947 JoltConstraints.rightLookupEqRightInputOtherwise
fingerprint a0612eba03e70454 JoltConstraints.rightLookupOperandEqInstructionRaf
fingerprint 1a57f0304efd0335 JoltConstraints.rightLookupSub
fingerprint 882ea0243eb2f1df JoltConstraints.rs1RaEqBytecodeRead
fingerprint 8af5c0cd1c1d53b5 JoltConstraints.rs1ValueEqRegistersRead
fingerprint 99aed4934b5df6af JoltConstraints.rs2EqRamWriteIfStore
fingerprint 5a0312d81b9cac42 JoltConstraints.rs2RaEqBytecodeRead
fingerprint a9c0920241e17a88 JoltConstraints.rs2ValueEqRegistersRead
fingerprint 209fd508be8c4194 JoltConstraints.shiftDataBTableEntry
fingerprint 5159d0696d8bd043 JoltConstraints.shiftDataHTableEntry
fingerprint 13c1d9e8e9591ba4 JoltConstraints.shiftDataWTableEntry
fingerprint 8e4badcc89eb2975 JoltConstraints.shiftRightBitmaskTableEntry
fingerprint b09e3e7410964c1c JoltConstraints.shiftRightBitmaskWTableEntry
fingerprint 32034ed9a18466f2 JoltConstraints.shouldBranchEqLookupOutputMulBranch
fingerprint 2491dd0469e30eda JoltConstraints.signExtendWordTableEntry
fingerprint 7695b7cee343b352 JoltConstraints.signMaskTableEntry
fingerprint 53472c24205da05f JoltConstraints.signedGreaterThanEqualTableEntry
fingerprint 162a3b20dfd52486 JoltConstraints.signedLessThanTableEntry
fingerprint 29c910c6db29650a JoltConstraints.swapBytes32
fingerprint 4a743fa647857643 JoltConstraints.unexpandedPCEqBytecodeRead
fingerprint 6de19bd2c8f0a2b8 JoltConstraints.uninterleave
fingerprint a370d89cd8783605 JoltConstraints.unsignedGreaterThanEqualTableEntry
fingerprint c05af18a855738ef JoltConstraints.unsignedLessThanEqualTableEntry
fingerprint 847ceab3a715477c JoltConstraints.unsignedLessThanTableEntry
fingerprint 50b0dc438362976e JoltConstraints.upperHalfAllOnes
fingerprint 7e67969ea722a7c2 JoltConstraints.upperWordTableEntry
fingerprint b62ec98816866382 JoltConstraints.validDiv0TableEntry
fingerprint 74d1a6e6d56bee01 JoltConstraints.validUnsignedRemainderTableEntry
fingerprint 002167ae76e2282a JoltConstraints.virtualNegateIfTableEntry
fingerprint ef2438b5ac2350fd JoltConstraints.virtualROTRTableEntry
fingerprint 2bd2cd999540d65a JoltConstraints.virtualROTRWTableEntry
fingerprint dd0075524d019a03 JoltConstraints.virtualRev8WTableEntry
fingerprint 4b79cf291b6b1488 JoltConstraints.virtualSRATableEntry
fingerprint fffa0b3540c9e2ee JoltConstraints.virtualSRAWTableEntry
fingerprint 3702fcc09017d7ea JoltConstraints.virtualSRLTableEntry
fingerprint a26861a7e86d9607 JoltConstraints.virtualSRLWTableEntry
fingerprint 54938826722bf4ee JoltConstraints.virtualXorRotL1TableEntry
fingerprint b1a2f8d970b97dbf JoltConstraints.virtualXorRotTableEntry
fingerprint 41dafd4b5ec9f300 JoltConstraints.virtualXorRotWTableEntry
fingerprint 48f0a6f2ff4ef303 JoltConstraints.windowMaskBTableEntry
fingerprint a528102c6b38acef JoltConstraints.windowMaskHTableEntry
fingerprint 9aa598b4087c86b5 JoltConstraints.windowMaskWTableEntry
fingerprint 2dfbd99d2b85d0ce JoltConstraints.windowSignBit
fingerprint d7edae453b2e78da JoltConstraints.xorTableEntry
fingerprint f58ce5dd00c40e93 JoltCustomInstruction
fingerprint 5371e91284c11647 JoltDevice
fingerprint 9d84a6211ce3aa98 JoltDevice.initialMem
fingerprint 9bf7d73e13f8b9a9 JoltDevice.is_input
fingerprint abf2d01a7b69e73f JoltDevice.is_io_gap
fingerprint 6d7740e7a8e37c47 JoltDevice.is_output
fingerprint 7a924f16efa0a155 JoltDevice.is_trusted_advice
fingerprint dae3e09c5c79e250 JoltDevice.is_untrusted_advice
fingerprint 46e35cfb49b78035 JoltDevice.load?
fingerprint 5777981c53745021 JoltDevice.outputsOf
fingerprint 80a067c6df68e94d JoltDevice.readable
fingerprint fd6bd1bd69202196 JoltDevice.store?
fingerprint 13f3badc33c11f1a JoltField
fingerprint fd6cc850e5d82225 JoltHaltKind
fingerprint fe750de0c0a53155 JoltHaltKind.ctorIdx
fingerprint 8d65578169f993d5 JoltHostIOConfig
fingerprint 7511a40e68f65852 JoltHostIOMode
fingerprint f7438ec90bd45e71 JoltHostIOMode.ctorIdx
fingerprint f8f584e2ad0b9cb6 JoltISA.Dst
fingerprint d294fc8e9a62a466 JoltISA.Dst.ctorIdx
fingerprint 8e11d6e8c77e7c49 JoltISA.Encoded.ADDI
fingerprint b44142aaaad48471 JoltISA.Encoded.ADDIW
fingerprint 3587b18c54976d5e JoltISA.Encoded.ANDI
fingerprint 8c170930c7e95d75 JoltISA.Encoded.AUIPC
fingerprint c48f902f183ea6ed JoltISA.Encoded.BEQ
fingerprint 4fc91c0c4305fc0e JoltISA.Encoded.BGE
fingerprint 3cecc93acda1140c JoltISA.Encoded.BGEU
fingerprint 7a0c17e0185ef3f0 JoltISA.Encoded.BLT
fingerprint ffc93104c6feb0d5 JoltISA.Encoded.BLTU
fingerprint 3fb15df43a486b27 JoltISA.Encoded.BNE
fingerprint dcaf51edfbbce9bc JoltISA.Encoded.JAL
fingerprint c9b1f93b08f5b7e9 JoltISA.Encoded.JALR
fingerprint e14c61f13f6b9a4b JoltISA.Encoded.LD
fingerprint 944104c53015c6c7 JoltISA.Encoded.ORI
fingerprint 6b6bc0e3cbed2a9d JoltISA.Encoded.SD
fingerprint 74a1e10659807af8 JoltISA.Encoded.SLTI
fingerprint 6778be4600e87171 JoltISA.Encoded.SLTIU
fingerprint 14251f17a3e5335f JoltISA.Encoded.VirtualAssertEQ
fingerprint 095f04d3b006f823 JoltISA.Encoded.VirtualLoadB
fingerprint b3d99804466398b9 JoltISA.Encoded.VirtualLoadH
fingerprint 6ba322747d67e426 JoltISA.Encoded.VirtualLoadW
fingerprint 64b606086caac8e2 JoltISA.Encoded.VirtualShiftDataB
fingerprint c79a39f4a8410248 JoltISA.Encoded.VirtualShiftDataH
fingerprint 30d0fa3b0f8160eb JoltISA.Encoded.VirtualShiftDataW
fingerprint 60af00bd6faccdab JoltISA.Encoded.VirtualStoreB
fingerprint 8d6e59db319d8104 JoltISA.Encoded.VirtualStoreH
fingerprint ce0f31c7b98cd982 JoltISA.Encoded.VirtualStoreW
fingerprint 3ac359b1f0d8542d JoltISA.Encoded.VirtualWindowMaskB
fingerprint 7e2a0aeb17957cdf JoltISA.Encoded.VirtualWindowMaskH
fingerprint 3068360106c48a89 JoltISA.Encoded.VirtualWindowMaskW
fingerprint f59d111c2db07723 JoltISA.Encoded.XORI
fingerprint a818127739ab27e6 JoltISA.Instr
fingerprint 9b257ec559e15b49 JoltISA.Instr.RuntimeAdvice
fingerprint b9e076e948a980e5 JoltISA.Instr.adviceValue?
fingerprint ce158a57c3060532 JoltISA.Instr.canonicalNoOp
fingerprint e924a13c210e6f28 JoltISA.Instr.ctorIdx
fingerprint fabf50802d681ece JoltISA.Instr.destination?
fingerprint edf5f3037aa0a7a4 JoltISA.Instr.haltKind?
fingerprint ae9b6100a31e9cb3 JoltISA.Instr.rewriteNative
fingerprint 60c945aa1aef01b1 JoltISA.Instr.withRuntimeAdvice
fingerprint e26833c8bd9f8f97 JoltISA.LoadFaultClass
fingerprint cf87d6b3dbf2b9e6 JoltISA.LoadFaultClass.alignFault
fingerprint 676fd660f1dd14a2 JoltISA.Mmu.effective_address_ok
fingerprint d195363a4452dae5 JoltISA.Mmu.load?
fingerprint f9533dddbf9a1644 JoltISA.Mmu.load_doubleword
fingerprint f965f2beb2534b59 JoltISA.Mmu.load_raw?
fingerprint f6196c54e0acd135 JoltISA.Mmu.protected_byte
fingerprint 97d8abfc5eec324f JoltISA.Mmu.protected_store_ok
fingerprint 14805c5908fbb2f7 JoltISA.Mmu.ram_backing_end
fingerprint 1b78be58f60a16b2 JoltISA.Mmu.ram_byte
fingerprint 415509f3e0e2f8ec JoltISA.Mmu.ram_doubleword
fingerprint 2aa894167a6a6500 JoltISA.Mmu.store_doubleword
fingerprint 1a9dfd243419f78f JoltISA.Mmu.store_raw?
fingerprint d72b076c66d87de7 JoltISA.Mmu.trace_load_ok
fingerprint 1182119cac49aca3 JoltISA.Mmu.unsupported_load
fingerprint e53360bce7659113 JoltISA.Mmu.unsupported_store
fingerprint e26ec856a8b8e930 JoltISA.Mmu.write_ram_doubleword
fingerprint 9f6b755ac05a7ffa JoltISA.Program
fingerprint 04094d03d6234b24 JoltISA.Program.instrs
fingerprint dd12fdcb871589af JoltISA.Program.seq
fingerprint 4b8be9b4afe9cdf7 JoltISA.RAM_START_ADDRESS
fingerprint 54a1bf3bb4129d61 JoltISA.STACK_CANARY_SIZE
fingerprint 08248ae783a29183 JoltISA.Src
fingerprint 81bf971eddb85316 JoltISA.SystemCSR
fingerprint 0c9b893f0cdfbe00 JoltISA.SystemCSR.ctorIdx
fingerprint 45a9807623ae26dc JoltISA.SystemCSR.vreg
fingerprint 1afcdc6e42f0b636 JoltISA.VReg
fingerprint 69b0d76097036d4c JoltISA.addWide
fingerprint cea123118f273b29 JoltISA.advicelbProgramAuto
fingerprint 195ceb77381609bf JoltISA.adviceldProgramAuto
fingerprint 22913ea6b768d7fa JoltISA.advicelhProgramAuto
fingerprint 9174384aef357e27 JoltISA.advicelwProgramAuto
fingerprint d5478752ad5fedd7 JoltISA.amoadddProgramAuto
fingerprint 803f014196919e7c JoltISA.amoaddwProgramAuto
fingerprint 389423f984c6d40e JoltISA.amoanddProgramAuto
fingerprint b8ad847cbb97d79e JoltISA.amoandwProgramAuto
fingerprint c4837431df17e531 JoltISA.amomaxdProgramAuto
fingerprint 67a6ccbd6b9bd13e JoltISA.amomaxudProgramAuto
fingerprint f5093c2e61772aa7 JoltISA.amomaxuwProgramAuto
fingerprint bc9edb4783b70e86 JoltISA.amomaxwProgramAuto
fingerprint b7b727662675b6e5 JoltISA.amomindProgramAuto
fingerprint dfec4c8febcaa0cc JoltISA.amominudProgramAuto
fingerprint 51a9945cb75481d2 JoltISA.amominuwProgramAuto
fingerprint e9754ae800d4c0d9 JoltISA.amominwProgramAuto
fingerprint 1de1556a0fe357f6 JoltISA.amoordProgramAuto
fingerprint acb72f7a5deca52d JoltISA.amoorwProgramAuto
fingerprint 320462dfb53c16a0 JoltISA.amoswapdProgramAuto
fingerprint e1bf56b4500484c3 JoltISA.amoswapwProgramAuto
fingerprint 9ddd110be5d894ad JoltISA.amoxordProgramAuto
fingerprint 0c593cca15d750c9 JoltISA.amoxorwProgramAuto
fingerprint beb00b7c6f010329 JoltISA.branchDecisionPure
fingerprint 42d0373eae484336 JoltISA.checkedCodeRegion
fingerprint 3a5152e5d1dfa1f8 JoltISA.codeRegionAt
fingerprint e54e77c3166f0f2e JoltISA.codeRegionOf
fingerprint 80ef02d9a3f53d52 JoltISA.csrBitUpdateProgram
fingerprint 03f15c0a154eb18e JoltISA.csrImmediateBitUpdateProgram
fingerprint 1d433e6ff3996ef0 JoltISA.csrImmediateMask
fingerprint 3d93a41cde30e670 JoltISA.csrReadInto
fingerprint 707cb32e0310994d JoltISA.csrSwapWrite
fingerprint e487e91ffe49c8f0 JoltISA.csrrcProgram
fingerprint 1f081c7d18e5a619 JoltISA.csrrciProgram
fingerprint e0bcc5d5714b88f1 JoltISA.csrrsProgram
fingerprint bff23d9fa59b9fd7 JoltISA.csrrsiProgram
fingerprint 4d255ce8e17fd6cb JoltISA.csrrwProgram
fingerprint d35c53c255274ea3 JoltISA.csrrwiProgram
fingerprint be8829704f347df2 JoltISA.divProgramAuto
fingerprint b37f90541e1b0420 JoltISA.divuProgramAuto
fingerprint 9126d16aace029c6 JoltISA.divuwProgramAuto
fingerprint 5e7964ad1651d7fd JoltISA.divwProgramAuto
fingerprint c951a3e6a79e93be JoltISA.ebreakProgram
fingerprint 70b87cc0f7da2058 JoltISA.ecallProgram
fingerprint bd73e43ad17da44c JoltISA.execHalt
fingerprint cb40ba3cbce99eb1 JoltISA.execHostIO
fingerprint 4210fefabaa3530e JoltISA.execHostIOWith
fingerprint f2b869f01e494ada JoltISA.execInstr
fingerprint 17a3bcf6a1976cb7 JoltISA.execProgram
fingerprint 447867a21af09750 JoltISA.hostAdviceWriteCall
fingerprint 87c176ec813b7f3c JoltISA.hostCycleTrackCall
fingerprint c786aeff0b2c3c6b JoltISA.hostPrintCall
fingerprint 210bfa73a6ced6e1 JoltISA.initialState
fingerprint b6f240d96df3e56d JoltISA.inlineRegisterBase
fingerprint b69098d201ad4583 JoltISA.inlineTmp
fingerprint 6a5d954ad859868e JoltISA.inlineTmp0
fingerprint e38bc1dbe4aabcef JoltISA.inlineTmp1
fingerprint 6d0917df8918ec88 JoltISA.instDecidableEqSystemCSR
fingerprint e54c2b83a0d8fae7 JoltISA.instReprLoadFaultClass.repr
fingerprint 7ca9ab951361d3b1 JoltISA.instReprSystemCSR.repr
fingerprint dc56e4a9522ee6c0 JoltISA.isX0
fingerprint 60dc3e05f9e237ab JoltISA.lbProgramAuto
fingerprint 9ed378d4708799cd JoltISA.lbuProgramAuto
fingerprint e4eeccfa22897f8f JoltISA.lhProgramAuto
fingerprint 584d7fa48aa13421 JoltISA.lhuProgramAuto
fingerprint 2ceae9a3c6f4a345 JoltISA.lrdProgramAuto
fingerprint 5d0ee099e38094bb JoltISA.lrwProgramAuto
fingerprint 48e3df1974c1b082 JoltISA.luiValue
fingerprint 890f92d3a3a9d56f JoltISA.lwProgramAuto
fingerprint 0f812b7d28909583 JoltISA.lwuProgramAuto
fingerprint 3812e61b6b2d162e JoltISA.mcauseVReg
fingerprint 05cec0643daf46d7 JoltISA.mepcVReg
fingerprint 84c5e8cf423c2c28 JoltISA.mretProgram
fingerprint 6b68b69cbb5defb7 JoltISA.mscratchVReg
fingerprint 5fdc29ffb4727f0f JoltISA.mstatusVReg
fingerprint 0022931085a3f3cc JoltISA.mtvalVReg
fingerprint 564febaeab2da91b JoltISA.mulWide
fingerprint 16f87260c8e7cf24 JoltISA.mulhProgramAuto
fingerprint 207c093263de064a JoltISA.mulhsuProgramAuto
fingerprint 580eb3b0e38ed43f JoltISA.numReservedVirtualRegisters
fingerprint ddb3a567339905e0 JoltISA.pureWritebackRdZeroProgram
fingerprint d75b0b533077935a JoltISA.rdZeroRewriteVReg
fingerprint 52dcf661b77d967b JoltISA.readAdviceTape
fingerprint 5c2394e6d279e1a9 JoltISA.readHostBytes
fingerprint faff3cb09649800b JoltISA.readSrc
fingerprint 971c9a01df45b853 JoltISA.read_doubleword?
fingerprint cf487ec1fcea69b3 JoltISA.recordHalt
fingerprint 0474d10b3aa683f8 JoltISA.remProgramAuto
fingerprint 6a7fc9cc3fd305b0 JoltISA.remuProgramAuto
fingerprint 34ff16121ec8e68d JoltISA.remuwProgramAuto
fingerprint fb89ccdf47846e7a JoltISA.remwProgramAuto
fingerprint 611da493b4628f5d JoltISA.reservationDReg
fingerprint 51ac1b2a05a7c06f JoltISA.reservationWReg
fingerprint c801f08edbd0650a JoltISA.riscvRegisterBase
fingerprint 3ad7cd1893a37801 JoltISA.riscvRegisterCount
fingerprint daab2e2520308f62 JoltISA.sameXReg
fingerprint 693190234996610f JoltISA.sbProgramAuto
fingerprint 1deff54e0722ff07 JoltISA.scdProgramAuto
fingerprint 5b66c98ca4b16b5c JoltISA.scwProgramAuto
fingerprint 3860dff2c3523064 JoltISA.shProgramAuto
fingerprint 7543a91079b59f1c JoltISA.sideEffectingDst
fingerprint ea487c95c1c6c8a8 JoltISA.sideEffectingRdZeroDst
fingerprint cdcb0e177caf4e17 JoltISA.sllProgramAuto
fingerprint b092a1e0f79a03e7 JoltISA.slliMultiplier
fingerprint 687e4023c1cd4c66 JoltISA.slliProgramAuto
fingerprint 911ee4157b13e2e6 JoltISA.slliwProgramAuto
fingerprint 663d728c542086dd JoltISA.sllwProgramAuto
fingerprint a71f6da8c6c7718a JoltISA.sourceValue
fingerprint 1326d14ab55ed503 JoltISA.sraProgramAuto
fingerprint 13105860b04a9c1f JoltISA.sraiBitmask
fingerprint 16385ec2d23cca4f JoltISA.sraiProgramAuto
fingerprint f881dbdf79cf4151 JoltISA.sraiwProgramAuto
fingerprint 016183a27fcd0fe9 JoltISA.srawProgramAuto
fingerprint 6654c41d5e6277f3 JoltISA.srlProgramAuto
fingerprint 38163967ecd0db87 JoltISA.srliBitmask
fingerprint 4fa9aa1d114f5722 JoltISA.srliProgramAuto
fingerprint 4b4b6393ff27fbfb JoltISA.srliwProgramAuto
fingerprint 48ee0a22c00aece4 JoltISA.srlwProgramAuto
fingerprint 96a1ba1f4cec7e56 JoltISA.subWide
fingerprint 59136aaf313f2ad1 JoltISA.swProgramAuto
fingerprint c8770d41201a084b JoltISA.systemScratchVReg
fingerprint c876168fa1055359 JoltISA.trace_doubleword?
fingerprint c0180697f69cc438 JoltISA.trapHandlerVReg
fingerprint 9f2d1915f805785f JoltISA.writeDst
fingerprint 82d04651a02cddbb JoltInstance
fingerprint 96870fa52d635144 JoltInstance.InLanguage
fingerprint f5225139defedc5b JoltInstance.RamRegionFits
fingerprint 846aa3fa461fb4ce JoltInstance.bytecode
fingerprint c253ffa520d5eb4d JoltInstance.completeness
fingerprint 80f129558c034eb5 JoltInstance.completeness_someWitness
fingerprint d2a81868d78c24e6 JoltInstance.initial_state
fingerprint c2cf38db2def1990 JoltInstance.memory_layout
fingerprint e4ed76d6ee0e2df1 JoltInstance.one_hot_fits_setup
fingerprint 716bc56a18818986 JoltInstance.public_io
fingerprint f940de405774e031 JoltInstance.ramRegionFits
fingerprint 093b6a70d53010e6 JoltInstance.ram_size_in_bounds
fingerprint ad23e02ee275295b JoltInstance.sail_soundness
fingerprint 6c0955e9e94edcfa JoltInstance.soundness
fingerprint 64b129d2ccc27442 JoltInstance.validate_inputs
fingerprint 6cdfbf8e504ab90b JoltInstance.verifier_ram_bounds
fingerprint 4008e874e4d73954 JoltInstructionRow
fingerprint 85b60feb48439415 JoltInstructionRow.starts_source
fingerprint e197383315215b40 JoltMetadata.circuitFlag
fingerprint df1fefb95c917e9d JoltMetadata.hasCombinedLookupOperands
fingerprint 64e8e957f73bc937 JoltMetadata.immediate
fingerprint b5656b7c8d44ff42 JoltMetadata.instructionFlag
fingerprint c5dffb0ae1e77d54 JoltMetadata.instructionRafFlag
fingerprint dd59f7d6bf3b9bd0 JoltMetadata.lookupTable
fingerprint 470965882406853d JoltMetadata.lookupTableFlag
fingerprint fa534ef5fc9ac785 JoltMetadata.opcodeFlag
fingerprint c50b2e8a3a417cbb JoltMonad
fingerprint fbfd18ad19f363b5 JoltPrivateInputs
fingerprint a330427fe3af8171 JoltPublicIo
fingerprint 357aad2fcef4cd02 LookupTableKind
fingerprint 490d6e41b82f456a LookupTableKind.ctorIdx
fingerprint f97696b8c367c520 MAX_FINAL_ROWS_PER_SOURCE
fingerprint 0d67af59ab2d52d9 MemoryConfig
fingerprint 4ef3f75baf8a8500 MemoryLayout
fingerprint ae1748e51ee026bc MemoryLayout.adviceRegions
fingerprint be5f22bcc53ff697 MemoryLayout.alignUp8
fingerprint 59af07e5a43c068b MemoryLayout.checkedAdd
fingerprint f8b3dd2a77e5898a MemoryLayout.checkedMul
fingerprint f0c502dd72b6a35d MemoryLayout.checkedSub
fingerprint 61c6371fed8a59a0 MemoryLayout.get_lowest_address
fingerprint d7292b7abac37a89 MemoryLayout.get_total_memory_size
fingerprint d0c9c735e202353f MemoryLayout.io_segments_ok
fingerprint 98031abcba0b8a70 MemoryLayout.max_ram_k?
fingerprint b61f705999617dac MemoryLayout.new
fingerprint 19a789d92f1151c0 MemoryLayout.powerOfTwoOrZero
fingerprint 4e31ed22116983f8 MemoryLayout.ram_size
fingerprint bc0bead1fc044839 ProverConfig
fingerprint a62e1b76e4871da2 ProverConfig.checkedRamSize
fingerprint 8379c26817dea3a7 ProverConfig.checkedTouched
fingerprint 061245ec79ecb0da ProverConfig.checkedTraceLength
fingerprint a554baa3df3dc018 ProverConfig.deriveFromDimensions
fingerprint 3ae9653df243c784 Riscv.andi
fingerprint 629db0006fe4f782 Riscv.ori
fingerprint 17fda5c60f459dd7 RiscvInstruction
fingerprint 8c6f410858f63758 RiscvInstruction.ctorIdx
fingerprint ead665c09f2cdd88 Rv64ProgramImage
fingerprint 4968616a106a7913 Rv64ProgramImage.DecodedFrom
fingerprint 6e0c8db96111ea32 Rv64ProgramImage.DecodedFrom.instructionLoaded
fingerprint 0d7bb8aa42ccacc5 Rv64ProgramImage.DecodedFrom.nextPCNoWrap
fingerprint 51ae86b6817c11be Rv64ProgramImage.DecodedFrom.programEndGeRamStart
fingerprint 2be898386a724e08 Rv64ProgramImage.ImageNonempty
fingerprint 3e9f35c55f84593b Rv64ProgramImage.NextPCNoWrap
fingerprint 3ba04a035f444958 Rv64ProgramImage.instructionAt
fingerprint 20eec48d540df9e3 Rv64ProgramImage.program_size
fingerprint 16edc040423d1134 SailJoltState
fingerprint 53652ba416ebae19 SailState
fingerprint be92db0b54bb8e1a SourceInstruction
fingerprint d9b43089d25fa5d0 SourceInstruction.DecodesFrom
fingerprint 7e9f8717a8dc1f6a SourceInstruction.ctorIdx
fingerprint 1330692acb211bd1 SourceInstruction.expand
fingerprint 9830898c2702e7b3 SourceInstruction.honestTracerAdvice
fingerprint befa5ddb58959cfd SourceInstructionRow
fingerprint b2abb398c9fbd2b6 Step.StepInvariant
fingerprint b88e9d81455e049e Step.setReg
fingerprint 8bba91dfc400da07 System.reservationWidth
fingerprint 0404e7eb5c14cb88 System.systemProject
fingerprint 661027df3f5837ae Trace
fingerprint d4ef9e269e9ad96e Trace.SpoilAssertsPass
fingerprint e4bb911921aea649 Trace.execution_dimensions
fingerprint 3484129635ace58d Trace.matches_outputs
fingerprint b133e90f97a23a16 Trace.prover_config
fingerprint 94fc213b0fad87e9 TraceRow
fingerprint 86eb772926c836c0 TraceRow.Halts
fingerprint 28ad36d80bef3a2e TraceRow.ram_address
fingerprint bf4c0ef2a3fed76a TraceRow.someTracerAdvice?
fingerprint 621903c0eb0ff5b5 TraceWitness.BytecodeRaChunk
fingerprint 240f9a1cf82d4765 TraceWitness.Imm
fingerprint 5a484eec79fab7a9 TraceWitness.InstructionFlags
fingerprint daf83c21d65e4eb3 TraceWitness.InstructionRa
fingerprint 89f929877d2ffada TraceWitness.InstructionRaChunk
fingerprint a33226371076d505 TraceWitness.InstructionRafFlag
fingerprint 13b8cdcd1119c688 TraceWitness.LeftInstructionInput
fingerprint 85fcdd15ee636920 TraceWitness.LeftLookupOperand
fingerprint 48cfa39c5ca017d1 TraceWitness.LookupOutput
fingerprint ea521df1dd9c10da TraceWitness.LookupTableFlag
fingerprint 5464328da6a40c9c TraceWitness.NextIsFirstInSequence
fingerprint 0074a67745c62dff TraceWitness.NextIsNoop
fingerprint 626a74e9cec4a96c TraceWitness.NextIsVirtual
fingerprint e55113897a72cad6 TraceWitness.NextPC
fingerprint 515ccecd9f07654d TraceWitness.NextUnexpandedPC
fingerprint 74e6923f666cbf76 TraceWitness.OpFlags
fingerprint cfff79bb5967e760 TraceWitness.PC
fingerprint 5cb5a227a281db0c TraceWitness.Product
fingerprint 77eac6c64081f424 TraceWitness.RamAddress
fingerprint 57c5bf5cf681ffa8 TraceWitness.RamRa
fingerprint 6fb042f257efc454 TraceWitness.RamRaChunk
fingerprint 5c2f74bc571213d8 TraceWitness.RamValFinal
fingerprint d368e74fb39c8014 TraceWitness.RamWriteValue
fingerprint c6e2b5fa5cf3d62b TraceWitness.RdInc
fingerprint 542c73f78401ae40 TraceWitness.RdWa
fingerprint 0e1bf04e98720f2d TraceWitness.RdWriteValue
fingerprint 16f8fc9e57b51a06 TraceWitness.RegistersVal
fingerprint 26fb3656fab78610 TraceWitness.RightInstructionInput
fingerprint 9547ddab982315b4 TraceWitness.RightLookupOperand
fingerprint af302bf3b716c62c TraceWitness.Rs1Ra
fingerprint 29a4f6b037b2fcf5 TraceWitness.Rs1Value
fingerprint 175dde8c29486d8a TraceWitness.Rs2Ra
fingerprint 85a8de4459fac762 TraceWitness.Rs2Value
fingerprint f8c3be40072525e7 TraceWitness.ShouldBranch
fingerprint b365b519d2025a58 TraceWitness.UnexpandedPC
fingerprint 275f04a1715c1cf7 TraceWitness.addressChunk
fingerprint 39a9acb810d2d526 TraceWitness.addressChunkEntry
fingerprint 8f6f07c26ba26d91 TraceWitness.bytecodePc
fingerprint b77ea638e6842c05 TraceWitness.capturedDestination
fingerprint 1f30f14e0f5ab4be TraceWitness.capturedDestinationValue
fingerprint 67c2e555f63d68c9 TraceWitness.destinationRegisterAddress
fingerprint 50791eec803a0443 TraceWitness.finalRamWord
fingerprint 3830e7e29d3d4380 TraceWitness.finalTraceState
fingerprint 9dc9fb73e5ec6732 TraceWitness.initialRamWord
fingerprint b736bf76637cfb25 TraceWitness.initialRamWordFromState
fingerprint 99e00f93ced8df38 TraceWitness.instructionLookupIndex
fingerprint 67ae3df1b1ae272f TraceWitness.interleaveLookupOperands
fingerprint f9e620780e0449d4 TraceWitness.lookupIndex
fingerprint f69311f48fa3cdcd TraceWitness.overlayRamBytes
fingerprint c41992dc584319f0 TraceWitness.ramAccessAddress
fingerprint b56cd44df503a14a TraceWitness.ramImageWord
fingerprint 1cbb76f28ec95692 TraceWitness.rdValue
fingerprint 8750fcf9b680855e TraceWitness.remapRamAddress
fingerprint 06d3386dfa6edaa7 TraceWitness.remappedRamAddress
fingerprint 02e3f3277f09ccb5 TraceWitness.rowLookupOutput
fingerprint a988f22008f5ae72 TraceWitness.sourceRegisterAddress
fingerprint 33bf2422223b1ee9 VReg
fingerprint 6a51c8df842ef21a ValidRun
fingerprint fe381e70f29f9a3f WholeRun.Block
fingerprint ab3f694ac093b6e6 WholeRun.Block.FirstRowAt
fingerprint a9b91d6674ea5b4b WholeRun.Block.Runs
fingerprint 2983d17f3a038dee WholeRun.Block.start
fingerprint 6f460249612a26c7 WholeRun.BlockConforms
fingerprint fc194157d5bd9baf WholeRun.BlockEncoding
fingerprint 65b3a5982ea85882 WholeRun.BlockEncoding.decodedWord
fingerprint ece43c3b024c1098 WholeRun.BlockEncoding.isCompressed
fingerprint 5518fed26ba90a2d WholeRun.ElfLayout
fingerprint de4e872feb24a4b3 WholeRun.ElfSection
fingerprint d461610097afa6fd WholeRun.ElfSection.bytes
fingerprint a51020196f460d00 WholeRun.ElfSection.dataRanges
fingerprint 2882b8f0324bdfa2 WholeRun.ElfSection.endAddress
fingerprint 5b48fa85e9626245 WholeRun.ElfSection.overlapsCode
fingerprint 5938cd0e42bf7b87 WholeRun.ElfSections
fingerprint c4683541a5202971 WholeRun.ElfSections.layout?
fingerprint ec5ce1b13adc0e38 WholeRun.ElfSections.loaded
fingerprint fb52f307ba131b33 WholeRun.HaltObservation
fingerprint a405f873fc59eb47 WholeRun.HaltPrefix
fingerprint 1b0363385504cd5a WholeRun.HonestTrace.sail_reproduces
fingerprint 1348ccfbe62b98a1 WholeRun.JoltCustomInstruction.decode?
fingerprint 375a6f2e8dc24355 WholeRun.MappingSymbol
fingerprint 89edf4f321aa3464 WholeRun.MappingSymbol.ctorIdx
fingerprint b17baf33b5c90b02 WholeRun.NextIsHalt
fingerprint 32fcb6015b07c589 WholeRun.Related
fingerprint b06ce22c7310c005 WholeRun.RowFromParcel
fingerprint 7135a95ee2e370a8 WholeRun.SailHalted
fingerprint 2f021d76f2366dc5 WholeRun.blockInstrs
fingerprint e79dfa07d8557845 WholeRun.dataRangesFrom
fingerprint 767220dc37c53f84 WholeRun.decodeText
fingerprint 161000ff0a0a2891 WholeRun.haltSource
fingerprint 3835643eb3ad3077 WholeRun.instDecidableEqMappingSymbol
fingerprint cb3a8d4a544d75ab WholeRun.ioRegion
fingerprint b7d3b56606a03b34 WholeRun.lastByte
fingerprint 107d876bac3e7a78 WholeRun.mappingLe
fingerprint 56d11c9e4a714a8a WholeRun.memHigh
fingerprint a4b646d77af9963f WholeRun.memLow
fingerprint 9ed2818704ed2441 WholeRun.mergeRanges
fingerprint d4adedc4e53f4d67 WholeRun.mergeStep
fingerprint c3cfbe86c13fda84 WholeRun.patchAdvice
fingerprint 23589c4b6b01735d WholeRun.platformPma
fingerprint 9fd6ee77f32483df WholeRun.ramRegion
fingerprint 00271c152c1f2b53 WholeRun.rangeBytes
fingerprint 26642dda90b079f9 WholeRun.rowAt
fingerprint 68432efd28101fad WholeRun.sailInit
fingerprint 589bce4e9a7d420e WholeRun.sailRegs
fingerprint 534d6996de07db3a WholeRun.sailRun
fingerprint 93e05be3107f79d1 WholeRun.segmentsFrom
fingerprint 2bef265e289c477e WholeRun.textSegments
fingerprint 464908c551be12cf WitnessParams
fingerprint c7fadfc0b730abe3 WitnessParams.BytecodeDomainFor
fingerprint b8a87c986fb324b3 WitnessParams.bytecodeChunks
fingerprint be5dca6f6d4466cc WitnessParams.instructionChunks
fingerprint 852cdd5f68deed93 WitnessParams.preprocessedBytecodeSize
fingerprint 0e115ecbf2679f26 WitnessParams.ramChunks
fingerprint 1f757defa6466ea0 WitnessParams.ramSize
fingerprint fa910191a124f623 WitnessParams.traceLength
fingerprint 205c9a510c0fde6c WitnessParams.virtualInstructionChunks
fingerprint 11a7e0098045869e WitnessType
fingerprint 580d05d30a79a626 advance_pc
fingerprint 43dab136a4bc3712 adviceStepsBeforeStepN
fingerprint 041cc9ec441d71cb bv_abs
fingerprint fe10b3f016783dd0 bytecode_address_ok
fingerprint 3ffc0e23c37b119f bytecode_source_extents
fingerprint ae549925ed1df31d ctz
fingerprint f576c66eb08106eb divw_advice_value
fingerprint b69df07648bc48e0 expand_instruction
fingerprint 3da2498542f97cbd expand_program
fingerprint 2495bcc094565d9f get_first_pc
fingerprint e183d0600649042c honestTracerAdviceAtStepN
fingerprint 8100dad4d37c8c9a init_state
fingerprint 619a35078e554954 initialRam
fingerprint d8f56d5f97f9b1e7 initialRegisterValue
fingerprint f06b07ff88f3f7d6 instDecidableEqCircuitFlags
fingerprint 38d5e109d2bb0076 instDecidableEqInstructionFlags
fingerprint b5bb0b18313c1ec4 instDecidableEqJoltHaltKind
fingerprint 3d92133a4b1e941c instDecidableEqJoltHostIOMode
fingerprint 9bc1f0075dba59d7 instDecidableEqLookupTableKind
fingerprint f6ee7a635028a7fe instFintypeLookupTableKind
fingerprint 64355384f395a678 instFintypeRegister_joltConstraints
fingerprint 0b01814cce7e3c0c jolt_addiw_value64
fingerprint 65806fe32c9636d8 jolt_addw_value
fingerprint 8785d4c1a3dc12a3 jolt_andn_value
fingerprint a6a4992628992190 jolt_assert_eq
fingerprint f87098aefbc7910a jolt_jalr_target64
fingerprint 37621e5c85d895b1 jolt_movsign_value
fingerprint 132372cb6d2bd287 jolt_mulhu_value
fingerprint ada35d7c075d1a27 jolt_mulw_value
fingerprint 65225a4023e1f5a1 jolt_pext_nat
fingerprint 2cd228d55030a06b jolt_popcount_nat
fingerprint d1c054ea99cd57b6 jolt_slt_value
fingerprint 5ecc78863948bd27 jolt_sltu_value
fingerprint 0ae96e0e3ffc1f5e jolt_subw_value
fingerprint 680b872ec75d24ac jolt_virtual_muli_value
fingerprint 24ec3f45717ee4ad jolt_virtual_muliw_value
fingerprint a11376cddd378214 jolt_virtual_negate_if_value
fingerprint bad0644507950afa jolt_virtual_pext_signed_value
fingerprint 3af15c39ce170c1b jolt_virtual_pext_value
fingerprint a6fa253fedb4fe8c jolt_virtual_pow2_value
fingerprint 878610fbd3392126 jolt_virtual_pow2i_value
fingerprint e272031a7e8429ef jolt_virtual_pow2iw_value
fingerprint d7d456377a7d7b87 jolt_virtual_pow2w_value
fingerprint 00b535ca59ea2e3f jolt_virtual_rev8w_value
fingerprint 39584bb04b789b72 jolt_virtual_rotri_value
fingerprint 7718baf040ab9039 jolt_virtual_rotriw_value
fingerprint 6dfdc7cd4cf7e706 jolt_virtual_shift_data_b_value
fingerprint 9987b60434c65aaf jolt_virtual_shift_data_h_value
fingerprint 485de1766cc8739c jolt_virtual_shift_data_w_value
fingerprint 84a2417dcde1ba2b jolt_virtual_shift_right_bitmask_value
fingerprint 081b63e1c1fe9743 jolt_virtual_shift_right_bitmaski_value
fingerprint fc8f2f50baac280c jolt_virtual_shift_right_bitmaskw_value
fingerprint df3b5777bd0226ce jolt_virtual_sign_extend_word_value
fingerprint 92500fb11329fe27 jolt_virtual_sra_value
fingerprint 7b37453887ed824d jolt_virtual_srai_value
fingerprint 910e577b1ab88bd1 jolt_virtual_sraiw_value
fingerprint 89d9ac2b3f6ac2a3 jolt_virtual_sraw_value
fingerprint 562652807eb01392 jolt_virtual_srl_value
fingerprint ae8ec2c7ff6de1ec jolt_virtual_srli_value
fingerprint 582c127171d8c6c4 jolt_virtual_srliw_value
fingerprint ef40d7efb88ead30 jolt_virtual_srlw_value
fingerprint c75eee6006c37738 jolt_virtual_window_mask_b_value64
fingerprint 898b979c7ef221a0 jolt_virtual_window_mask_h_value64
fingerprint efc9ad8bd6be54ba jolt_virtual_window_mask_w_value64
fingerprint 36fc1fbeda029da1 jolt_virtual_xorrot_value
fingerprint 05dbb872a4dddb43 jolt_virtual_xorrotl1_value
fingerprint 209c79cfe1736623 jolt_virtual_xorrotw_value
fingerprint c277008699f821fe jolt_virtual_zero_extend_word_value
fingerprint a1f918943f4fdc75 jolt_xor_value
fingerprint b9ae28ef209dabf7 liftSail
fingerprint 1d053aa573a2d035 min_bytecode_address
fingerprint e78b18b40e4c5097 new_heap_end_le
fingerprint b825dca67b200960 pc_map_ok
fingerprint 8e90352a43010649 preprocess
fingerprint 8b6c8ac457868c54 program_image_len_words
fingerprint b0edda3fbaec338c ramPmaRegion
fingerprint 07fd55e8a9bd2140 readVReg
fingerprint 77181f8a8c3e78b0 rem_advice_value
fingerprint c9a2b2fee28be979 remw_advice_value
fingerprint f2726520fa4076ed sail_div_value
fingerprint a4badfaa30534473 sail_divuw_advice
fingerprint 609e2a1d7d34dec8 sail_divw_value
fingerprint c3e2e4965e6432c8 source_is_compressed
fingerprint c1cced456a51776c stamp_sequence
fingerprint 7ab7381186becc87 startOfExpansionContainingStepN
fingerprint b8e5aa562f61fd8b stepNOfTraceIsAdvice
fingerprint 5b80b8874de1084b stepNOfTraceIsStartOfNewExpansion
fingerprint d62f3d9d571cbfdd trimTrailingZeros
fingerprint 9b15d11c234592cd valid_run
fingerprint 895f61c5d680b2e4 writeVReg
"#
