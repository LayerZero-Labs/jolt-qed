# Constraints migration, Step 2: completeness repairs

Date: 2026-11-03.
The recorded Jolt pin is `5def437f21a0006e13c063a03f0b5a7c9b93cd6f`, and the migration target is `c6703570588e88033b8722bd4dec47c7f46f3b16`.
The Lean base and HEAD are `5a4860483953e2c78050e14cf0ce034e60453741` (`5a48604`), on `review/audit-completeness-soundness`, with reviewed Step 1 changes still uncommitted.
Jolt's checkout was read only through the target commit; it was not edited.
This report supersedes the earlier Step 2 wrap-stop reports.

The eleven originally failing completeness modules and their newly exposed register/PC helpers have been migrated.
After Ari's review, the two unrestricted bitvector wrap admissions were deleted and replaced by the approved bounds for a matching row of an honest trace.
The approved `WordEntry` repair removes the retired `alignAddr_entry` theorem without editing any other soundness module.
`lake build JoltConstraints.Completeness` passes in 10.2 seconds, and `lake build JoltConstraints.Completeness.completeness` passes in 10.5 seconds.
The complete lookup dispatch, constraint (39), the equation bundle and the assembled completeness theorem now build against the migrated definitions.
The diff remains uncommitted and awaits review.

## Statements and gaps

The only existing honest-witness statement changed is (01): `honestWitness_ramAddrEqRs1PlusImmIfLoadStore` was renamed to `honestWitness_ramAddrEqRs1PlusImmMinusLookupIfLoadStore` and now states the Step 1 constraint with `+ LookupOutput` in its residual.
Its original `sorry` remains.
Its module, root import, assembly field, theorem reference and documentation links were renamed together.
No public completeness theorem gained, lost or changed a premise.
The private `lookupIndex_right_eq_input` helper now takes an `HonestTrace` instead of a raw `Trace`; its only caller already has that certificate.
The main completeness statement, `InLanguage`, assumptions, restrictions, Step 1 definitions and `TracerAddressChecks` are unchanged by Step 2.
The only soundness edit is deletion of the retired-table `alignAddr_entry` theorem from `Soundness/Layer4/WordEntry.lean`, authorized in work item 8.
The three retired lookup-entry statements were replaced by AddressOffset statements with the same selected-table premise shape.
The helper definitions `rs1Operand?` and `rs2Operand?` now recognize the six floor constructors and ShiftData's extra immediate, matching the reviewed selectors.
All new proved helpers are used by the migrated proofs and are listed below.

Exactly two new `sorry` bodies remain, with Ari's express approval in work items 6 and 7.
`HonestTrace.floorAccess_address_nonneg` takes an honest trace, a row index and its in-bounds proof, and a certificate that `floorAccess?` selects that row's base and immediate.
It concludes only that the signed sum of that row's base value and immediate is nonnegative.
`HonestTrace.shiftData_address_noWrap` takes the corresponding honest-row data and a `shiftDataAddress?` certificate, and concludes that the signed sum lies in `[0, 2^64)`.
Their only differences from Ari's approved Lean snippets are explicit implicit parameters required by `autoImplicit false`, explicit array-bound proofs, and root namespace qualification.
The two selectors return the requested operands for exactly the six floor rows or three ShiftData rows, respectively, and `none` otherwise.
The former arbitrary-bitvector `floor_rightOperand_eq_inputs` and `shiftData_rightOperand_eq_input` admissions are deleted.
`encodedInt_cast` is proved for an integer within the chosen unsigned width, and is shared by both field-equality proofs.
`floor_lookup_sum` derives nonnegativity from the approved floor-row lemma and proves the 128-bit upper bound from the operand widths.
`shiftData_lookup_sum` derives both 64-bit bounds from the approved ShiftData-row lemma and rewrites the wrapping addition as `BitVec.ofInt 64`.
The caller supplies each row certificate from its instruction equation, so the admitted facts are used only in their six floor or three ShiftData cases.
These row-bound obligations remain false until #1949 is fixed, as approved; no claim is admitted about arbitrary bitvectors.
The rest of (08) and (11) is proved from those row-specific obligations without new public theorem premises.
The approved (01), (08) and (11) docstrings were copied unchanged and checked against the current plan.
No further wrap case required a new gap.
There are six completeness `sorry` bodies: the four existing gaps, (01), (37), (38) and RAM bounds, plus the two approved wrap lemmas.
`model_review.md` records all six, and `constraints.md` keeps (08) and (11) `FIXME` while restoring (39) to `DONE` after its integration build.
No `native_decide`, `decide +kernel`, `bv_decide`, limit increase or commit was introduced.

## Proof changes and target correspondence

The load proofs share `ramReadValue_of_load` and `ramWriteValue_of_load`, which use `opcodeFlag_load_cases`; the store proof uses `opcodeFlag_store_cases`.
They cover LD/SD and all six floor rows, whose flags are in `crates/jolt-riscv/src/instructions/i/ld.rs` and `instructions/virt/{load,store}_{b,h,w}.rs` (`jolt_instruction!`) at `c6703570`.
The floor-memory helpers prove the alignment guard and successful doubleword access once, then specialize the masks for B/H/W.
For natural-alignment masks 0/1/3 and offset masks 7/6/4, they prove the recorded address `ea - (ea & offset)` equals the accessed doubleword `ea & ~7`.
Zero-address load capture, impossible zero-address stores, RAM selection, PC preservation and other-register preservation follow from the existing execution certificate and MMU facts.
These match Jolt's tracer in `tracer/src/instruction/floor_access.rs` (`addresses`, `load`, `store`) and `tracer/src/emulator/mmu.rs` (`Mmu::load_doubleword`, `Mmu::store_doubleword`).
Native and floor register-frame proofs share the same doubleword continuation lemmas.

`addressOffset_entry` proves the table mask equation for arbitrary width, including wrapped effective addresses, without an execution or no-wrap premise.
Widths 1/2/4 give `AddressOffsetB/H/W` and masks 7/6/4, matching Jolt's prover in `crates/jolt-lookup-tables/src/tables/address_offset.rs` (`AddressOffsetTable::materialize_entry`) and `instructions/virt/floor_access.rs` (`floor_access!`).
The earlier isolated check is now superseded by a successful build of the complete `LookupEntryProofHelpers` module and (39).
Their original `Soundness.Layer4.WordEntry` import was retained.
The obsolete aligned-address theorem was removed from that imported module; the existing width-parametric AddressOffset proof remains the only new table identity.

Constraint (33) now proves selection of the sum of independently flagged inputs; its old flag-exclusivity helper was false for ShiftData and was removed.
This matches Jolt's verifier in `crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs` (`InputVirtualization::unbatched_relation`).
Constraint (41) now uses the index's right half directly, through `lookupAddressRight_eq_uninterleave`, with a Boolean choice for combined indices instead of an ISA-wide proof.
Constraint (11) proves the separate-index correspondence once, including LD's captured destination and the approved ShiftData arithmetic gap.
The operand definitions match Jolt's prover in `crates/jolt-witness/src/witnesses/operands.rs` and `crates/jolt-lookup-tables/src/traits.rs` (`LookupQuery::to_lookup_operands`).

## Declaration inventory

All paths below are relative to the repository; numbers in parentheses are final declaration lines.
New declarations, proof repairs, the approved rename and docstring-only changes are included.
The two PC rules and `ordinary_instruction` are in namespace `JoltPCFrame`.

| File | Added or changed declarations and lines |
|---|---|
| `JoltConstraints/Completeness/All.lean` | `honestWitness_constraintEquations` (15) |
| `JoltConstraints/Completeness/Helpers/AddressOffsetEntry.lean` | `floor_index_low` (12), `addressOffset_entry` (28) |
| `JoltConstraints/Completeness/Helpers/FloorMemory.lean` | `floor_access_guard` (15), `floor_load_access` (35), `floor_store_access` (59), `floor_recorded_address` (87) |
| `JoltConstraints/Completeness/Helpers/MemoryValueFacts.lean` | `ramReadValue_of_load` (10), `ramWriteValue_of_load` (32) |
| `JoltConstraints/Completeness/Helpers/LookupEntryProofHelpers.lean` | `lookupEntryCorrect_AddressOffsetB` (314), `lookupEntryCorrect_AddressOffsetH` (324), `lookupEntryCorrect_AddressOffsetW` (334), `lookupEntryCorrect_of_lookupTable` (855) |
| `JoltConstraints/Completeness/Helpers/LookupWriteProofHelpers.lean` | `lookup_row_write` (42) |
| `JoltConstraints/Completeness/Helpers/RamReadSelection.lean` | `captured_zero_retire` (33), `HonestTrace.load_zero_captured` (53), `HonestTrace.floor_load_properties` (86), `HonestTrace.floor_store_properties` (121), `HonestTrace.ram_accesses_valid` (155), `ramValues_zero_at_zero` (280), `ramWriteValue_eq_read_add_inc` (420) |
| `JoltConstraints/Completeness/Helpers/RegistersReadProofHelpers.lean` | `rs1Operand?` (22), `rs2Operand?` (55) |
| `JoltConstraints/Completeness/Helpers/RegistersValProofHelpers.lean` | `register42_load_word_preserves_other` (490), `register42_load_preserves_other` (512), `register42_store_word_preserves_sourceValue` (531), `register42_store_preserves_sourceValue` (549), `register42_instruction_preserves_other` (649) |
| `JoltConstraints/Completeness/Helpers/TracePCProofHelpers.lean` | `load_doubleword_rule` (144), `store_doubleword_rule` (151), `"jolt_pc_auto"` (159), `ordinary_instruction` (179) |
| `JoltConstraints/Completeness/RamAddrEqRs1PlusImmMinusLookupIfLoadStore.lean` | `honestWitness_ramAddrEqRs1PlusImmMinusLookupIfLoadStore` (33) |
| `JoltConstraints/Completeness/RamReadEqRamWriteIfLoad.lean` | `honestWitness_ramReadEqRamWriteIfLoad` (14) |
| `JoltConstraints/Completeness/RamReadEqRdWriteIfLoad.lean` | `honestWitness_ramReadEqRdWriteIfLoad` (14) |
| `JoltConstraints/Completeness/Rs2EqRamWriteIfStore.lean` | `honestWitness_rs2EqRamWriteIfStore` (14) |
| `JoltConstraints/Completeness/RightInstructionInputEqSelection.lean` | `honestWitness_rightInstructionInputEqSelection` (14) |
| `JoltConstraints/Completeness/LeftLookupOperandEqInstructionRaf.lean` | `honestWitness_leftLookupOperandEqInstructionRaf` (16) |
| `JoltConstraints/Completeness/RightLookupOperandEqInstructionRaf.lean` | `rightLookupRaf_select` (15), `honestWitness_rightLookupOperandEqInstructionRaf` (28) |
| `JoltConstraints/Completeness/RightLookupAdd.lean` | `floorAccess?` (16), `HonestTrace.floorAccess_address_nonneg` (47), `floor_lookup_sum` (63), `honestWitness_rightLookupAdd` (109) |
| `JoltConstraints/Completeness/RightLookupEqRightInputOtherwise.lean` | `shiftDataAddress?` (17), `HonestTrace.shiftData_address_noWrap` (46), `shiftData_lookup_sum` (61), `lookupIndex_right_eq_input` (79), `honestWitness_rightLookupEqRightInputOtherwise` (117) |
| `JoltConstraints/Completeness/Helpers/AddressSum.lean` | `encodedInt_cast` (13) |

Removed declarations, with their former lines at Lean base `5a48604`:

| File under `JoltConstraints/Completeness/` | Removed declaration and former line |
|---|---|
| `RightInstructionInputEqSelection.lean` | `rightOperandFlagsExclusive` (10), now false for ShiftData and unused |
| `Helpers/LookupEntryProofHelpers.lean` | `halfword_aligned` (263), `word_aligned` (267), unused after retirement |
| `Helpers/LookupEntryProofHelpers.lean` | `lookupEntryCorrect_AlignAddr` (317), `lookupEntryCorrect_HalfwordAlignment` (780), `lookupEntryCorrect_WordAlignment` (795) |
| `RamAddrEqRs1PlusImmIfLoadStore.lean` | `honestWitness_ramAddrEqRs1PlusImmIfLoadStore` (14), replaced by the approved renamed theorem |

Review deletions, with lines from the pre-review working tree:

| File | Removed declaration and former line |
|---|---|
| `JoltConstraints/Completeness/RightLookupAdd.lean` | `floor_rightOperand_eq_inputs` (35), superseded by the approved honest-row bound |
| `JoltConstraints/Completeness/RightLookupEqRightInputOtherwise.lean` | `shiftData_rightOperand_eq_input` (35), superseded by the approved honest-row bound |
| `JoltConstraints/Soundness/Layer4/WordEntry.lean` | `alignAddr_entry` (73), refers to the retired `alignAddrTableEntry` |

`JoltConstraints/Completeness.lean:30` changes only the (01) import.
The documentation changes are in `JoltConstraints/constraints.md`, `JoltConstraints/model_review.md` and this report.
The current migration plan remains until review, as it requests.

## Validation

Every Lake invocation was preceded by `pgrep -fl lake`; builds and diagnostic invocations ran serially.
All logs and result metadata are in the session scratchpad, not standalone `/tmp` files.
The scratchpad is `/private/tmp/claude-501/-Users-ari-biswas-Lean-jolt-qed-public/60614f14-d14c-46b9-a578-be2119998646/scratchpad`.
The ledger below records failed intermediate attempts as well as successful checks.
The first two full builds found 17 failures; the third, before this review, found six soundness failures.
The final full-library build for this review is run once after the approved changes.
Earlier failed results in the ledger are historical and do not describe the final source.
The earlier arithmetic diagnostics checked operand and layout facts; they did not construct a complete `HonestTrace` counterexample.

In commands, `<scratchpad>` denotes the directory above.
Each log is named by the ledger label plus `.log`; command, exit status and elapsed seconds are also saved in the matching `_result.json`.

| Log label | Command | Exit | Wall time | Observed result |
|---|---|---:|---:|---|
| `step2_wrap_check` | `lake env lean <scratchpad>/Step2WrapCheck.lean` | 0 | 6.9s | Passed |
| `step2_full_1` | `lake build JoltConstraints` | 1 | 25.7s | 17 failing modules before the latest approval |
| `step2_floor_add_wrap_check` | `lake env lean <scratchpad>/Step2FloorAddWrapCheck.lean` | 0 | 12.3s | Passed |
| `step2_full_2` | `lake build JoltConstraints` | 1 | 26.1s | 17 failing modules before the latest approval |
| `step2_nonwrap_1` | `lake build JoltConstraints.Completeness.RightInstructionInputEqSelection JoltConstraints.Completeness.RamReadEqRdWriteIfLoad JoltConstraints.Completeness.RamReadEqRamWriteIfLoad JoltConstraints.Completeness.Rs2EqRamWriteIfStore JoltConstraints.Completeness.LeftLookupOperandEqInstructionRaf JoltConstraints.Completeness.RightLookupOperandEqInstructionRaf` | 1 | 13.8s | Failed: `Completeness.RightLookupOperandEqInstructionRaf`, `Completeness.RamReadEqRdWriteIfLoad`, `Completeness.RamReadEqRamWriteIfLoad`, `Completeness.Rs2EqRamWriteIfStore` |
| `step2_nonwrap_2` | `lake build JoltConstraints.Completeness.RamReadEqRdWriteIfLoad JoltConstraints.Completeness.RamReadEqRamWriteIfLoad JoltConstraints.Completeness.Rs2EqRamWriteIfStore JoltConstraints.Completeness.RightLookupOperandEqInstructionRaf JoltConstraints.Completeness.Helpers.LookupWriteProofHelpers` | 1 | 15.1s | Failed: `Completeness.RightLookupOperandEqInstructionRaf`, `Completeness.RamReadEqRdWriteIfLoad`, `Completeness.RamReadEqRamWriteIfLoad` |
| `step2_nonwrap_3` | `lake build JoltConstraints.Completeness.RamReadEqRdWriteIfLoad JoltConstraints.Completeness.RamReadEqRamWriteIfLoad JoltConstraints.Completeness.RightLookupOperandEqInstructionRaf` | 1 | 10.2s | Failed: `Completeness.RightLookupOperandEqInstructionRaf`, `Completeness.RamReadEqRamWriteIfLoad`, `Completeness.RamReadEqRdWriteIfLoad` |
| `step2_raf_debug` | `lake env lean JoltConstraints/Completeness/RightLookupOperandEqInstructionRaf.lean` | 1 | 4.9s | Failed during proof development |
| `step2_nonwrap_4` | `lake build JoltConstraints.Completeness.RamReadEqRdWriteIfLoad JoltConstraints.Completeness.RamReadEqRamWriteIfLoad JoltConstraints.Completeness.RightLookupOperandEqInstructionRaf` | 1 | 13.2s | Failed: `Completeness.RamReadEqRdWriteIfLoad`, `Completeness.RamReadEqRamWriteIfLoad` |
| `step2_nonwrap_5` | `lake build JoltConstraints.Completeness.RamReadEqRdWriteIfLoad JoltConstraints.Completeness.RamReadEqRamWriteIfLoad` | 0 | 10.1s | Passed |
| `step2_floor_1` | `lake build JoltConstraints.Completeness.Helpers.FloorMemory` | 1 | 9.0s | Failed: `Completeness.Helpers.FloorMemory` |
| `step2_floor_2` | `lake build JoltConstraints.Completeness.Helpers.FloorMemory` | 1 | 6.4s | Failed: `Completeness.Helpers.FloorMemory` |
| `step2_floor_3` | `lake build JoltConstraints.Completeness.Helpers.FloorMemory JoltConstraints.Completeness.RamReadEqRdWriteIfLoad JoltConstraints.Completeness.RamReadEqRamWriteIfLoad` | 1 | 7.3s | Failed: `Completeness.Helpers.MemoryValueFacts` |
| `step2_ram_1` | `lake build JoltConstraints.Completeness.Helpers.RamReadSelection JoltConstraints.Completeness.RamReadEqRdWriteIfLoad JoltConstraints.Completeness.RamReadEqRamWriteIfLoad` | 1 | 21.2s | Failed: `Completeness.Helpers.RamReadSelection` |
| `step2_ram_2` | `lake build JoltConstraints.Completeness.Helpers.RamReadSelection` | 1 | 13.6s | Failed: `Completeness.Helpers.RamReadSelection` |
| `step2_completeness_1` | `lake build JoltConstraints.Completeness` | 1 | 21.9s | Failed: `Soundness.Layer4.WordEntry`, `Completeness.RamAddrEqRs1PlusImmIfLoadStore`, `Completeness.RightLookupEqRightInputOtherwise`, `Completeness.RightLookupAdd`, `Completeness.Helpers.TracePCProofHelpers` |
| `step2_pc_1` | `lake build JoltConstraints.Completeness.Helpers.TracePCProofHelpers` | 0 | 15.7s | Passed |
| `step2_offsets_1` | `lake build JoltConstraints.Completeness.Helpers.AddressOffsetEntry` | 1 | 3.5s | Failed: `Completeness.Helpers.AddressOffsetEntry` |
| `step2_nonwrap_6` | `lake build JoltConstraints.Completeness.Helpers.AddressOffsetEntry JoltConstraints.Completeness.NextUnexpandedPCUpdateOtherwise JoltConstraints.Completeness.NextUnexpandedPCEqLookupIfShouldJump JoltConstraints.Completeness.NextPCEqPCPlusOneIfInline` | 0 | 12.9s | Passed |
| `step2_offsets_instances` | `lake env lean <scratchpad>/Step2AddressOffsetCheck.lean` | 0 | 6.6s | Passed |
| `step2_wrap_1` | `lake build JoltConstraints.Completeness.RamAddrEqRs1PlusImmMinusLookupIfLoadStore JoltConstraints.Completeness.RightLookupAdd JoltConstraints.Completeness.RightLookupEqRightInputOtherwise` | 1 | 12.0s | Failed: `Completeness.RightLookupEqRightInputOtherwise` |
| `step2_wrap_2` | `lake build JoltConstraints.Completeness` | 1 | 20.0s | Failed: `Soundness.Layer4.WordEntry`, `Completeness.Helpers.RegistersValProofHelpers` |
| `step2_registers_1` | `lake build JoltConstraints.Completeness` | 1 | 26.0s | Failed: `Soundness.Layer4.WordEntry`, `Completeness.Helpers.RegistersReadProofHelpers` |
| `step2_registers_2` | `lake build JoltConstraints.Completeness` | 1 | 22.0s | Failed: `Soundness.Layer4.WordEntry` |
| `step2_profile_lookup` | `lake env lean -Dprofiler=true JoltConstraints/Completeness/Helpers/LookupWriteProofHelpers.lean` | 0 | 10.3s | Passed |
| `step2_profile_pc` | `lake env lean -Dprofiler=true JoltConstraints/Completeness/Helpers/TracePCProofHelpers.lean` | 0 | 13.6s | Passed |
| `step2_profile_registers` | `lake env lean -Dprofiler=true JoltConstraints/Completeness/Helpers/RegistersValProofHelpers.lean` | 0 | 15.2s | Passed |
| `step2_profile_ram` | `lake env lean -Dprofiler=true JoltConstraints/Completeness/Helpers/RamReadSelection.lean` | 0 | 11.9s | Passed |
| `step2_full_3` | `lake build JoltConstraints` | 1 | 21.4s | Failed: `Soundness.Layer4.WordEntry`, `Soundness.Layer5.TapeSemantics`, `Soundness.Layer4.Inputs`, `Soundness.Layer4.Assertions`, `Soundness.Layer5.MemoryAddress`, `Soundness.Layer2.ZeroRegister` |
| `step2_timing_registers` | `lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 JoltConstraints/Completeness/Helpers/RegistersValProofHelpers.lean` | 0 | 17.1s | Passed; individual declaration timings |
| `step2_timing_pc` | `lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 JoltConstraints/Completeness/Helpers/TracePCProofHelpers.lean` | 0 | 15.7s | Passed; individual declaration timings |
| `step2_review_word_1` | `lake build JoltConstraints.Completeness.Helpers.LookupEntryProofHelpers` | 0 | 34.4s | Passed |
| `step2_review_wrap_1` | `lake build JoltConstraints.Completeness.RightLookupAdd JoltConstraints.Completeness.RightLookupEqRightInputOtherwise` | 1 | 3.9s | Failed: `Completeness.Helpers.AddressSum` |
| `step2_review_wrap_2` | `lake build JoltConstraints.Completeness.RightLookupAdd JoltConstraints.Completeness.RightLookupEqRightInputOtherwise` | 0 | 12.6s | Passed |
| `step2_review_completeness_1` | `lake build JoltConstraints.Completeness` | 0 | 10.2s | Passed |
| `step2_review_assembly_1` | `lake build JoltConstraints.Completeness.completeness` | 0 | 10.5s | Passed |
| `step2_review_timing_entries` | `lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 JoltConstraints/Completeness/Helpers/LookupEntryProofHelpers.lean` | 0 | 25.5s | Passed |
| `step2_review_axioms` | `lake env lean <scratchpad>/Step2ReviewAxioms.lean` | 0 | 6.0s | Passed |
| `step2_review_full_1` | `lake build JoltConstraints` | 1 | 24.3s | Failed: `Soundness.Layer5.TapeSemantics`, `Soundness.Layer4.Inputs`, `Soundness.Layer4.Word`, `Soundness.Layer4.Assertions`, `Soundness.Layer5.MemoryAddress`, `Soundness.Layer2.ZeroRegister` |

## Timing

Four affected helper modules took about ten seconds or more, so all four were checked with Lean's profiler.
`LookupWriteProofHelpers.lean` took 12 seconds in a build and 10.3 seconds in the standalone profile, including 3.36 seconds importing dependencies.
`TracePCProofHelpers.lean` took 12 seconds in a build and 13.6 seconds in the standalone profile, including 3.41 seconds importing dependencies.
`RegistersValProofHelpers.lean` took 14 seconds in a build and 15.2 seconds in the standalone profile, including 3.43 seconds importing dependencies.
`RamReadSelection.lean` took about 10 seconds in a build and 11.9 seconds in the standalone profile, including 3.37 seconds importing dependencies.
These are whole-module wall times, not individual proof times.
Nested trace profiling separated individual declaration times in the two larger modules.
`JoltPCFrame.ordinary_instruction` took 9.76 seconds, approximately the reporting threshold.
`register42_instruction_preserves_other` took 5.14 seconds; the slowest register declaration was the unchanged `register42_prepareSource_preserves_sourceValue` at 6.51 seconds.
Before the newly unblocked lookup-entry module was checked, no measured individual declaration exceeded ten seconds.
The lookup-write and RAM-selection module times excluding imports were below ten seconds, so their individual proofs were also below that threshold in those runs.
The ordinary profiler records nested tactic categories, so its cumulative numbers must not be added or attributed to a single declaration.
No heartbeat or other limit was changed; the pre-existing limits of 1000000 in `LookupWriteProofHelpers` and 400000 in `TracePCProofHelpers` remain unchanged.

The newly unblocked `LookupEntryProofHelpers.lean` built in 29 seconds and its nested-profile invocation took 25.5 seconds.
The following table lists every proof in that profile with elapsed time above ten seconds, including unchanged proofs.
These are overlapping wall-clock intervals under Lean's asynchronous elaborator, not additive CPU measurements.
The log is `step2_review_timing_entries.log`; no performance repair or limit change was made.

| Declaration in `JoltConstraints/Completeness/Helpers/LookupEntryProofHelpers.lean` | Line | Elaboration wall time |
|---|---:|---:|
| `lookupEntryCorrect_RangeCheck` | 137 | 14.73s |
| `lookupEntryCorrect_And` | 145 | 13.17s |
| `lookupEntryCorrect_Or` | 151 | 13.14s |
| `lookupEntryCorrect_Xor` | 157 | 13.15s |
| `lookupEntryCorrect_Andn` | 163 | 12.94s |
| `lookupEntryCorrect_SignedLessThan` | 169 | 13.30s |
| `lookupEntryCorrect_UnsignedLessThan` | 176 | 13.28s |
| `lookupEntryCorrect_SignedGreaterThanEqual` | 183 | 13.05s |
| `lookupEntryCorrect_UnsignedGreaterThanEqual` | 190 | 13.02s |
| `lookupEntryCorrect_Equal` | 197 | 13.20s |
| `lookupEntryCorrect_NotEqual` | 204 | 13.03s |
| `lookupEntryCorrect_SignExtendWord` | 274 | 13.73s |
| `lookupEntryCorrect_UpperWord` | 284 | 12.97s |
| `lookupEntryCorrect_LowerHalfWord` | 291 | 12.94s |
| `lookupEntryCorrect_RangeCheckAligned` | 299 | 13.02s |
| `lookupEntryCorrect_AddressOffsetB` | 314 | 13.11s |
| `lookupEntryCorrect_AddressOffsetH` | 324 | 13.14s |
| `lookupEntryCorrect_AddressOffsetW` | 334 | 13.11s |
| `lookupEntryCorrect_SignMask` | 340 | 12.98s |
| `lookupEntryCorrect_VirtualNegateIf` | 346 | 12.93s |
| `lookupEntryCorrect_Pow2` | 352 | 13.24s |
| `lookupEntryCorrect_Pow2W` | 360 | 13.23s |
| `lookupEntryCorrect_ShiftRightBitmask` | 368 | 13.36s |
| `lookupEntryCorrect_ShiftRightBitmaskW` | 376 | 12.99s |
| `lookupEntryCorrect_ShiftDataB` | 383 | 12.83s |
| `lookupEntryCorrect_ShiftDataH` | 389 | 12.96s |
| `lookupEntryCorrect_ShiftDataW` | 395 | 12.96s |
| `lookupEntryCorrect_WindowMaskB` | 401 | 12.96s |
| `lookupEntryCorrect_WindowMaskH` | 407 | 12.88s |
| `lookupEntryCorrect_WindowMaskW` | 413 | 12.86s |
| `lookupEntryCorrect_VirtualXORROTL1` | 419 | 12.95s |
| `lookupEntryCorrect_VirtualXORROT32` | 425 | 12.92s |
| `lookupEntryCorrect_VirtualXORROT24` | 431 | 12.95s |
| `lookupEntryCorrect_VirtualXORROT16` | 437 | 12.95s |
| `lookupEntryCorrect_VirtualXORROT63` | 443 | 12.95s |
| `lookupEntryCorrect_VirtualXORROTW16` | 449 | 12.88s |
| `lookupEntryCorrect_VirtualXORROTW12` | 455 | 12.92s |
| `lookupEntryCorrect_VirtualXORROTW8` | 461 | 12.94s |
| `lookupEntryCorrect_VirtualXORROTW7` | 467 | 12.88s |
| `lookupEntryCorrect_VirtualXORROTW22` | 473 | 12.88s |
| `lookupEntryCorrect_VirtualXORROTW19` | 479 | 12.94s |
| `lookupEntryCorrect_VirtualXORROTW6` | 485 | 12.95s |
| `lookupEntryCorrect_VirtualRev8W` | 491 | 12.94s |

## Axiom checks

`Step2ReviewAxioms.lean` imports the assembled completeness module and prints both approved row statements and the relevant axiom dependencies.
The printed statements match the approved honest-trace row bounds, including the instruction selector and in-bounds certificate.
`encodedInt_cast` depends only on `propext` and `Quot.sound`.
`addressOffset_entry` depends on `propext`, `Classical.choice` and `Quot.sound`.
Constraint (39) depends on `propext`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.
Constraints (08), (11) and `JoltInstance.completeness` additionally depend on `sorryAx`, as expected from the recorded gaps.
A source search finds exactly six completeness `sorry` bodies and no remaining declaration of either unrestricted bitvector admission.

## Final build and remaining soundness work

The required final `lake build JoltConstraints` ran once on this review and exited 1 in 24.3 seconds.
All six observed failures are in soundness; the completeness root, equation bundle and assembled completeness theorem were rebuilt successfully in the same run.
The final log is `step2_review_full_1.log`, with result metadata in `step2_review_full_1_result.json` and this inventory in `step2_review_full_1_first_errors.json`.
The newly exposed `Soundness.Layer4.Word` failure still refers to the retired AlignAddr table and theorem; that module was left unchanged under the Step 2 boundary.

| Failing module under `JoltConstraints` | First error | Module time |
|---|---|---:|
| `Soundness.Layer5.TapeSemantics` | `JoltConstraints/Soundness/Layer5/TapeSemantics.lean:67:12`: Type mismatch | 3.5s |
| `Soundness.Layer4.Inputs` | `JoltConstraints/Soundness/Layer4/Inputs.lean:34:33`: unsolved goals | 6.3s |
| `Soundness.Layer4.Word` | `JoltConstraints/Soundness/Layer4/Word.lean:62:67`: Unknown constant `LookupTableKind.AlignAddr` | 6.4s |
| `Soundness.Layer4.Assertions` | `JoltConstraints/Soundness/Layer4/Assertions.lean:24:67`: Unknown constant `LookupTableKind.HalfwordAlignment` | 6.4s |
| `Soundness.Layer5.MemoryAddress` | `JoltConstraints/Soundness/Layer5/MemoryAddress.lean:40:40`: Unknown identifier `ramAddrEqRs1PlusImmIfLoadStore` | 6.7s |
| `Soundness.Layer2.ZeroRegister` | `JoltConstraints/Soundness/Layer2/ZeroRegister.lean:45:2`: unsolved goals | 7.3s |

No soundness module other than the approved `WordEntry` file was edited.
The remaining failing proofs are left for Step 3.
Modules blocked by failed dependencies are not counted as additional observed failures.
The final full log contains the complete goal states and later diagnostics.
A comparison against the pre-review snapshot confirms that Step 1 definitions, the public completeness statements and every other soundness file were preserved.
`git diff --check` passes.
Stop for review.
