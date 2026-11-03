# Constraints migration definitions: Step 1 review follow-up

Date: 2026-11-02.
The recorded Jolt pin is `5def437f`, and the migration target is `c6703570`.
The Lean base and HEAD are `5a4860483953e2c78050e14cf0ce034e60453741` (`5a48604`).
The diff is uncommitted.
All 20 approved changes are implemented, including change 20 and the repairs authorized by “Approved without asking”.
All ten required Step 1 build targets passed before this review follow-up.
Ari's review confirmed that the definitions match Jolt's code.
The follow-up changes only the approved completeness import and this report.
Paths below are relative to `JoltConstraints/`.
Source abbreviations are R = `crates/jolt-riscv/src/`, L = `crates/jolt-lookup-tables/src/`, and T = `tracer/src/instruction/`.
The cited sources were read with `git show c6703570:<path>`.

| Step | Changed or removed declarations, current lines unless marked base | Mapping and Jolt source |
|---|---|---|
| 1 | `witness.lean:22` `InstructionFlags` | Append `RightOperandIsRdWriteValue` after `IsNoop`; R`flags.rs` (`InstructionFlags`). |
| 2 | New `Constraints/RamAddrEqRs1PlusImmMinusLookupIfLoadStore.lean:14` `ramAddrEqRs1PlusImmMinusLookupIfLoadStore`; remove old file/definition `RamAddrEqRs1PlusImmIfLoadStore.lean:12` at base; `Constraints/All.lean:72` `ConstraintEquations`, renamed field at :79 and import | Add `+ LookupOutput` inside (01)'s guarded difference; `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs` (row 0). |
| 3 | `witness_helpers/ram_address.lean:16` `TraceWitness.ramAccessAddress` | LD/SD record wrapping `ea`; floor B/H/W record `ea - (ea & 7/6/4)`; T`floor_access.rs` (`addresses`), `crates/jolt-witness/src/witnesses/ram.rs` (`ram_access_address`). |
| 4 | `trace.lean:50` `TraceRow.ram_address` | Same recorded addresses as natural numbers; R`trace_row.rs` (`ram_address`), `crates/jolt-program/src/execution/trace.rs` (`ExecutionDimensions::from_rows`). |
| 5 | `Constraints/RightInstructionInputEqSelection.lean:14` `rightInstructionInputEqSelection` | Add destination-value flag times `RdWriteValue` to (33); `crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs` (`InputVirtualization::unbatched_relation`); (11) unchanged. |
| 6 | `witness_helpers/right_instruction_input.lean:16` `TraceWitness.RightInstructionInput` | Sum the three flag-guarded sources, so ShiftData gets rs2 + signed imm and LD gets captured rd; L`instructions/virt/shift_data_b.rs` and `instructions/riscv/ld.rs` (`to_instruction_inputs`). |
| 7 | `metadata.lean:15` `JoltMetadata.immediate` | Floor loads/stores and ShiftData use `imm.toInt`; T`format/format_{load,s,shift_data}.rs` (`NormalizedOperands::from`), `crates/jolt-program/src/expand/memory/shared.rs` (`LaneWindow::open`, `merge`). |
| 8 | `witness.lean:32` `LookupTableKind` | Remove all three retired names and append AddressOffsetB/H/W after VirtualXORROTL1; all 55 names and all seven instruction flags match target order; L`tables/mod.rs` (`LookupTableKind`). |
| 9 | `lookup_table.lean:173` `addressOffsetTableEntry`, :561 `lookupTableEntry`; remove `alignAddrTableEntry` (base :170), `halfwordAlignmentTableEntry` (:244), `wordAlignmentTableEntry` (:251) | Shared width argument; B/H/W widths 1/2/4 give `index & 7/6/4`; L`tables/address_offset.rs` (`AddressOffsetTable::materialize_entry`). |
| 10 | `metadata.lean:56` `JoltMetadata.instructionFlag` | LD gets only RdWriteValue routing; floor rows get LeftOperandIsRs1Value and RightOperandIsImm; ShiftData also retains RightOperandIsRs2Value; R`instructions/i/ld.rs`, `instructions/virt/{load,store,shift_data}_{b,h,w}.rs` (`jolt_instruction!`). |
| 11 | `metadata.lean:138` `JoltMetadata.opcodeFlag` | Floor loads/stores get Load/Store plus AddOperands; retired rows removed from AddOperands, WriteLookupOutputToRD and Assert; same R files as step 10. |
| 12 | `metadata.lean:266` `JoltMetadata.lookupTable` | Floor B/H/W loads and stores select AddressOffsetB/H/W; LD/SD remain none; ShiftData keeps its tables; L`instructions/virt/floor_access.rs` (`floor_access!`), `instructions/riscv/{ld,sd}.rs` (`impl_lookup_table!`). |
| 13 | `witness_helpers/lookup_index.lean:27` `TraceWitness.instructionLookupIndex` | Floor index is signed base + imm encoded in 128 bits; ShiftData interleaves value and wrapping address + imm; LD interleaves zero and captured rd; L`traits.rs` (`LookupQuery`), `instructions/virt/floor_access.rs`, `instructions/virt/shift_data_{b,h,w}.rs`, `instructions/riscv/{ld,sd}.rs`. |
| 14 | `witness_helpers/lookup_output.lean:18` `TraceWitness.rowLookupOutput` | Floor outputs `ea & 7/6/4`; ShiftData uses address + imm; LD/SD output zero; L`instructions/virt/floor_access.rs` (`floor_access!`) and `instructions/virt/shift_data_{b,h,w}.rs` (`to_lookup_output`). |
| 15 | `witness_helpers/right_lookup_operand.lean:15` `TraceWitness.RightLookupOperand` | Combined rows retain 128 bits; other rows recover the wrapped 64-bit right input by uninterleaving the index; L`traits.rs` (`LookupQuery::to_lookup_operands`), `crates/jolt-witness/src/witnesses/operands.rs` (`RightLookupOperand`). |
| 16 | `register_encoding.lean:45` `JoltRegisterEncoding.instructionIsCanonical` | Floor loads check dst/base, stores check base/value, ShiftData gains an immediate wildcard; T`format/format_{load,s,shift_data}.rs` (`FormatLoad`, `FormatS`, `FormatShiftData`). |
| 17 | `witness_helpers/rd_value.lean:14` `rdValue`, `rd_wa.lean:17` `RdWa`, `rs1_value.lean:18` `Rs1Value`, `rs2_value.lean:18` `Rs2Value`, `rs1_ra.lean:18` `Rs1Ra`, `rs2_ra.lean:18` `Rs2Ra` (all `TraceWitness`); `Constraints/BytecodeReadSelectors.lean:14/:49/:86` `bytecodeRs1Register`/`bytecodeRs2Register`/`bytecodeRdRegister`; `expansion_temp_liveness.lean:22` `ExpansionTempLiveness.readSources` | Floor loads use base/none/dst, stores use base/value/none; ShiftData roles unchanged; T`virtual_load_{b,h,w}.rs` (`RegisterStateLoad`), `virtual_store_{b,h,w}.rs` (`RegisterStateS`), `format/format_shift_data.rs`. |
| 18 | `witness_helpers/ram_write_value.lean:19` `TraceWitness.RamWriteValue`; `honest_witness_helpers/ram_read_value.lean:23` `HonestWitness.RamReadValue`, `memory_presence.lean:502` private `store_sequence_old_present`, :548 private `store_runtime_advice`, :564 `HonestTrace.store_word_present` | Loads use captured rd; stores write source value and read old word at ea for SD or `ea & ~7` for floor rows; one shared mask/address-function proof, with a runtime-advice identity for store rows; T`floor_access.rs` (`load`, `store`), T`sd.rs` (`SD::exec`), `crates/jolt-witness/src/witnesses/ram.rs` (`RamReadValue`, `RamWriteValue`). |
| 19 | `metadata.lean:236/:250` `opcodeFlag_load_cases`/`opcodeFlag_store_cases`; remove `opcodeFlag_load_requiresLD`/`opcodeFlag_store_requiresSD` (base :215/:220) | Conclusions now include the three floor constructors, with unchanged flag hypotheses; R`instructions/i/{ld,sd}.rs` and `instructions/virt/{load,store}_{b,h,w}.rs` (`jolt_instruction!`). |
| 20 | `witness_params.lean:45` `TraceRow.ram_address_lt`; `nextpc_frame.lean:209` `JoltNextPCFrame.ordinary_instruction`, :296 `load_doubleword_rule`, :304 `store_doubleword_rule`, :312 `load_instruction`, :325 `store_instruction`, :338 `floor_load_instruction`, :352 `floor_store_instruction`, :373 `instruction`; remove unused `memory_write` (base :287) | All recorded addresses remain 64-bit; classify memory rows by flags and compose read/write/MMU frame rules, with one floor-load and one floor-store lemma covering all widths; T`floor_access.rs` (`load`, `store`, `addresses`), T`ld.rs`/`sd.rs` (`LD::exec`, `SD::exec`), R`trace_row.rs` (`ram_address`), `tracer/src/emulator/mmu.rs` (`Mmu::load_doubleword`, `Mmu::store_doubleword`). |

The declaration inventory above includes these approved statement changes.
Equations (01) and (33) changed, and the corresponding (01) field in `ConstraintEquations` was renamed.
The classifier helpers have new names and wider conclusions, with unchanged flag hypotheses.
`store_word_present` replaces its SD equality and operand parameters with an accessed-address/instruction match covering SD and the three floor stores.
`ordinary_instruction` replaces the exclusions of LD and SD with false Load and Store flags, excluding the floor rows that `instruction` handles separately.
Every caller of a changed helper derives its premises from its existing instruction case, flag case, or honest-trace initialization and execution.
`TraceRow.ram_address_lt`, `JoltNextPCFrame.instruction`, and the native load/store frame statements are unchanged.
Every completeness and soundness theorem statement, `InLanguage`, the restrictions, and the assumption bundles are unchanged.
No new external premise was added.
The review follow-up changes only line 1 of `Completeness/RamAddrEqRs1PlusImmIfLoadStore.lean` to import `JoltConstraints.Constraints.RamAddrEqRs1PlusImmMinusLookupIfLoadStore`.
The remainder of that file is byte-for-byte unchanged.

The successful Step 1 build commands were:

| Command | Attempt | Result | Elapsed time |
|---|---:|---|---:|
| `lake build JoltConstraints.witness` | 1 | Exit 0 | 2.9s |
| `lake build JoltConstraints.lookup_table` | 1 | Exit 0 | 2.4s |
| `lake build JoltConstraints.metadata` | 2 | Exit 0 | 8.2s |
| `lake build JoltConstraints.register_encoding` | 1 | Exit 0 | 1.9s |
| `lake build JoltConstraints.trace` | 1 | Exit 0 | 2.9s |
| `lake build JoltConstraints.witness_helpers` | 1 | Exit 0 | 48.2s |
| `lake build JoltConstraints.Constraints.All` | 1 | Exit 0 | 69.3s |
| `lake build JoltConstraints.nextpc_frame` | 1 | Exit 0 | Not separately recorded |
| `lake build JoltConstraints.memory_presence` | 9 | Exit 0 | 7.8s |
| `lake build JoltConstraints.honest_witness` | 2 | Exit 0 | 16.2s |
| `lake build JoltConstraints.expansion_temp_liveness` | 1 | Exit 0 | 2.9s |

The earlier failed Step 1 build commands all exited 1.
`lake build JoltConstraints.metadata` attempt 1 failed on an unsolved classifier goal.
`lake build JoltConstraints.honest_witness` attempt 1 failed on missing floor cases in nextpc_frame and witness_params, and an unqualified `Virtaddr` in memory_presence.
`lake build JoltConstraints.memory_presence` attempts 1–8 exposed intermediate bind-reduction, dependent runtime-advice rewriting, and zero-mask simplification errors.
Those memory-presence errors were resolved in attempt 9.
The original `lake build JoltConstraints` attempt exited 1 after 1.1s during job computation, before compiling any module.
Its first error was `no such file or directory (error code: 4294967294)` for `JoltConstraints/Constraints/RamAddrEqRs1PlusImmIfLoadStore.lean`.
The approved import change removes that dependency-discovery blocker.

The approved review rerun invoked `lake build JoltConstraints` exactly once after the import change.
It exited 1 after 112.4 seconds and reported 17 failing modules.
The table lists every module in Lake's final failure list, in log order, with its first emitted diagnostic.
Full goal states and subsequent errors are preserved in `step1_full_2.log`.
Modules blocked by these failures are not counted as additional observed failures.

| Module under `JoltConstraints` | First error, with file, line and column |
|---|---|
| `Soundness.Layer5.TapeSemantics` | `Soundness/Layer5/TapeSemantics.lean:67:12`: Type mismatch |
| `Completeness.Rs2EqRamWriteIfStore` | `Completeness/Rs2EqRamWriteIfStore.lean:27:8`: Unknown identifier `JoltMetadata.opcodeFlag_store_requiresSD` |
| `Completeness.RightLookupEqRightInputOtherwise` | `Completeness/RightLookupEqRightInputOtherwise.lean:31:4`: Type mismatch: After simplification, term |
| `Completeness.RightLookupAdd` | `Completeness/RightLookupAdd.lean:61:18`: `simp` made no progress |
| `Completeness.RamReadEqRamWriteIfLoad` | `Completeness/RamReadEqRamWriteIfLoad.lean:27:8`: Unknown identifier `JoltMetadata.opcodeFlag_load_requiresLD` |
| `Completeness.RamReadEqRdWriteIfLoad` | `Completeness/RamReadEqRdWriteIfLoad.lean:27:8`: Unknown identifier `JoltMetadata.opcodeFlag_load_requiresLD` |
| `Completeness.RamAddrEqRs1PlusImmIfLoadStore` | `Completeness/RamAddrEqRs1PlusImmIfLoadStore.lean:20:4`: Unknown identifier `ramAddrEqRs1PlusImmIfLoadStore` |
| `Soundness.Layer4.WordEntry` | `Soundness/Layer4/WordEntry.lean:74:4`: Unknown identifier `alignAddrTableEntry` |
| `Completeness.RightInstructionInputEqSelection` | `Completeness/RightInstructionInputEqSelection.lean:12:82`: unsolved goals |
| `Completeness.Helpers.LookupWriteProofHelpers` | `Completeness/Helpers/LookupWriteProofHelpers.lean:689:4`: Invalid alternative name `VirtualAlignAddr`: Expected `JAL`, `JALR`, `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, `BGEU`, `FENCE`, `VirtualLoadB`, `VirtualLoadH`, `VirtualLoadW`, `VirtualStoreB`, `VirtualStoreH`, `VirtualStoreW`, `LD`, `SD`, `VirtualHostIO`, `VirtualAssertEQ`, `VirtualAssertValidDiv0`, `VirtualAssertValidUnsignedRemainder`, `VirtualAssertMulUNoOverflow`, or `VirtualAssertLTE` |
| `Completeness.LeftLookupOperandEqInstructionRaf` | `Completeness/LeftLookupOperandEqInstructionRaf.lean:30:2`: unsolved goals |
| `Completeness.RightLookupOperandEqInstructionRaf` | `Completeness/RightLookupOperandEqInstructionRaf.lean:51:14`: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached |
| `Completeness.Helpers.RamReadSelection` | `Completeness/Helpers/RamReadSelection.lean:96:4`: unsolved goals |
| `Soundness.Layer4.Inputs` | `Soundness/Layer4/Inputs.lean:34:33`: unsolved goals |
| `Soundness.Layer5.MemoryAddress` | `Soundness/Layer5/MemoryAddress.lean:40:40`: Unknown identifier `ramAddrEqRs1PlusImmIfLoadStore` |
| `Soundness.Layer2.ZeroRegister` | `Soundness/Layer2/ZeroRegister.lean:45:2`: unsolved goals |
| `Soundness.Layer4.Assertions` | `Soundness/Layer4/Assertions.lean:24:67`: Unknown constant `LookupTableKind.HalfwordAlignment` |

The seven pending classifier call sites remain unchanged:

- `Completeness/RamReadEqRamWriteIfLoad.lean:27`.
- `Completeness/RamReadEqRdWriteIfLoad.lean:27`.
- `Completeness/Rs2EqRamWriteIfStore.lean:27`.
- `Soundness/Layer6/PlainRow.lean:949` and `:954`.
- `Soundness/Layer7/TerminationStore.lean:703`.
- `Soundness/Layer7/StallSuffix.lean:3305`.

No mismatch was found between the approved semantic mappings and the inspected Jolt sources.
The (33) citation names `InputVirtualization::unbatched_relation`.
Equations (46) and (47) need no edits because their definitions already quantify over the appropriate flag types.
No source `sorry`, `native_decide`, `decide +kernel`, `bv_decide`, or heartbeat change was added.
The changed proof modules rebuilt in 9.9s for nextpc_frame, 4.8s for memory_presence, and 5.0s for witness_params during Step 1 validation.
Individual proof times were not collected.
Existing dependency warnings remain.

Logs are in `/private/tmp/claude-501/-Users-ari-biswas-Lean-jolt-qed-public/60614f14-d14c-46b9-a578-be2119998646/scratchpad/`.
The Step 1 logs follow `step1_<module>_<attempt>.log`.
The original full build is `step1_full_1.log`, and the approved rerun is `step1_full_2.log`.
`pgrep -fl lake` preceded each build series and found no other Lake process.
Two earlier scratch diagnostics using `lake env lean StoreGuardProbe.lean` exited 1 while investigating zero-mask simplification.
Their logs are `step1_store_guard_probe.log` and `step1_store_guard_probe2.log`.
The Jolt checkout remains untouched.
No failing proof has been repaired in this review follow-up.
No commit has been made.
This follow-up is complete and stopped for review.
