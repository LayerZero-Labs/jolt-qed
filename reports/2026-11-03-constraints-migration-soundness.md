# Constraints migration, Step 4: soundness repair and blockers

Date: 2026-11-03.
This report has two parts.
The first part, up to "Timing and final checks", is the first Step 4 run, which stopped at the blockers it describes.
The second part, [Continuation](#continuation-approved-restriction-extension-and-floor-memory-proofs-2026-11-03), records the work after Ari approved work item 5; it resolves those blockers, and `JoltInstance.soundness` is again proved with no `sorry`.
Statements in the first part about failing builds and blocked proofs describe that first run only.
The Jolt source pin remains `5def437f21a0006e13c063a03f0b5a7c9b93cd6f` (`5def437f`), and the migration target is `c6703570588e88033b8722bd4dec47c7f46f3b16` (`c6703570`).
The Lean starting commit and unchanged HEAD are `e29949809bbf2c54c315c2ca55ae3b90c7fd37a6`, on `review/audit-completeness-soundness`.
The working tree was clean at the start of this run.
Jolt's checkout was read with `git show c6703570:<path>` and was not modified.
The diff is uncommitted.

Step 4 is blocked and is not complete.
All six originally failing modules now build, as do their repaired independent callers.
The final `lake build JoltConstraints` exits 1 after 39.89 seconds, with two failing targets: `Soundness.Layer5.DeviceMemory` and `Soundness.Layer7.TerminationStore`.
Their existing proofs require facts that no longer follow when floor stores are present.
The soundness statement, `InLanguage`, assumptions, restrictions, execution definitions, witness definitions and completeness files are unchanged.
No new `sorry`, `bv_decide`, `native_decide`, `decide +kernel`, heartbeat increase or other limit increase was introduced.
The six completeness admissions and seven bytecode admissions are unchanged.
The top-level soundness axiom check cannot be completed because its rebuilt dependencies are missing.

## Blockers and review boundary

### Panic stores and device preservation

`row_panic_of_no_store` (`JoltConstraints/Soundness/Layer5/DeviceMemory.lean:207`) concludes that the panic flag is preserved when `¬ run.StoresPanicAt i`.
`UntrustedAnswerRun.StoresPanicAt` (`JoltConstraints/Soundness/Layer5/PanicRestriction.lean:39`) recognizes only SD.
For any floor-store row it is false, even if that row successfully stores to the panic word.
A floor byte store at the panic address, storing zero from an available register into an initially unpanicked device, succeeds and sets the panic flag to true.
The stored value does not matter to this device effect.
Thus the old intermediate claim that every non-SD instruction preserves the device is false, and the no-SD history cannot establish the panic-preservation step.
This is a kernel-checked local semantic counterexample, not a constructed satisfying witness for the complete soundness statement.
The scratch certificate uses panic address 8, termination address 16, `io_end` 24, output end and maximum output size 8, and zeros for the other layout fields.
Its device buffers are empty, its initial panic flag is false, its virtual-register values are zero, and its Sail state is arbitrary.
`VirtualStoreB (.vreg 0) (.vreg 1) 8 (.E_SAMO_Addr_Align ())` executes successfully and changes only the device panic field to true.
The certificate also checks Store=true, non-SD constructor inequality, and omission of every floor byte store from both completed-store predicates.
This synthetic layout tests the unrestricted frame helper; it is not claimed to be a generated layout or an initialized `UntrustedAnswerRun`.

The target sources are Jolt's tracer in `tracer/src/instruction/floor_access.rs` (`store`, `addresses`), `tracer/src/emulator/mmu.rs` (`Mmu::store_doubleword`), and `common/src/jolt_device.rs` (`JoltDevice::store`, `JoltDevice::load`).
They access the containing doubleword and set panic on a store to its first byte, regardless of the stored value.
The Lean floor-store cases in `JoltISA.execInstr` (`JoltBytecode/JoltISA/Semantics.lean:452`) have that same effect.

`JoltInstance.PanicStoresOne` (`JoltConstraints/Soundness/Layer5/PanicRestriction.lean:63`) still constrains only SD stores and LD loads.
The exact missing conditions are: a floor store touching panic must store the word 1; a later load, including a floor load, must avoid panic after any native or floor panic store; and completed-store history must record floor stores.
`TracerAddressChecks` only supplies access permissions and cannot imply any of these facts.
The new proved frame helper excludes all stores, but this blocked caller cannot prove that exclusion.
The blocked `row_panic_of_no_store` body is unchanged and still refers to the removed false non-SD helper, so its current diagnostic is an unknown identifier at line 222.
No false replacement or admission was inserted.

### Termination stores and stopping

`termination_effect_is_sd` (`JoltConstraints/Soundness/Layer7/TerminationStore.lean:646`) concludes that a represented cycle with a nonzero RAM effect is SD.
A floor store can have exactly that effect: a byte-store expansion can write 1 into the initially zero termination table word using `VirtualStoreB`.
It has Store=true, may have a nonzero RAM increment, and is not SD.
The widened `opcodeFlag_store_cases` therefore gives a disjunction containing that row, not the theorem's SD-only conclusion.
Its old classifier call at line 703 is unchanged because mechanically replacing it cannot prove the stated conclusion.
This example identifies the missing implication; this session does not construct a complete satisfying-witness counterexample.

`UntrustedAnswerRun.StoresTerminationAt` (`JoltConstraints/Soundness/Layer5/TerminationRestriction.lean:35`) records only SD.
`JoltInstance.TerminationThenStall` (`:59`) is triggered only by that history and forbids later termination loads only for LD.
After a floor termination store, the required trigger is absent, and a floor load is not covered even after a native store.
The exact missing facts are that every native or floor termination store enters the history, subsequent jumps satisfy the existing stopping discipline, and subsequent native or floor loads avoid termination.
The `TerminationTableZero` part of `DeviceMemoryStepAgreement` (`JoltConstraints/Soundness/Layer5/DeviceMemory.lean:80`) also cannot remain true after a nonzero floor termination store while the history still says no store occurred.
The permission checks and AddressOffset lookup do not supply those history or stopping facts.

### Work that remains dependent on review

A repair would need Ari's approval to extend `PanicStoresOne`, `TerminationThenStall`, `StoresPanicAt` and `StoresTerminationAt` to the containing doubleword of floor rows, or another approved treatment of their device effects.
No such change was made.
The Step 4 instruction explicitly lists a change to a restriction or model definition as a blocker, and `AGENTS.md` prohibits changing restrictions without review.
Because the cited implications are false, they were not restated as named `sorry` lemmas.

The floor-memory AddressOffset/alignment-to-execution proof and row append cases are not complete.
The old AlignAddr proof was removed with its retired row; the native address proof now uses the new constraint and zero lookup output.
It does not yet prove the corresponding floor-row address/execution theorem.
`RowStepKinds.row_kind` (`JoltConstraints/Soundness/Layer6/RowStepKinds.lean:29`) still needs floor alternatives after the repaired `PlainRow` excludes them.
Its caller `row_extension` (`JoltConstraints/Soundness/Layer6/RowStep.lean:37`) still needs the corresponding load/store execution cases.
Those modules are blocked by the device-memory import chain; the final two-target failure list is not a claim that these remaining cases already compile.
The floor-row replay invariant must first have a valid treatment of panic and termination history.

## Repairs and statement changes

Constraint (33)'s selected-input theorem now includes the independently flagged `RdWriteValue` term.
The no-op, register-input, LUI, AUIPC and branch callers prove that this flag vanishes for their instructions.
The shared `rdWriteInput_false_of_rs1Input` uses only an instruction and its rs1-input flag.
Jolt's verifier at the target implements this routing in `crates/jolt-claims/src/protocols/jolt/relations/instruction/input_virtualization.rs` (`InputVirtualization::unbatched_relation`).

`ramAddress_eq_sum` now takes `ramAddrEqRs1PlusImmMinusLookupIfLoadStore` and concludes that the encoded signed sum is reduced by `LookupOutput`.
The native LD/SD address theorems keep their statements and share one proof that their absent table makes this offset zero.
The field-injectivity argument is reused by `word_add_eq_of_field_sum`, whose inputs are only three words and a field equality.
Jolt's verifier gives the address argument in `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs` (`rv64_eq_constraint_rows`, row 0).

The `VirtualBinary` proof classification now carries an immediate on each of its three ShiftData constructors.
Its instruction and value projections use that immediate, and `virtualBinary_step` consequently covers the new instruction arity and address-plus-immediate semantics.
A single `virtualBinary_inputs` proof recovers the signed sum as a 64-bit word from the interleaved lookup operand, without a new nonwrapping premise or the completeness admissions.
Jolt's tracer implements this in `tracer/src/instruction/virtual_shift_data_b.rs` (`VirtualShiftDataB::exec`) and the H/W counterparts.
The `VirtualBinary.offset` helper is zero for extraction and conditional negation.

The obsolete AlignAddr and alignment-assertion table theorems, instruction-family classification and execution proof were deleted.
`AddressMask` now has only byte, halfword and word lane masks.
`OtherScalarKind` no longer has an alignment-assertion constructor, and `otherScalarKind?` carries ShiftData's immediate.
These are proof classifications, not changes to the ISA or witness model.

`PlainRow` now excludes all native and floor memory rows.
Its `plain_no_memory` caller uses the widened load/store classifiers.
The stall-source proof uses the same widened store classifier and the existing small control-flow classification.
Neither proof introduces a split over the full instruction set.

`execWithTapeAnswer_rule_of_device_relation_for_store` gains the floor-store preservation obligation already required by the underlying instruction frame.
Its callers supply that obligation from their existing arbitrary-byte-store preservation or constructor exclusions.
The false `execWithTapeAnswer_device_of_not_sd` is removed and replaced by the proved `execWithTapeAnswer_device_of_not_store`, which also excludes the three floor stores.
The HostIO caller proves both exclusions syntactically; the unrepairable panic caller remains unchanged as described above.
The unconditional device-relation frame retains its statement.

`RebuildAgreement.ram_address_eq` retains its statement and replaces duplicated LD/SD proofs with one register-agreement argument for every memory row.
It isolates VirtualMULI, the sole possible pending narrow-answer discrepancy, which has no RAM address.
The remaining rows use the same pre-state source values, including the three recorded floor offsets.

No other explicit theorem statement changes were made.
The changes to helper classifications alter the corresponding family-indexed statements as listed above, without changing their register-liveness or field-bound premises.
Every new helper is used by a repaired caller.

## Declaration inventory

Paths in this table are relative to `JoltConstraints/Soundness/`.
Numbers are current declaration lines unless explicitly marked as base lines.
Existing declarations with changed proofs or docstrings are included.

| File | Changed or added declarations |
|---|---|
| `Layer2/ZeroRegister.lean` | `canonicalNoOp_inputs` (32) |
| `Layer4/Inputs.lean` | new `rdWriteInput_false_of_rs1Input` (15); `instructionInputs_of_selected_bytecode` (37) |
| `Layer5/AddressMasks.lean` | `AddressMask` (17), `AddressMask.instruction` (22), `AddressMask.value` (31), `AddressMask.table` (38), `addressMask_canonical` (81), `addressMask_write_value` (93), `addressMask_step` (157) |
| `Layer5/Auipc.lean` | `auipc_write_value` (34) |
| `Layer5/LoadUpperImmediate.lean` | `lui_write_value` (33) |
| `Layer5/MemoryAddress.lean` | new `word_add_eq_of_field_sum` (42); `ramAddress_eq_sum` (60); new `native_memory_address_encoded` (145); `ld_address_encoded` (179), `sd_address_encoded` (194) |
| `Layer5/RegisterInputs.lean` | `RegisterAgreementOn.registerInputs` (80), `RegisterAgreementOn.immediateInputs` (131) |
| `Layer5/TapeSemantics.lean` | `execWithTapeAnswer_rule_of_device_relation_for_store` (41), `execWithTapeAnswer_rule_of_device_relation` (81), new replacement `execWithTapeAnswer_device_of_not_store` (98) |
| `Layer5/VirtualBinary.lean` | `VirtualBinary` (24), `VirtualBinary.instruction` (32), `VirtualBinary.value` (44), `VirtualBinary.table` (54), new `VirtualBinary.offset` (64), `virtualBinary_canonical` (82), new `virtualBinary_inputs` (97), `virtualBinary_write_value` (143), `virtualBinary_step` (191) |
| `Layer6/DivisionLayout.lean` | `source_advice_kind` (37) |
| `Layer6/PlainRow.lean` | `PlainRow` (48), `otherScalar_execution` (895), `plain_no_memory` (940) |
| `Layer6/PlainRowKinds.lean` | `OtherScalarKind` (159), `OtherScalarKind.instruction` (167), `OtherScalarKind.noTape` (174), `otherScalarKind?` (185) |
| `Layer6/RowStepTerminal.lean` | `append_host_row` (71) |
| `Layer7/StallSuffix.lean` | `stall_branch_lookup_decision` (838), `stable_stall_source_no_store` (3289) |
| `Layer7/TapeRebuild.lean` | `RebuildAgreement.ram_address_eq` (1747) |

Removed declarations, with declaration lines at base `e299498`:

| File | Removed declarations |
|---|---|
| `Layer4/Word.lean` | `lookupOutput_alignAddr_of_identity` (60) |
| `Layer4/Assertions.lean` | `lookupOutput_halfwordAlignment_of_identity` (22), `lookupOutput_wordAlignment_of_identity` (31) |
| `Layer5/AssertionsAlignment.lean` | entire retired file: `AlignmentAssertion` (18), `.instruction` (22), `.modulus` (29), `low_word_aligned` (33), `alignmentAssertion_canonical` (59), `alignmentAssertion_passes` (68), `alignmentAssertion_step` (110) |
| `Layer5/TapeSemantics.lean` | false `execWithTapeAnswer_device_of_not_sd` (87), replaced by the proved all-store exclusion helper |

`JoltConstraints.lean` removes only the retired `AssertionsAlignment` import.
`Layer6/PlainRow.lean` and `Layer6/PlainRowKinds.lean` remove the same import.
`methods/soundness.md` and `JoltConstraints/model_review.md` record the current partial result and review blockers.
The Step 4 instruction file remains because the step has not been reviewed or completed.

## Validation

Logs and scratch Lean files are in `/private/var/folders/36/6c7f3bpd7zgfw480v1y6b18w0000gn/T/codex-step4-e299498/scratchpad/`.
No scratch files were placed in the repository or `/tmp`.
Every build was preceded by a `pgrep -fl lake` check, but the agent mistakenly started `build08` while `build07` was still running after the check reported it.
The overlap caused a transient missing `VirtualBinary.olean` failure in `build07`.
Both invocations finished; `build08`, `build09` and the final serial build subsequently checked the affected modules again.
The overlap is a workflow violation, not evidence of an additional source blocker.
Two sandbox process-list failures were retried using the existing approved `pgrep -fl lake` escalation.
All subsequent checks ran serially.

| Log | Command | Exit and result |
|---|---|---|
| `build01` | `lake build JoltConstraints` | 1; reproduced all six initial failing modules |
| `build02` | `lake build JoltConstraints.Soundness.Layer2.ZeroRegister JoltConstraints.Soundness.Layer4.Inputs JoltConstraints.Soundness.Layer4.Word JoltConstraints.Soundness.Layer4.Assertions JoltConstraints.Soundness.Layer5.MemoryAddress JoltConstraints.Soundness.Layer5.RegisterInputs` | 1; the four Layer 2/4 modules passed; intermediate MemoryAddress and RegisterInputs errors |
| `build03` | `lake build JoltConstraints.Soundness.Layer5.MemoryAddress JoltConstraints.Soundness.Layer5.RegisterInputs` | 1; MemoryAddress passed, intermediate RegisterInputs error |
| `build04` | `lake build JoltConstraints` | 1; TapeSemantics tactic-layout error; RegisterInputs passed |
| `build05` | `lake build JoltConstraints` | 1; TapeSemantics passed and exposed additional callers, retired rows and device-history blockers |
| `build06` | `lake build JoltConstraints.Soundness.Layer5.VirtualBinary JoltConstraints.Soundness.Layer5.AddressMasks JoltConstraints.Soundness.Layer5.Auipc JoltConstraints.Soundness.Layer5.LoadUpperImmediate` | 1; only intermediate VirtualBinary simplification errors remained |
| `build07` | `lake build JoltConstraints` | 1; TapeRebuild, device-history blockers, and overlap-related dependency failures |
| `build08` | `lake build JoltConstraints` | 1; TapeRebuild and the two device-history blockers; repaired scalar callers passed |
| `build09` | `lake build JoltConstraints.Soundness.Layer7.TapeRebuild JoltConstraints.Soundness.Layer7.StallSuffix` | 0; completed with 8657 jobs |
| `build_final` | `lake build JoltConstraints` | 1 in 39.89s; only DeviceMemory and TerminationStore in the emitted failing-target list |
| `axioms_soundness` | `lake env lean <scratchpad>/SoundnessAxioms.lean` | 1 in 3.55s; missing rebuilt `Soundness/Layer7/TerminationStore.olean` prevents the top-level check |
| `axioms_repairs` | `lake env lean <scratchpad>/RepairAxioms.lean` | 0 in 6.54s; repaired helper and caller checks contain no `sorryAx` |
| `counterexamples06` | `lake env lean <scratchpad>/Counterexamples.lean` | 0 in 4.98s; successful panic-changing floor store and omitted history predicates |
| `profile_plain` | `lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 JoltConstraints/Soundness/Layer6/PlainRow.lean` | 0 in 9.16s |
| `profile_stall` | `lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 JoltConstraints/Soundness/Layer7/StallSuffix.lean` | 0 in 15.89s |

`SoundnessAxioms.lean` imports `JoltConstraints.Soundness.soundness` and requests `#print axioms JoltInstance.soundness`.
It emits no axiom list, because the import fails first.
The pre-migration four-axiom list must not be treated as a check of the migrated theorem.

The successful repair checks cover `instructionInputs_of_selected_bytecode`, `ld_address_encoded`, `sd_address_encoded`, `virtualBinary_step`, `addressMask_step`, `execWithTapeAnswer_device_of_not_store`, `JoltInstance.plain_row_step`, `JoltInstance.stable_stall_source_no_store`, and `untrustedAnswerLanguage_implies_inLanguage`.
Each uses a subset of `propext`, `sys_enable_experimental_extensions`, `Classical.choice` and `Quot.sound`.
None uses `sorryAx`.

The counterexample diagnostic had five earlier failed attempts (`counterexamples.log`, `counterexamples02.log` through `counterexamples05.log`).
They tested the same local claim and failed on reduction, simplification, or match elaboration; attempt 2 hit the unchanged 200000-heartbeat limit.
The final proof uses the concrete address-mask equality, the existing state-monad reductions and the doubleword-store equation, without raising a limit.
These diagnostic files are outside the repository and introduced no admitted source declaration.

## Timing and final checks

No individual successful proof was measured above ten seconds in the isolated validation.
`PlainRow`'s profile took 9.16 seconds for the whole module, with the slowest reported proof `trace_push_observations` (`Layer6/PlainRow.lean:406`) at 1.14 seconds.
`StallSuffix`'s profile took 15.89 seconds for the whole module, with the slowest reported proof `represented_last_branch_registers` (`Layer7/StallSuffix.lean:2894`) at 5.73 seconds.
Neither is a newly changed proof.
Earlier parallel Lake workers reported roughly 12–18 seconds for several Layer 5 modules and 27 seconds for `StallSuffix`; those are module wall times, not individual proof timings.
The final or isolated successful builds put every other changed proof module below ten seconds, including `VirtualBinary` at 5.4 seconds, `TapeSemantics` at 2.3 seconds and `TapeRebuild` at 8.6 seconds.
The final full build remains failed, so these timings do not establish completion of the soundness proof.

`git diff --check` passes.
A source diff confirms that `language.lean`, `Soundness/soundness.lean`, `Soundness/Assumptions.lean`, all three memory/panic/termination restriction files and `Completeness/` are unchanged from `e299498`.
The diff contains no added admission or prohibited tactic and no limit change.
The independent repairs and this report are ready for Claude's audit and Ari's review; no commit was made.

## Continuation: approved restriction extension and floor-memory proofs (2026-11-03)

Date: 2026-11-03.
The Jolt pin is `5def437f`, and the migration target is `c6703570`; Jolt's checkout was read only, with `git show c6703570:<path>`.
The Lean starting point is commit `e29949809bbf2c54c315c2ca55ae3b90c7fd37a6` (`e299498`) plus the uncommitted working tree of the first Step 4 run, which Ari authorized this run to continue from.
No repair of the first run was reverted.
The diff is uncommitted.

### Result

`lake build JoltConstraints` succeeds (exit 0, 8,837 jobs).
`#print axioms JoltInstance.soundness` prints:

```
'JoltInstance.soundness' depends on axioms: [propext, sys_enable_experimental_extensions, Classical.choice, Quot.sound]
```

These are the same four axioms as at `7096dca`; there is no `sorryAx`.
No `sorry` was added, and no blocker lemma was staged: every fact the proof needed followed from the existing premises and the approved restriction extension.
No `native_decide`, `decide +kernel` or `bv_decide` was added, and no heartbeat or other limit was raised.
Apart from the four restriction definitions of work item 5, the statement of `JoltInstance.soundness`, `InLanguage`, the assumptions, the other restrictions, the completeness files and every model definition are unchanged; `git diff HEAD` is empty for `language.lean`, `Soundness/soundness.lean`, `Soundness/Assumptions.lean`, `Completeness/` and `JoltBytecode/`.
The six completeness admissions and the seven bytecode admissions are unchanged.

### Restriction change (work item 5)

The four definitions were extended exactly as written in work item 5 of `methods/constraints-migration-step4.md`, with no other change to their bodies:

| Declaration | File and line | Change |
|---|---|---|
| `UntrustedAnswerRun.StoresPanicAt` | `Soundness/Layer5/PanicRestriction.lean:41` | New arm for `VirtualStoreB/H/W`, touching panic at `(base + imm) &&& ~~~7` |
| `JoltInstance.PanicStoresOne` | `Soundness/Layer5/PanicRestriction.lean:70` | New store arm (a floor store touching panic stores 1) and load arm (a floor load avoids panic after a panic store) |
| `UntrustedAnswerRun.StoresTerminationAt` | `Soundness/Layer5/TerminationRestriction.lean:37` | New arm for `VirtualStoreB/H/W`, touching termination at `(base + imm) &&& ~~~7` |
| `JoltInstance.TerminationThenStall` | `Soundness/Layer5/TerminationRestriction.lean:66` | New load arm: after a termination store, a floor load avoids termination at `(base + imm) &&& ~~~7` |

Each restriction's FIXME docstring has the sentence "The extension to VirtualLoadB/H/W and VirtualStoreB/H/W was approved by Ari on 2026-11-03, only to fit the new ISA."
The one-line docstrings of the two history predicates said "an SD"; they now name the floor stores and their accessed doubleword, to match the extended bodies.
For review: this docstring change was not spelled out in work item 5.

### Approach

`Soundness/Layer5/MemoryRows.lean` (new) classifies the memory rows once by width.
`MemoryWidth` has the cases `double` (LD, SD), `byte`, `halfword` and `word` (VirtualLoadB/H/W, VirtualStoreB/H/W).
`LoadRow` and `StoreRow` say that an instruction is the load or store row of a width, and `AccessRow` is either.
Each width fixes the accessed doubleword (`accessed`: `ea` for `double`, `ea &&& ~~~7` otherwise), the natural-alignment mask (`alignMask`: 7, 0, 1, 3), the lookup-offset mask (`offsetMask`: 0, 7, 6, 4) and the recorded RAM address (`recorded`: `ea - (ea &&& offsetMask)`, as in `TraceWitness.ramAccessAddress`).
Every later proof is stated over this classification, so no proof is repeated per row.

`AccessRow.address_encoded` is Jolt's own argument for constraint (01), the comment on row 0 in `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs` (`rv64_eq_constraint_rows`) at `c6703570`.
Constraint (01) gives `RamAddress = (base + imm) - LookupOutput` as an integer sum in the field.
The lookup output is zero for LD/SD and the AddressOffset entry `chosen &&& offsetMask` for a floor row, so it is at most 7.
RAM selection makes `RamAddress` zero or an in-domain word address, which `RamRegionFits` bounds by `2^64 - 8`.
The field bound then gives the integer equation, so the effective address does not wrap and the selected lookup address is the effective address itself.
Hence `RamAddress` is the recorded address; it is a multiple of 8, which forces the row's natural alignment (`aligned_of_recorded`) and makes the recorded address the accessed doubleword (`recorded_eq_accessed`, using the completeness helper `floor_recorded_address`).
For example, VirtualStoreH at `ea = 10` records `10 - 2 = 8`; at `ea = 11` it would record 9, which no RAM selection allows.

`row_panic_of_no_store` is now proved: a store row runs `Mmu.store_doubleword` at its accessed doubleword (`StoreRow.store_of_run`), which `¬ StoresPanicAt` keeps away from the panic word, and every other row keeps the whole device.
`termination_effect_is_store` (formerly `termination_effect_is_sd`) concludes that a nonzero RAM effect comes from a store row, and `termination_store_touches_termination` shows that row touches termination at its accessed doubleword.
The device load and store steps take the panic and termination facts from `LoadRow.panic_free`, `LoadRow.termination_free` and `StoreRow.panic_value`, the projections of the extended restrictions.

### Declarations added

| File | Declarations (line) |
|---|---|
| `Soundness/Layer5/MemoryRows.lean` (new) | `MemoryWidth` (35), `MemoryWidth.accessed` (43), `.alignMask` (50), `.offsetMask` (60), `.recorded` (69), `.table?` (75), private `MemoryWidth.low_bits_zero` (84), `MemoryWidth.recorded_toNat` (99), `.aligned_of_recorded` (109), `.recorded_eq_accessed` (124), `MemoryWidth.load` (139), `MemoryWidth.store` (151), `LoadRow` (165), `StoreRow` (173), `AccessRow` (179), `LoadRow.access` (184), `StoreRow.access` (190), `loadRow_of_flag` (198), `storeRow_of_flag` (212), `LoadRowFacts` (227), `StoreRowFacts` (249), `LoadRow.metadata` (268), `StoreRow.metadata` (276), `AccessRow.metadata` (286), `AccessRow.floor_inputs` (304), `AccessRow.not_tape` (319), `AccessRow.ramAccessAddress` (327), `LoadRow.exec_rule` (340), `StoreRow.exec_rule` (361), private `store_bind_result` (378), `StoreRow.store_of_run` (394), `LoadRow.address_checks` (418), `StoreRow.address_checks` (434), `StoreRow.panic_value` (450), `LoadRow.panic_free` (467), `LoadRow.termination_free` (484), `storeTouches` (504), `storeTouches_iff` (515), `storesTerminationAt_iff` (536), `storesPanicAt_iff` (544), private `AccessRow.lookup_offset` (569), `AccessRow.address_encoded` (635) |
| `Soundness/Layer5/LoadDoubleword.lean` | `LoadRow.canonical` (33) |
| `Soundness/Layer5/StoreDoubleword.lean` | `StoreRow.canonical` (38), replacing `sd_canonical` |
| `Soundness/Layer5/DeviceMemory.lean` | private `device_of_not_store_flag` (187) |

### Declarations changed

Every statement change below is to a helper; each new hypothesis is discharged by its callers from premises they already had.

| File | Declaration (current line; base `e299498` line) | Change |
|---|---|---|
| `Layer5/MemoryAddress.lean` | `addressSum_eq_of_field_eq` (23; 16), `address_toNat_eq_sum` (81; 98) | Made public, with docstrings; statements unchanged |
| `Layer5/LoadDoubleword.lean` | `load_ram_step` (48), formerly `ld_ram_step` (39) | Takes `LoadRow` of any width instead of `.LD`; address `width.accessed (base + imm)` |
| `Layer5/StoreDoubleword.lean` | `store_write_value` (49), formerly private `sd_write_value` (48); `store_ram_step` (71), formerly `sd_ram_step` (69) | Take `StoreRow` of any width; address `width.accessed (base + imm)`; `store_write_value` is now public |
| `Layer5/RamStoreAgreement.lean` | `store_ram_step_agreement` (23), formerly `sd_ram_step_agreement` (20) | As `store_ram_step` |
| `Layer5/DeviceMemory.lean` | `row_panic_of_no_store` (214; 207) | Statement unchanged; proof completed for all store rows |
| `Layer5/DeviceMemory.lean` | `ready_load_panic_false` (1452), formerly `ready_ld_panic_false` (1445) | Takes an address and a `panicFree` fact instead of `PanicStoresOne` and an LD |
| `Layer5/DeviceMemory.lean` | `device_load_image_bytes` (1499; 1492), private `device_load_read` (1581; 1576) | Take the accessed address, a destination, `panicFree` and `terminationFree` instead of the two restrictions and an LD |
| `Layer5/DeviceMemory.lean` | `load_device_step` (1695), formerly `ld_device_step` (1685); `store_device_step` (1801), formerly `sd_device_step` (1795) | Take `LoadRow`/`StoreRow` of any width; address `width.accessed (base + imm)`; the unused `atCut` hypothesis is dropped |
| `Layer5/DeviceMemory.lean` | `TerminationTableZero` (66), `DeviceMemoryStepAgreement` (82), `DeviceStoreResult` (104), `device_output_store_image` (761), `device_termination_store_image` (944) | Docstrings only: "SD" becomes "store row" where the floor stores now apply |
| `Layer6/MemoryRowExecution.lean` | `load_row_execution` (34; 33), `store_row_execution` (70; 68) | Take `LoadRow`/`StoreRow` and the accessed address; the unused `atCut` hypothesis is dropped |
| `Layer6/MemoryRowAppend.lean` | `append_memory_row` (50; 49) | The new-row termination disjunct is `storeTouches TouchesTermination step` instead of an SD-only match, so it covers floor stores |
| `Layer6/RowStepMemory.lean` | `append_load_row` (33), formerly `append_ld_row` (31); `append_store_row` (71), formerly `append_sd_row` (71) | Take `LoadRow`/`StoreRow` of any width |
| `Layer6/RowStepKinds.lean` | `row_kind` (30; 29) | The load and store alternatives are `∃ width destination base imm, LoadRow …` and `∃ width base source imm, StoreRow …`, classified by the Load and Store flags |
| `Layer6/RowStep.lean` | private `row_extension` (37) | Dispatches load and store rows to `append_load_row` and `append_store_row`; statement unchanged |
| `Layer6/PlainRow.lean` | `append_expansion_row_of_termination` (1135), `append_expansion_row` (1227) | The termination premise uses `storeTouches TouchesTermination` instead of an SD-only match; `append_expansion_row` keeps its statement |
| `Layer6/DivisionAppend.lean` | private `DivisionArithmeticRow.notStoresTerminationAt` (808) | Statement unchanged; proof via `storeTouches_iff` |
| `Layer7/TerminationStore.lean` | `UntrustedAnswerRun.truncate_storesTerminationAt` (140; 139), private `termination_effect_store_row` (762; 769), private `store_precedes_last_jump` (974; 984) | Statements unchanged; proofs use `storeTouches` |
| `Layer7/TerminationStore.lean` | private `termination_effect_is_store` (633), formerly `termination_effect_is_sd` (646) | Concludes `∃ width base value imm, StoreRow …` instead of an SD |
| `Layer7/TerminationStore.lean` | private `termination_store_touches_termination` (695), formerly `termination_sd_touches_termination` (708) | Takes a `StoreRow`; concludes `TouchesTermination` at the accessed doubleword |
| `Layer7/TerminationStore.lean` | `soundness_termination_store_exists` (806) | Docstring only |

### Declarations removed

All were unused after the generalization; line numbers are at base `e299498` unless marked.

| File | Removed declarations |
|---|---|
| `Layer5/MemoryAddress.lean` | `addressSum_eq_of_selected` (61), `addressSum_zero_of_unselected` (74), `addressSum_noWrap` (84), `ramAddress_encoded` (111), `ld_address_encoded` (121), `sd_address_encoded` (141), and the first run's `native_memory_address_encoded` (its line 145); `AccessRow.address_encoded` subsumes them |
| `Layer5/MemoryAccessRestriction.lean` | `ld_address_checks` (110), `sd_address_checks` (124); replaced by `LoadRow.address_checks` and `StoreRow.address_checks` |
| `Layer5/TerminationRestriction.lean` | `termination_next_ld_disjoint` (103); replaced by `LoadRow.termination_free` |
| `Layer5/StoreDoubleword.lean` | `sd_canonical` (40); replaced by `StoreRow.canonical` |
| `Layer5/DeviceMemory.lean` | private `sd_store_of_run` (181); replaced by `StoreRow.store_of_run` |
| `Layer6/RowStepKinds.lean` | `ld_ram_row_step` (92), `ld_device_row_step` (103), `sd_ram_row_step` (114), `sd_device_row_step` (126); each only forwarded to `append_ld_row` or `append_sd_row` with an unused address-region hypothesis |

For review: the three removed helper theorems in `MemoryAccessRestriction.lean` and `TerminationRestriction.lean` sit in restriction files, but they are proof helpers, not restrictions.

### Imports

`JoltConstraints.lean` imports the new `Soundness.Layer5.MemoryRows`.
`LoadDoubleword.lean` and `StoreDoubleword.lean` import `MemoryRows` in place of `RamAlignment`, `MemoryAddress`, `MemoryAccessRestriction` and `LookupWrite`, which `MemoryRows` imports.
`PlainRow.lean` and `TerminationStore.lean` import `MemoryRows`.
`MemoryRows` imports two completeness helpers, `Completeness.Helpers.FloorMemory` (for `floor_recorded_address`) and `Completeness.Helpers.RegistersReadProofHelpers` (for `rs1Operand?` and `rs2Operand?`); neither file was changed.

### Builds and checks

Logs are in `/Users/ari.biswas/Lean/scratch-step4b/`, outside the repository and `/tmp`.
Every build was preceded by `pgrep -fl lake`, which found no running Lake process, and builds ran serially.

| Log or command | Result |
|---|---|
| `build01.log`: `lake build JoltConstraints` at the start | exit 1; `Soundness.Layer5.DeviceMemory` (unknown `execWithTapeAnswer_device_of_not_sd`) and `Soundness.Layer7.TerminationStore` (unknown `opcodeFlag_store_requiresSD`), as the first run reported |
| `lake build …Layer5.TerminationRestriction …Layer5.PanicRestriction` | exit 0 after work item 5 |
| `lake build …Layer5.MemoryAddress …Layer5.RamAlignment`, `…Layer5.MemoryRows`, `…Layer5.LoadDoubleword …Layer5.RamStoreAgreement` | exit 0 |
| `lake build …Layer5.DeviceMemory` | exit 1 once (a structure field named `destination` shadowed the parameter), then exit 0 |
| `build02.log`, `build03.log`: `lake build JoltConstraints` | exit 1; dot notation on an `Or` term, then a `rw` across `Fin` and `Nat` indices; both fixed |
| `build04.log`, `build05.log`: `lake build JoltConstraints` | exit 0, 8,837 jobs |
| `lake build …Layer6.RowStepMemory` | exit 0 after adding `AccessRow.not_tape` |
| `build_final.log`: `lake build JoltConstraints` | exit 0, 8,837 jobs, 45 s wall |
| `axioms_final.log`: `lake env lean SoundnessAxioms.lean` (`#print axioms JoltInstance.soundness`) | the four axioms above |

`git diff --check` passes.
A search of the diff finds no added `sorry`, `native_decide`, `decide +kernel`, `bv_decide` or `maxHeartbeats`.
The `decide +kernel` uses in `Soundness/Layer5/DeviceMemoryObstruction.lean` are unchanged from `e299498`, already listed in "Proofs owed", and not used by `JoltInstance.soundness`.

### Timing

Each changed module was profiled with `lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=1000`, serially.
No proof takes more than about ten seconds.
No new or changed proof appears above the one-second threshold.
Module wall times are under ten seconds except `DeviceMemory.lean` at 15.1 seconds, whose slowest proofs are unchanged: `device_store_cases` 6.6 s, `loadImageBytes_image` 4.3 s and `loadImageBytes_read` 4.2 s.
`TerminationStore.lean` takes 7.7 seconds; its slowest proof is `soundness_termination_last_stall` at 1.7 s.

### Blockers

None.
Every fact the proof needed followed from the existing premises and the extended restrictions, so no lemma was staged with `sorry`.

### Review points

- `append_load_row` and `append_store_row` repeat their operand and append steps, as `append_ld_row` and `append_sd_row` did; this is listed under "Cleanup" in "Proofs owed".
- The five restriction projections in `MemoryRows.lean` (`LoadRow.address_checks`, `StoreRow.address_checks`, `StoreRow.panic_value`, `LoadRow.panic_free`, `LoadRow.termination_free`) have the same four-line shape, one per restriction arm.
- `MemoryWidth.load` and `MemoryWidth.store` carry an alignment exception that LD, SD and VirtualLoadB/StoreB ignore in execution, so that `LoadRow` and `StoreRow` are one existential for every width.
