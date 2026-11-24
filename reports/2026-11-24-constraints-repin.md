# JoltConstraints repin to ff6fc6568

Date: 2026-11-24.
Jolt revision inspected: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean baseline: `3522261`, branch `split/c-constraints`.
This is a working report; the repin and its validation are incomplete.
Local commit `877356e` records the checked halt/RAM constraint interface and generator equivalences.
No push, branch switch, or change under `JoltBytecode/` or `LeanRV64D/` has occurred.

## Source review and baseline

I read the bytecode repin report, its statement inventory, and the constraint-generator diff report before editing.
I inspected the pinned `specs/halt-end-rule.md`, `PublicIoMemory::new`, `write_protected_word_intervals`, and the new bytecode shared-memory APIs.
The baseline build through `track-t-build.sh lake build JoltConstraints` found missing `JoltSuccess`/`Panic` cases in register canonicalization and destination capture, and obsolete device-relation frame calls in `Soundness/Layer5/TapeSemantics.lean`.
The baseline log is `.constraints-repin-baseline.log`.

## Changes in progress

`translation/program.lean` separates public claim bytes into `JoltPublicIo`.
This record describes the verifier's statement, not an execution-side copy of I/O memory.
The execution device remains the bytecode model's two-field `JoltDevice`.
`JoltInstance.initial_state` now invokes `JoltISA.initialState` to install shared input/advice bytes and the code guard, after constructing the bootstrap RAM/register state.
`translation/witness_helpers/ram_state.lean` reads both initial and final RAM words directly from shared memory, including the I/O window and gap.
It no longer overlays device arrays or synthesizes flag words.
`Trace.matches_outputs` extracts final bytes with `JoltDevice.outputsOf`.

`translation/witness.lean` adds the real `Halt`/`HaltPanic` flags and removes `ShouldJump` and `RamHammingWeight`.
`translation/metadata.lean`, `register_encoding.lean`, and `witness_helpers/rd_value.lean` account for both halt instructions.
The source ISA and expansion dispatch now include `jolt.success`.
The existing EBREAK expansion already uses the bytecode project's new panic program.

The row-14 definition is renamed to `nextUnexpandedPCEqLookupIfJump` and uses `OpFlags.Jump`.
`Constraints/HaltEndRule.lean` states row 21 with the public panic bit and genuine halt columns.
`Constraints/RamWriteProtected.lean` defines public C from the code, input, advice and canary word intervals, and states its increment equation.
Its code-region construction reads each source expansion's last row, where sequence stamping puts the source compression flag.
`Constraints/RamAccessCount.lean` states the global selector-sum equation.
`ConstraintEquations` includes both new RAM claims and the halt lane and removes both retired RAM Hamming claims.
The corresponding retired constraint and witness-helper files are deleted.
`RamReadData.lean` restricts the public mask to `[input_start, output_end)` and emits input/output words only.

`ConstraintGen/Semantics.lean` reads halt columns from the witness.
Its remaining explicit extra input is public mask C; `ConstraintEquations.generated` fixes C to the model's public mask.
`ConstraintGen/Equiv.lean` replaces all four old admissions with proofs or, for coverage, a statement restricted to modelled kinds.
Coverage includes both halt kinds and explicitly excludes the two inline-only kinds `VirtualXORROT2` and `VirtualXORROT61`.
The generator equivalences compile at local commit `877356e`.
No generated data file has changed.

## Statement changes in progress

The following records the current changed interfaces; a final declaration-and-line inventory remains to be produced after the proofs compile.

- `CircuitFlags.ctorIdx_lt`: old bound 14; new bound 16, reflecting the two new flags.
- `JoltInstance.public_io`: old result `Option JoltDevice`; new result `Option JoltPublicIo`, retaining statement input/output bytes while removing advice buffers from that statement record.
- `JoltInstance.initial_state`: unchanged signature; its meaning now includes shared-memory initialization, code-span protection and cleared halt state.
- `initialRamWordFromState` and `finalRamWord`: unchanged signatures; old device overlays and synthetic flag words become direct shared-memory word reads.
- `Trace.matches_outputs`: unchanged signature; output bytes now come from final shared memory through `outputsOf`.
- `ConstraintContext.io` and `ConstraintEquations`'s `io` parameter: `JoltDevice` becomes `JoltPublicIo`.
- `nextUnexpandedPCEqLookupIfShouldJump`: renamed `nextUnexpandedPCEqLookupIfJump`; the old `ShouldJump` guard becomes `OpFlags.Jump`.
- `ConstraintEquations`: the old `shouldJumpEqJumpMulNotNextIsNoop` field is replaced by `haltEndRule io.panic`; adds the protected-increment and selector-sum fields; removes RAM Hamming booleanity and chunk Hamming fields.
- `ramPublicIoMask`: unchanged signature apart from `JoltPublicIo`; old upper bound `RAM_START_ADDRESS` becomes `output_end`.
- `ramPublicIoWord`: unchanged signature apart from `JoltPublicIo`; removes panic and termination overlays.
- `RepinInputs`: removes independent halt-column functions; retains only public C.
- `rv64Row14_holds_iff` and `rv64Rows_holds_iff`: row 14 compares the new Jump guard.
- `rv64Row21_holds_iff` and `rv64Rows_holds_iff`: row 21 compares the panic-dependent halt lane instead of `ShouldJump`.
- `ramReadWriteChecking_holds_iff`: old two-claim conjunction becomes all four pinned claims.
- `kindCoverage_matches`: old false total coverage expectation becomes coverage under `ModelledKind`, excluding exactly the two inline XOR rotations.
- `ConstraintEquations.generated`: C is now fixed from bytecode/layout rather than supplied arbitrarily, and the generated halt columns read the authenticated witness flags.

The new definitions `haltEndRule`, `ramAccessCount`, `ramCodeRegion`, `ramWriteProtectedMask`, `ramWriteProtected`, and `ModelledKind` support named consumers above.
No new theorem premise is intended as a workaround for a proof gap.

## Remaining work

The whole-run relation and its second I/O implementation have not yet been migrated.
The three flag-word restrictions and their old stopping proofs have not yet been removed.
The status of `tracerAddressChecks` is not yet established.
The two RAM completeness admissions have not yet been proved.
The three #1949 admissions remain untouched.
The methods pin and other Rust citations remain to be updated after the model is consistent.
The complete JoltConstraints build, required diff scans, axiom checks and final clean-tree check have not passed.
No final soundness or completeness claim is made by this working report.

## Validation in progress

The targeted build is `track-t-build.sh lake build JoltConstraints.ConstraintGen.Equiv`.
Its log and completion marker are `.constraints-repin-core.log` and `.constraints-repin-core.done`.
The source scan currently finds no `sorry` or `admit` in `JoltConstraints/ConstraintGen`.
There are no new decision-procedure uses, axioms or resource-limit increases.
Per-proof timings have not yet been measured.

## Continuation after the first core build

The first core build failed on eight missing halt-constructor cases in operand tables, lookup tables and bytecode read selectors.
Those cases now treat both halts as source-free, table-free rows with their destination captured as the link.
The next core build targets `ConstraintGen.Equiv` and `Soundness.Layer1.Addresses`.
Its log and marker are `.constraints-repin-core2.log` and `.constraints-repin-core2.done`.

The RAM selector uniqueness proof no longer uses retired chunk Hamming equations.
It obtains the zero-or-one global access count from the authenticated load/store flags and their instruction-level disjointness, then combines that count with Boolean full selectors.
`bytecode_read_of_selected` moved unchanged from `Layer1/Bytecode.lean` to `Layer1/Addresses.lean` because the latter now needs authenticated flag values.
The unused RAM Hamming lemmas in `Layer1/Chunks.lean` are deleted.

`theorems/DeviceFrame.lean` supplies shared-memory device-frame rules and a primitive initialization shape theorem.
The generic instruction device relation now requires compatibility with both halt updates; it no longer requires compatibility with device-byte stores.
These facts are candidates to move into JoltBytecode when that project can accept changes.
`Soundness/Layer5/TapeSemantics.lean` and `Completeness/Helpers/IOSetupFrame.lean` use these rules.
The old non-store-implies-device-equality lemma is deleted because halts can set the panic bit.
Two old consumers of that lemma remain to be migrated.

`theorems/layout_facts.lean` is being updated to the current constructor, checked RAM-domain admission and output-end geometry.
`new_io_geometry` formerly described panic and termination words; it now describes `output_end = output_start + max_output_size`, aligned output capacity, `io_end = output_end`, and the constructor's reserved eight-byte gap below RAM.
`new_io_ordered` formerly ordered the two flag words; it now orders input/output start and end addresses and bounds `io_end` by RAM start.
`new_io_word_geometry` drops the termination index and uses the output-end index in place of the panic index.
`JoltDevice.low_address_free` drops the two removed flag-region predicates and strengthens its final geometric bound to strict inequality.
`init_state_jolt_device` no longer resets an output array; it resets only `panic`.
`initial_state_device` drops the two advice-array equalities while retaining the checked layout and both tracer advice-size checks.
`initial_state_advice_below_input` states the same byte-range bounds using the instance's trusted advice and the supplied private advice directly.
`initial_state_inputs`, whose conclusion referred to a deleted device field, is deleted; its consumers still need direct shared-memory initialization facts.

`theorems/execution_facts.lean` carries register initialization through `JoltISA.initialState` and handles the halt primitive in register-presence preservation.
`Mmu.load_raw_low` formerly returned `some 0`; it now returns `none` because the pinned tracer rejects unmapped low addresses.
`Mmu.load_doubleword_zero` formerly returned a successful zero load; it now returns `Error.Assertion "Load Failed"`.
`execInstr_load_zero` retains its conditional statement, proved by eliminating an impossible retired zero-address load.
The corresponding floor-load completeness branch now eliminates that failure too.

`theorems/memory_presence.lean` removes the old byte-presence induction and flag-word ordering invariant.
The tracer now reads mapped shared memory with zero defaults, and stores do not delete bytes.
The retained store-word existence proof instead uses address admission, stable layout and an aligned padded RAM end.
`store_doubleword_old_present` and its private store-sequence helper replace the old populated-memory and flag-order hypotheses with lowest-address alignment, which `HonestTrace.preState_lowest_address_aligned` proves from initialization and row linkage.
`heap_end_le_ram_backing_end` now takes the successful layout-construction certificate; the assertion over an arbitrary layout record is false under the new padded-backing definition.
Its two image-proof callers in `WholeRun/Decoded.lean` and `CodeInv.lean` already have that certificate.
The RAM-array size identity remains available to those callers.

The new frame and foundation proofs await compilation.
The queued targeted build is `track-t-build.sh lake build JoltConstraints.theorems.DeviceFrame JoltConstraints.theorems.Soundness.Layer5.TapeSemantics JoltConstraints.theorems.execution_facts JoltConstraints.theorems.memory_presence`.
Its log and marker are `.constraints-repin-frames.log` and `.constraints-repin-frames.done`.
The new helper proofs have not established an overall build or soundness result.

## Checked core and next integration build

`ConstraintGen.Equiv` compiled after explicitly normalizing the generated protected claim's integer zero into the field zero.
All four original generator admissions are removed, and the two explicitly excluded inline-only kinds remain outside `ModelledKind`.
`Soundness.Layer1.Addresses` compiled with the new global access-count argument.
`theorems/DeviceFrame.lean`, `Soundness/Layer5/TapeSemantics.lean` and `theorems/layout_facts.lean` now compile.
The layout module uses one `initial_state_build` decomposition rather than duplicating the input-check argument in each register or device initialization proof.
The execution and memory-presence modules still await a captured integration result.

Local commit `877356e` is `Update halt and RAM constraints to the Jolt pin`.
It includes the translation changes, generator equivalences and Layer 1 selector proofs.
The whitespace and forbidden-addition scans passed before that commit.
No claim is made that the committed slice alone repairs the full library.

The full diagnostic build is running through the required wrapper as `.constraints-repin-integration1.log`, with marker `.constraints-repin-integration1.done`.
It is expected to expose old consumers beyond the checked foundation; the required final successful full build remains outstanding.

## Additional pinned-source checks

`crates/jolt-prover/src/config.rs`, `ProverConfig::padded_trace_length` (lines 44–63), rounds the executed row count itself up to a power of two, with the compiled floor.
It does not reserve an extra padding row.
`derive_from_dimensions` (lines 77–80) rejects zero rows and any trace not ending in a halt.
The current Lean padding definitions and their strict inequalities still follow the previous pin and must change.
The temporary `noMaxLengthTrace` restriction is therefore obsolete too; its removal is part of matching the actual pinned stopping/sizing rule.

A fresh independent reviewer performed the requested blind statement read-back over the changed constraint interface and essential definitions before seeing the brief or intended contract.
The read-back expands the field equations, finite domains, public-mask intervals and default branches, and records the exact uncommitted source hashes.
It confirms only the literal statements, not semantic fidelity or whole-library validity.
The reviewed interfaces permit arbitrary fields for algebraic equivalences; the later soundness argument still needs its characteristic bound to interpret the halt lane and selector sums.
The reviewer then inspected the intended pin and identified an admission check absent from the old context.
Jolt's `JoltProgramPreprocessing::code_region` and verifier input checks call `validate_code_region`, requiring checked code-region construction and `region.end ≤ compute_max_ram_k(layout)`.
This is an upper bound by the maximum domain, not by the proof's selected RAM domain or by `program_end`.
`ConstraintContext.validInputs` can carry this actual admission check once `JoltInstance.validate_inputs` models it; no new soundness premise is needed.
This migration remains outstanding.

## Harness scan conflict awaiting clarification

The obsolete imported `Soundness/Layer5/DeviceMemoryObstruction.lean` contains two baseline `decide +kernel` uses, in `layout_from_config` and `layout_ram_bound`.
Its definitions and conclusions refer to the removed termination and panic words, and cannot remain an executable obstruction for this pin.
The supplied diff scan anchors most alternatives to added lines, but its final `decide \+kernel` alternative matches removed lines and context lines too.
Consequently deleting or repairing this obsolete counterexample can fail that scan without introducing a forbidden proof.
I asked whether the harness can test that alternative on added lines, consistently with the stated “no new” rule.
No harness or test command has been edited, and this obsolete file remains untouched while that clarification is pending.

## Integration result and foundation repairs

The full `.constraints-repin-integration1.log` build failed.
Its failures include obsolete completeness imports, old device-array projections, the old whole-run I/O layer, and flag-word restriction proofs.
It also found initialization proofs that had not yet been carried through `JoltISA.initialState`.
This is diagnostic evidence only; the final full-library check has not passed.

I deleted the three completeness modules for the retired `RamHammingWeightBooleanity`, `RamRaChunkHammingWeight` and `ShouldJumpEqJumpMulNotNextIsNoop` constraints, their aggregate imports, and their record-field assignments.
The generated pin has removed those equations; the aggregate will instead need proofs of the three new halt/access/protection fields.
The earlier renamed jump completeness module remains under `NextUnexpandedPCEqLookupIfJump.lean`.

Targeted compilation passed `theorems/execution_facts.lean`, `expansion_temp_liveness.lean`, `Soundness/Layer1/Ram.lean` and `Soundness/Layer3/State.lean`.
The layout projections in the latter two now use `JoltPublicIo.memory_layout`.
The temporary-register source classifier treats both halt instructions as having no source operands.
The initialization register proofs explicitly instantiate the bootstrap device, tape and host configuration after using `initialState_shape`.
The targeted modules took approximately 56–59 seconds each while compiled together; individual proof timings have not been measured.

`theorems/advice_inputs.lean` deletes the unused `JoltInstance.initial_states_agree_on_trusted_advice`, whose conclusion compared the two removed device advice arrays.
The intended shared-memory invariance is already a consequence of the fixed initialization inputs; no compatibility device field is introduced.
`JoltInstance.initial_state_with_advice_tape` and `initial_state_adviceTape_readPosition_zero` retain their statements.
A new primitive `JoltConstraints.initialState_with_adviceTape` under `theorems/DeviceFrame.lean` states that replacing a tape commutes with shared-memory initialization; it is another candidate to move to JoltBytecode.
This tape proof and the updated memory geometry still await the next targeted build.

In `Completeness/Helpers/RamReadSelection.lean`, the old `Mmu.load_doubleword_below_heap_end`, `Mmu.store_doubleword_below_heap_end` and `HonestTrace.ram_address_below_heap_end` become the correspondingly named `*_below_ram_backing_end` declarations.
Their old conclusions bounded an accepted RAM start address by `layout.heap_end.toNat`.
Their new conclusions bound it by `Mmu.ram_backing_end device`, with all execution hypotheses retained.
The RAM-bound conjuncts of `HonestTrace.floor_load_properties` and `floor_store_properties` change in the same way.
This is the pinned MMU rule: padding after the configured heap can be read and written, subject to protection checks.
The caller `HonestTrace.highest_ram_slot_lt_heap_end` in `Completeness/Helpers/VerifierSizes.lean` still needs migration to the maximum padded domain.
No RAM-domain completeness result is claimed yet.

A separate whole-run invariant is false after this model change: `WholeRun.MemoryFrame.below` claims all memory below RAM is unchanged by execution.
An output store now changes a byte in that interval.
`WholeRun.Shadow` also compares memory only above RAM, which cannot justify a shared-memory I/O load.
The required repair is to compare zero-default shared bytes across the mapped range, preserve code/halt state where the execution uses it, and replace the old below-RAM frame consumers together with the deleted duplicate I/O relation.
These statements and `Ghost.lean` remain unchanged pending that coordinated migration.

The next targeted build checks the new primitive tape frame, memory-presence geometry, RAM read selection and the existing register replacement commutation proof.
Its log is `.constraints-repin-foundation2.log`, with completion marker `.constraints-repin-foundation2.done`.

## Checked initialization and frame slice

After reading `.constraints-repin-foundation2.log`, I repaired the primitive tape frame's Option case reduction and carried tape initialization through that shared lemma.
`DeviceFrame`, `layout_facts`, `Soundness/Layer5/TapeSemantics`, `advice_inputs`, `execution_facts`, `memory_presence` and `Completeness/Helpers/IOSetupFrame` now pass targeted builds through the required wrapper.
`memory_presence` takes about 21 seconds as a module; individual declaration times remain unmeasured.
Its initial kernel recursion failure was resolved by stating the domain arithmetic over only natural-number bounds and an abstract Option domain, then instantiating those facts with the layout.
No elaborator or kernel limit was raised.
The shared-memory old-word capture theorem now compiles, including stores in the I/O gap and padded RAM.
This establishes the capture prerequisite, not either RAM history completeness theorem.

The foundation build also exposed the new source instruction case in `ExpansionChecks.expand_ok`; it now applies the existing `native_ok` framework to `jolt.success`.
This classifier repair and the register replacement protection-check proof await their next checks.
