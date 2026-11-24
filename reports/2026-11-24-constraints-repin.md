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

## Halt admission and exact-domain padding migration

Local commit `0d9ed87` records the checked initialization/shared-memory frame slice.
Local commit `66f2e4c` records the checked source-expansion and initial-PC repairs, plus corrected generator coverage documentation.
`ExpansionChecks.expand_ok` now handles `jolt.success` through the existing native-row framework.
`initial_state_pc` retains its statement and uses `initial_state_build` and `initialState_shape` before applying the bootstrap register fact.
The expansion module took about 43 seconds, and the initial-PC interface module took about 21 seconds, in isolated targeted builds.
Individual proof timings have not been measured.

The following model changes are now implemented and await the next targeted build.
They follow the pinned halt and code-admission specification; their consumers are still being migrated.

- `translation/program.lean`, new `JoltISA.Instr.haltKind?`, classifies exactly `JoltSuccess` and `Panic` as success/panic halts.
- `translation/honest_trace.lean`, new `TraceRow.Halts`, states that the row's instruction has a halt kind.
- `HonestTrace.stops` changes from `∀ last ∈ rows.back?, last.StableStall` to `∀ last ∈ rows.back?, last.Halts`.
- `HonestTrace.runs_until_stop` changes the earlier-row exclusion from `¬ current.StableStall` to `¬ current.Halts`.
- `Soundness/Layer5/TapeTrace.lean`, `UntrustedAnswerTrace.stops` and `runs_until_stop`, make exactly the same changes for relaxed tape-answer executions.
- `padded_trace_length rows` changes from the previous floor/round-up formula with `rows + 1` to `max 256 (2 ^ Nat.clog 2 rows)`.
- `WitnessParams.proverTraceLength minimumLogT physicalRows` changes from `max (2 ^ minimumLogT) (2 ^ (Nat.log2 physicalRows + 1))` to `max (2 ^ minimumLogT) (2 ^ Nat.clog 2 physicalRows)`.
- `WitnessParams.ProverPaddedFor` retains its two supported floor formulas but changes the final bound from `physicalRows < p.traceLength` to `physicalRows ≤ p.traceLength`.
- `padded_trace_length_spec` changes its first conjunct from strict containment to `rows ≤ padded_trace_length rows`; its floor and power-of-two conjuncts remain.
- `ExecutionDimensions.ends_in_jump` becomes `ends_in_halt`, and `Trace.execution_dimensions` computes it from the final instruction's halt kind.
- `ProverConfig.checkedTraceLength` removes checked addition of the extra row and rounds the executed row count directly.
- `ProverConfig.deriveFromDimensions` changes its admission from `trace_length = 0 ∨ ends_in_jump` to `trace_length ≠ 0 ∧ ends_in_halt`.
- `ProverConfig.checkedTraceLength_rounding` and `checkedTraceLength_eq` replace every `Nat.clog 2 (rows + 1)` by `Nat.clog 2 rows`.
- `ProverConfig.deriveFromDimensions_sizes` changes its first conclusion to the new nonempty/halt admission condition and retains its size and maximum conclusions.
- The new `HonestTrace.prover_config_last_halt` extracts the actual accepted final-halt condition.
- `HonestTrace.prover_config_last_jump` retains its signature and derives the Jump property from that halt condition.
- `JoltISA.Instr.is_jump` now includes the two halt constructors along with JAL/JALR, matching their circuit flags.
- The unused `clog_succ_eq_log2_succ` lemma is deleted after removing the old extra-row arithmetic.

`valid_run` retains the descending sequence-count and size checks and adds `run.length ≤ 1 ∨ every row has no halt kind`.
This models `BytecodePCMapper::try_new` rejecting `HaltInSequence` at `preprocess/bytecode.rs:163–174`.
`valid_run_countdown` retains its statement and extracts the countdown equality from the enlarged acceptance check.
The new `bytecode_source_extents` factors the source-anchor calculation used by the public code mask and checked preprocessing.

The new `JoltISA.checkedCodeRegion` requires successful `codeRegionOf`, successful `layout.max_ram_k?`, an ordered interval ending within that maximum, and the unique empty encoding `(0, 0)`.
It is a candidate to move into JoltBytecode.
`JoltInstance.bytecode` retains its expansion, PC-map and entry lookup checks and additionally rejects a zero entry and validates the expanded source-anchor code region against the layout.
`JoltInstance.validate_inputs` retains its public layout and input/output size checks and additionally checks a nonzero entry and the source image's checked code region.
The context's existing `validInputs` certificate carries these actual verifier checks, without adding a new context assumption.
The equivalence of the original source extents and expanded terminal-anchor extents still needs an explicit proof.
The old-bound consumers currently extract the retained bounds conjunct while the new code-admission facts remain available for the upcoming soundness argument.

`methods/soundness.md` now records the requested `ff6fc6568` pin and the current date.
The three flag-word restrictions, `noMaxLengthTrace`, whole-run duplicate I/O layer and both RAM completeness admissions remain to be removed or proved.
The old stable-stall support declarations remain until their callers have been replaced by the halt proof.
No result is claimed for the changed main model until its callers compile.

The next detached targeted build is `.constraints-repin-halt-model1.log`, with marker `.constraints-repin-halt-model1.done`.
It checks generator equivalences, padding/sizing facts, relaxed trace construction, RAM read selection and register replacement.
Before starting it, the whitespace check, forbidden-addition scan, generator-admission scan and frozen-directory diff check passed.
The obsolete baseline `decide +kernel` counterexample has still not been edited; the earlier harness-scan clarification remains pending.

## Halt model checks and padded RAM sizing

The detached halt-model check passed the generator equivalences, trace/configuration padding facts, witness-domain facts, relaxed tape trace and RAM read-selection modules.
Its sole failure was the register-replacement store commutation proof in `WholeRun/NonInterference.lean`.
That proof now normalizes the updated protection and shared-memory store branches explicitly, retaining its statement; the isolated module build passed in approximately 22 seconds.

The RAM sizing migration now delegates `VerifierSizes.maxRamSize layout` to `layout.max_ram_k?`.
The old definition checked subtraction, rounded a ceiling word count and checked only the rounded host integer.
The new definition additionally checks heap headroom/alignment, contiguous aligned I/O segments and the maximum padded address extent, exactly as `common/src/jolt_device.rs` (`MemoryLayout::max_ram_k`) at `ff6fc6568`.
The new `max_ram_k_spec` in `theorems/layout_facts.lean` exposes these checked domain facts to the existing geometry callers; it is a candidate to move into JoltBytecode.
`memory_presence.lean` now derives its heap/backing geometry from that shared specification instead of a second private unfolding proof.

In `Completeness/Helpers/VerifierSizes.lean`, `HonestTrace.highest_ram_slot_lt_heap_end` is replaced by `HonestTrace.highest_ram_slot_lt_maximum`.
The old conclusion bounded the highest slot by the ceiling word count through `heap_end`.
The new conclusion bounds it by `layout.max_ram_k?.getD 0`, retaining the honest trace as its only argument.
This admits actual accesses in heap padding rather than excluding them through a false heap-only bound.
`HonestTrace.witness_params_ram_maximum` retains its full statement and derives its touched-word bound from this maximum-domain theorem.
`new_heap_end_ge` retains its statement and follows the pinned aligned heap-end construction.
These sizing proofs are undergoing their targeted compilation check; no completeness result is claimed for them yet.
`Soundness/Layer7/ProverAccepts.verifier_ram_image_end_bounded` retains its statement and obtains the maximum from the new checked-domain specification.

Local commit `bdc29d7` records the checked explicit-halt, exact-domain padding and code-admission slice.
The targeted RAM sizing build now passes `Completeness/Helpers/VerifierSizes`, `Soundness/Layer3/Layout` and their changed initialization/geometry dependencies.
The verifier-sizes helper module took approximately 16 seconds; individual declaration times remain unmeasured.
The first proof encountered a kernel recursion limit while transporting an equality through the full checked layout expression.
Factoring the backing-end arithmetic over a natural-number base, an abstract `Option Nat` domain and a successful-domain certificate resolved that failure without raising a limit.
The resulting `highest_ram_slot_lt_maximum` uses actual traced RAM bounds and includes padded RAM accesses.
`witness_params_ram_maximum` retains its prior existential maximum and prover-size inequality with no new hypothesis.
The independent reviewer is checking this sizing slice against the pinned Jolt implementation.

The next detached integration check builds `JoltConstraints` through the required wrapper, with log `.constraints-repin-integration2.log` and marker `.constraints-repin-integration2.done`.
This is an integration diagnostic; the obsolete flag-word soundness and whole-run I/O consumers have not yet been migrated, so a passing full build is not claimed.

## Independent sizing review and halt replay work

The fresh `ram_sizing_readback` reviewer completed a code-only read-back before receiving the intended Jolt contract.
It checked `maxRamSize`, `max_ram_k_spec`, `highest_ram_slot_lt_maximum` and `witness_params_ram_maximum`, including their initialization, execution and prover-size dependencies.
The reviewed SHA256s were `5a29eebc7a98dfc30c71b545bf7e789f21c23e61537344e810f96e9b8deb3106` for `translation/verifier_sizes.lean`, `b9ed9111e6632c0d33dfc7ce18c892eb74c8db0ca587811e122fa4c04859e5c7` for `theorems/layout_facts.lean`, and `e8f7b3037eee320b234d5000f44a48af07935f06079f633d8165d2b420327386` for `Completeness/Helpers/VerifierSizes.lean`.
The subsequent comparison against `ff6fc656813d950565c9f6e1258b78bdaf0e60e8` found no sizing discrepancy or added heap-only-access premise.
The reviewer noted that riscv-tests/tohost mode can allocate less backing than the normal modeled guest; this does not invalidate the maximum-domain upper bound.
This was a read-only source review, not a separate build or axiom check.

The full `.constraints-repin-integration2.log` still fails, primarily on old device arrays, stable-stall conclusions and primitive frame interfaces.
The next slice repairs the shared interfaces before updating their remaining callers.

- `Soundness/Layer5/TapeDeviceFrame.lean`: the run/trace `device_relation` hypotheses change from preservation by device-byte stores to compatibility with `recordHalt`'s two panic updates.
- Their `final_device_same` conclusions retain the existing layout-only `JoltIOSetupFrame.Same` relation.
- Their `final_outputs_fit_layout` conclusions replace the deleted final device output-array size by the size of `finalDevice.outputsOf finalState.sail.mem`, retaining the initial-layout capacity bound.
- `Soundness/Layer5/MisaFrame.lean`: public statements are unchanged; the proof now covers `execHalt` and shared-memory initialization.
- `Completeness/Helpers/TracePCProofHelpers.lean`: public statements are unchanged; the PC frame now covers the shared halt body and `recordHalt`.
- `Soundness/Layer5/RamInitialization.lean`: `initialRamWord_eq_ram_doubleword` retains its statement and reads the shared initial byte map directly; two unused private overlay-construction proofs are deleted.
- `theorems/DeviceFrame.lean`: new `store_doubleword_relation` factors the existing device frame over any reflexive/transitive relation that permits Sail-state updates.
  `store_doubleword_keeps_device` retains its statement and becomes an instance of this shared proof.
- `theorems/program_facts.lean`: new `pc_map_ok_halt_terminal` derives a zero remaining-row count from PC-map admission, row membership and an explicit halt classifier; its targeted module build passed in approximately 19 seconds.
- `theorems/execution_conditions.lean`: `HonestTrace.Terminated` retains nonemptiness, the source boundary and repeated PC, replacing `selfJumpRepeats = true` by an existential halt kind, the post-state's recorded kind and its corresponding panic Boolean.
  `HonestTrace.terminated` retains its theorem signature and is being reproved from this certificate.
  The new `execHalt_end` and `HonestTrace.halt_row` supply the local execution and accepted-source-boundary facts; the primitive halt fact is a candidate to move into JoltBytecode.
- `Soundness/Layer7/TapeRebuild.lean`: `rebuild_stops` and `rebuild_runs_until_stop` replace `StableStall` by `Halts`, exactly as their original/replayed trace certificates now require.
  `rebuild_matches_outputs` retains its signature and uses agreement on shared memory as well as the final device.
  A shared observation lemma factors the device/memory agreement proofs through the same tape/destination replacement relation.

The first targeted frame check passed `TapeDeviceFrame`, `MisaFrame` and `TracePCProofHelpers` (approximately 29, 28 and 34 seconds as parallel modules).
The initial RAM-word proof then needed the existing `witness_domain` import for the lowest-address identity; that repair is in the next check.
`store_doubleword_relation` and its unchanged device corollary pass their isolated module build.
The halt certificates and tape-replay migration are still awaiting compilation, so their proofs are not reported complete.
The next detached check is `.constraints-repin-halt-replay2.log`, with marker `.constraints-repin-halt-replay2.done`.
The three flag-word restrictions, whole-run I/O deletion and two RAM-history completeness proofs remain open.

## Halt replay continuation

The `.constraints-repin-halt-replay2.log` failures in `execution_conditions`, `RamInitialization` and the tape replay primitives were inspected and repaired.
The isolated builds of `execution_conditions` and `RamInitialization` now pass (approximately 9 and 20 seconds).
`HonestTrace.terminated` now derives its retained source-boundary and repeated-PC facts and its new halt-kind certificate from the actual final halt execution.
The implementation packages the dependent runtime-advice execution existential before selecting the halt constructor, avoiding an invalid dependent rewrite.
The initial RAM-word proof uses the shared byte map and the existing lowest-address identity directly, without device-overlay reconstruction.

`DeviceFrame.store_raw_map` is a new shared commutation lemma parameterized by the state transformation, preservation of the device, memory and protection checks, and commutation with memory replacement.
`DeviceFrame.store_bytes_map` derives commutation for a list of byte stores from single-store commutation.
Both are candidates to move into JoltBytecode.
The isolated `DeviceFrame` build passes (approximately 2 seconds).
`WholeRun/NonInterference.store_raw_withReg` and `TapeRebuild.swap_store_raw` now instantiate this common argument, and their byte-fold lemmas instantiate the same fold proof.
Their existing statements are unchanged.
This removes the duplicated raw-store branch proof and avoids reducing a guard while retaining an incompatible Boolean decidability instance.

`WholeRun/Blocks.lean` retains all its statements and derives the final source boundary and repeated PC from `HonestTrace.halt_row` rather than projecting the former stable-stall certificate.
The renamed `Completeness/NextUnexpandedPCEqLookupIfJump.lean` now proves the new row-14 polynomial, replacing the old ShouldJump guard by the actual Jump flag.
Its public theorem retains the honest-trace, RAM-fit, prover-padding and bytecode-domain hypotheses.
The old conclusion is `nextUnexpandedPCEqLookupIfShouldJump (honestWitness params trace)`; the new conclusion is `nextUnexpandedPCEqLookupIfJump (honestWitness params trace)`.
For a nonfinal real row, the no-earlier-halt execution certificate reduces a Jump row to JAL/JALR.
For the final real row, either halt kind has lookup result zero and the successor column is zero, including when the real trace exactly fills the witness domain.
The old proof incorrectly relied on a strict padding inequality; that reliance is removed.
These consumer changes await their compilation check.

A fresh read-only reviewer, `halt_certificate_readback`, is independently reading the changed terminal certificate and its dependencies before receiving the intended contract.
Its result remains pending.
The next detached check is `.constraints-repin-halt-replay3.log`, with marker `.constraints-repin-halt-replay3.done`.
It builds tape replay, register replacement, whole-run block construction, row-14 completeness, the initialization/frame modules, the halt certificates and generator equivalences through the required locked wrapper.
This is a targeted integration check, not the final `JoltConstraints` acceptance check.
The whitespace and forbidden-diff scans passed before starting it.
No new admission, forbidden decision procedure, axiom or resource-limit increase was added.
The three obsolete flag-word restrictions, whole-run duplicate I/O deletion and both RAM-history completeness proofs remain unfinished.
The earlier harness-scanner question remains unanswered; its unanchored `decide +kernel` alternative would reject removal of the two baseline occurrences in the obsolete device-memory obstruction file.

## Checked halt replay slice and terminal sizing migration

The `.constraints-repin-halt-replay3.log` check passes `TapeRebuild`, `WholeRun/NonInterference`, `RamInitialization`, `TapeDeviceFrame`, `MisaFrame`, `TracePCProofHelpers`, `execution_conditions` and generator equivalences.
The replay and noninterference modules took approximately 20 and 69 seconds under the parallel build; the latter recompiled multiple dependencies.
Declaration timings are not separately measured.
The only failures were the block initializer's obsolete Option unfolding and an explicit Fin-to-Nat projection needed by row 14's nonjump flag proof.
Both are repaired for the next targeted check.

The fresh `halt_certificate_audit` reviewer recorded a blind read-back of `execHalt_end`, `HonestTrace.halt_row`, `HonestTrace.Terminated`, `HonestTrace.terminated` and `pc_map_ok_halt_terminal` before receiving their intended contract.
The reviewed working-file SHA256s were `b61e35e997cd1ecfb904a719fa6bfafbf64b648711f7eeb943fb11a00efbbafe` for `execution_conditions.lean`, `b598940d5861b340007d22fe6d8dcd8d5125aa878608511133b6e38c1bd745d5` for `program_facts.lean`, and `faf62fe85ec78866e04209226c06c806aaed4227c496ba6305000edcc44dd2cc` for `translation/honest_trace.lean`.
After comparison against `Cpu::halt`, `Cpu::tick` and `BytecodePCMapper::try_new` at `ff6fc6568`, the reviewer found no blocking mismatch in this honest-trace certificate slice.
It explicitly did not review a proof of public-claim binding or constraint soundness.
The frozen JoltBytecode model sets the panic bit eagerly in `recordHalt`; Jolt's tracer instead sets the extracted device bit from `cpu.halted` in `Emulator::take_jolt_device` (`tracer/src/emulator/mod.rs:137–146`).
The final extracted observations agree, but intermediate device-bit timing is an abstraction and is not represented literally.
The certificate conclusions do not expose the link write, although the primitive executes it, and completion/nonemptiness remain fields of `HonestTrace` rather than a universal termination claim.

`Soundness/Assumptions.lean` now removes `terminationThenStall`, `panicStoresOne`, `claimsNoPanic` and `noMaxLengthTrace` from `JoltInstance.TemporaryRestrictions` and removes the unused `NoMaxLengthTrace` definition.
The remaining fields are `tracerAddressChecks` and `hostCallsSucceed`.
The old flag-word restriction definitions and callers still exist in their obsolete modules; their replacement is unfinished and the full library still fails.
No claim of unrestricted soundness is made yet.

In `Soundness/Layer7/ProverAccepts.lean`, the old `represented_trace_ends_in_jump` conclusion (`trace.rows.size = 0 ∨ dimensions.ends_in_jump = true`) is replaced by `relaxed_trace_ends_in_halt` (`trace.rows.size ≠ 0 ∧ dimensions.ends_in_halt = true`).
The new theorem needs only the completed relaxed trace, whose existing certificate supplies these facts; the old represented-branch replay helper becomes unused and is deleted.
`checked_trace_length_fits` retains its rows/domain/public-maximum/floor arguments and conclusion but drops `rows ≠ 2 ^ Nat.log2 maximum.toNat`.
It now rounds `rows` instead of `rows + 1`, exactly as the pinned prover does.
`Soundness/TopLevel.soundness_prover_accepts` drops its `NoMaxLengthTrace` argument, checks a nonempty explicit halt and uses this exact sizing result.
Its caller in `Soundness/soundness.lean` is updated.
These sizing and acceptance caller changes await compilation, and their top-level dependencies remain under migration.
