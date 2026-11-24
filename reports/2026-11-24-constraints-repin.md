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

Local commit `5b712bd` records the checked halt certificates, generic memory frames, shared-memory initialization, register replacement and tape replay slice.
The next detached integration check builds `JoltConstraints` through the required wrapper, with log `.constraints-repin-integration3.log` and marker `.constraints-repin-integration3.done`.
It will also check the repaired block initialization, row-14 coercion and exact-padding acceptance helpers through their imports.
The full library is still expected to expose old flag-word and duplicate-device-I/O callers; this is diagnostic integration work, not a passing final check.

The remaining memory migration has a concrete consolidation point.
`Layer5/DeviceMemory.lean` still separately tracks device words and excludes a synthetic termination index, while `Layer5/RamAgreement.lean` compares byte-map words only at or above `RAM_START_ADDRESS`.
The pinned model instead needs one agreement over all shared words, with checked below-RAM MMU reads/stores reduced to that same map.
`MemoryRowExecution`, `MemoryRowAppend`, `RamCutAgreement` and `ExecutionPrefix` must then consume that agreement without termination events or a word exception.
Similarly, `WholeRun/Ghost.Shadow` must compare every zero-default shared byte and retain the new code-region/halted fields; its old frame asserting that every below-RAM byte is fixed is false for output and I/O-gap stores and must be replaced as part of the model change.
The old `WholeRun/Halt.Block.ebreak_post` device-unchanged claim also belongs to the previous self-jump model: the new panic halt updates final panic metadata.
These old claims have not been hidden behind compatibility wrappers or new assumptions.

## Shared-memory foundation and halt-link continuation

The `.constraints-repin-integration3.log` failure list was inspected on 2026-11-24 at Lean HEAD `5b712bd`, against Jolt `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
That check passes `WholeRun.Blocks`, the renamed row-14 completeness module, `Soundness.Assumptions` and the verifier-sizing helpers.
The full build still fails in the old flag-word restrictions, execution-prefix memory exceptions, duplicate whole-run I/O layer, obsolete EBREAK treatment and remaining completeness consumers.
This continuation does not claim those obligations are discharged.

`DeviceFrame.execHalt_shape` is new and proves the successful halt's two reads, destination write and exact final state for either halt kind.
Its conclusion is an existential link/address/intermediate state with the original nextPC/PC reads, `writeDst` execution and `post = recordHalt kind` after the nextPC update.
`execution_conditions.execHalt_end` retains its statement and now derives the existing terminal observations from this shared execution shape.
`JumpReturnProofHelpers.jump_halt_link` is new: under its existing writable-destination, nextPC-read and successful-halt facts, the captured destination equals the link.
`RegistersValProofHelpers.register42_halt_preserves_other` is new: a successful halt preserves any distinct source register's value, with the same readability premise used by the enclosing instruction-frame proof.
Both constructor cases use this common halt fact.
`honestWitness_rdWriteEqPCPlusConstIfJump` retains its public statement; its proof now handles JAL, JALR and both halt kinds before performing one common field calculation.
The two next-PC completeness files replace uses of strict trace padding by the new nonstrict padding bound without changing their theorem signatures.
The relaxed-trace terminal-halt helper fixes a definitional coercion by explicitly unfolding `TraceRow.Halts`.

The isolated `DeviceFrame` build passed after repairing two equality witnesses already rewritten by case analysis (approximately 4 seconds for the successful module build).
The isolated `WholeRun.Ghost` build also passed (approximately 7 seconds).
After those checks, its byte-insertion presence proof was factored through the new `DeviceFrame.insert_preserves_present`, so that final factoring awaits the next check.
`insert_preserves_present`, `execHalt_shape` and the existing primitive initialization/commutation facts are candidates to move into JoltBytecode.
A foreground helper build was started but its final result was not collected by polling; the next detached batch includes those helpers and their callers.

The changed whole-run declarations are:

- `WholeRun.Ghost.Shadow`: formerly equal registers/vregs/device/tape/host plus zero-default bytes only above RAM; now also equal code regions and halt markers, and equal zero-default bytes at every natural-number address.
- `WholeRun.Ghost.MemoryFrame`: formerly byte presence plus unchanged values at every below-RAM address; now byte presence.
  The removed below-RAM assertion is false for shared output/I/O-gap writes at this pin.
  `execInstr_shadow` and `execProgram_shadow` retain their result structure with these updated predicates, including exact successful values/errors and presence on both execution paths.
- `WholeRun.Related.ram`: formerly byte agreement only at/above RAM; now byte agreement everywhere.
  The obsolete `io`, panic-word correspondence and device-output-array-size fields are removed.
  Registers, Sail's step invariant, HTIF setting, checked layout and memory presence remain.
- `WholeRun.memHigh`: formerly `heap_end + 8`; now `Mmu.ram_backing_end`, the tracer's padded backing endpoint.
- `WholeRun.sailInit`: formerly a register overlay plus a reconstructed I/O/zero-fill memory; now only that register overlay, retaining exactly Jolt's initialized shared byte map.
  `IsFlagWord`, `sailByte`, `sailPanicWord`, `sailInitMem` and `sailOutputs` are deleted.
- `WholeRun.Init.related_sailInit`: the public signature is unchanged, with the new relation and initial state above.
  It uses the actual successful `JoltISA.initialState` shape and `JoltDevice.initialMem` rather than asserting that initialization is the old RAM-only `init_state`.
  The now-false `initial_state_spec` statement is removed; its system-invariant caller also uses the successful initialization shape.
- `WholeRun.Related.outputs`: formerly equality of trimmed reconstructed Sail outputs and the device output array; now equality of the full `outputsOf` arrays from the two shared memories.
  This directly supplies equality before any trailing-zero normalization.
- `WholeRun.Init.sailInitMem_get?` and `load?_output` are removed with their deleted reconstruction/device-array definitions.
  The unused input/output-boundary wrapper is also removed.
- `foldl_insert_range_get?`, `zipIdx_fold_get?` and `init_state_mem_get?` move from WholeRun initialization/decoding into `SharedMemoryInitialization.lean`, under `JoltConstraints`, without changing their mathematical signatures.
  The new `initialMem_present` proves that initialization retains base-byte presence and fills every I/O-window address; it is parameterized by the device, base/result maps and buffers, rather than a witness context.
- `memory_presence.initialRam_size_eq_ram_size` is new: a checked layout's initial RAM array has exactly `layout.ram_size` bytes.
  It uses the checked padded-domain bound to rule out u64 size wrap and its alignment to remove allocation rounding.
- `BlockStep` and `SystemBlocks` retain their public simulation statements with the new `Related` predicate and no separate I/O/panic-word preservation branches.
  The obsolete private `panicWord_eq` is deleted.

A fresh `shared_memory_readback` reviewer recorded a blind reading of the semantic interfaces before receiving the intended contract.
The initial reviewed hashes were `fe20600f43f4ecc90cd42f80518edda7d5ae421f006888f93769b0e8c05897b5` for `Ghost.lean` and `817a16ffdba56a17ebf08cf8ec26cc7cd8d4c494fc32f6fe40554dd8eda7ccf9` for `Relation.lean`.
It explicitly distinguishes zero-default value equality from hash-map domain equality and notes that these shadow theorems concern direct finite instruction/program execution, not CPU fetching or a global termination certificate.
Its subsequent fidelity/proof comparison against the pinned tracer is pending.

The next detached check is `.constraints-repin-shared-foundation1.log`, with marker `.constraints-repin-shared-foundation1.done`.
It checks the shared initializer, relation, ghost, block-step/system invariant foundations, halt-link/register completeness consumers, corrected next-PC padding proofs and the terminal-halt acceptance helper through the required build wrapper.
The forbidden-diff scan and whitespace check pass before launch.
The duplicate `Io.lean`/`IoAmo.lean` files and their remaining consumers are still pending replacement and deletion, as are the old soundness flag-word definitions/callers and both RAM-history admissions.
No new admission, forbidden decision procedure, axiom or resource-limit increase was added.

## Shared foundation check and row-21 completeness

The detached `.constraints-repin-shared-foundation1.log` check ended with exit 1 at 04:55:45 on 2026-11-24, at Lean HEAD `5b712bd`, against Jolt `ff6fc6568`.
It passed `DeviceFrame`, `WholeRun.Ghost`, `WholeRun.NonInterference`, `execution_facts`, `trace_interface`, `witness_domain`, `Soundness.Assumptions` and `Soundness.Layer7.ProverAccepts`.
The last module confirms the relaxed-trace halt acceptance and exact padded-length helper in this targeted slice, without validating the unfinished top-level theorem.
The sole failed prerequisite was `memory_presence.initialRam_size_eq_ram_size`, where the kernel reported deep recursion.
Its statement is unchanged.
The proof now delegates subtraction bounds, optional-domain arithmetic and allocation rounding to three small private natural-number lemmas, without changing any limit.
That repair awaits the next check.

`theorems/HaltFlags.lean` adds `JoltMetadata.haltFlags`, identifying the two opcode columns with `Instr.haltKind?`: `Halt` is true exactly when a halt kind exists, and `HaltPanic` exactly for panic.
The pinned tracer's instruction declarations are `crates/jolt-riscv/src/instructions/virt/halt.rs` (`jolt_instruction!` for `Success` and `Panic`).
`theorems/Completeness/HaltEndRule.lean` adds `honestWitness_haltEndRule`: the honest witness satisfies row 21 under the actual final state's panic claim, for either halt kind and for an exactly full or padded trace domain.
Its premises are the honest trace and its existing `ProverPaddedFor` bound; it adds no restriction on the panic claim.
The proof uses the trace's no-earlier-halt and final-halt execution certificates, and treats padding separately.
`Completeness.lean` imports this result, and the unfinished `Completeness/All.lean` assembly now supplies the corresponding field.
These two new lemmas are not yet checked.
The assembly still needs the public-I/O migration and both new RAM claims; its current status is not completeness of the full bundle.

The next targeted check is `.constraints-repin-shared-foundation2.log`, with marker `.constraints-repin-shared-foundation2.done`.
It includes the repaired RAM-size lemma, initialization and shared-memory relation consumers, the halt-link/register helpers, row-21 completeness and the next-PC completeness consumers.
The full `JoltConstraints` acceptance check, removal of the duplicate whole-run I/O modules and old flag-word callers, both RAM-history proofs, and the final soundness proof remain open.

## Checked allocation and shared-foundation repairs

The `.constraints-repin-shared-foundation2.log` batch ended with exit 1 at 05:08:37 on 2026-11-24.
It replayed the repaired `memory_presence` module successfully, including `initialRam_size_eq_ram_size`.
It also checked `HaltFlags.haltFlags`, `JumpReturnProofHelpers.jump_halt_link`, the updated `RegistersValProofHelpers`, both next-PC completeness consumers, `WholeRun.Relation` and `WholeRun.BlockStep`.
`execution_conditions.execHalt_end` passed with its factored proof.
Local commit `44c094f` records the checked changes to `DeviceFrame.lean`, `WholeRun/Ghost.lean`, `execution_conditions.lean` and `memory_presence.lean`.

The initializer's failure was inference of a Boolean accumulator for `List.foldlRecOn`; each call now supplies the memory-map presence motive explicitly.
The row-21 completeness failure was simplifier matching across the two bytecode index forms (`Fin` versus its natural-number value); the halt metadata facts now use the same natural-number indexing as the witness columns.
The link-value proof similarly names its execution and source-end facts in terms of the local bytecode row before rewriting its instruction.
These are proof-body repairs, not statement changes.
The existing `rs1Operand?` and `rs2Operand?` classifications now include `JoltSuccess` and `Panic` in their no-source alternatives.
Their existing source-selector/value/canonicality theorems retain their statements.
`HaltFlags.jumpCases` is new and classifies a true Jump flag as JAL, JALR, success halt or panic halt; the return-value proof uses this one metadata classification rather than enumerating the ISA.
`WholeRun.Init` drops an unused verifier-sizing import.
These repairs await the next targeted check.

Several previously unchanged transitive modules still fail because they use removed advice arrays or flag-word predicates: `advice_below_input`, `PanicRestriction` and `TerminationRestriction`.
Their old interfaces have not been preserved through compatibility fields.
The remaining `WholeRun.CodeInv` and `Decoded` paths still reach those obsolete layers, so they are not evidence of a checked whole-run migration.
The next batch focuses on the repaired initializer, `Init`, `SystemInv`, `Bundles`, `SystemBlocks`, row-21 completeness and register/link consumers.
Its log is `.constraints-repin-shared-foundation3.log` and marker `.constraints-repin-shared-foundation3.done`.
The task's final full-library and soundness-closure checks have not passed.

## Loader preservation and image facts

The `.constraints-repin-shared-foundation3.log` check ended with exit 1 at 05:14:23 on 2026-11-24.
It checked `SharedMemoryInitialization` and `Completeness/Helpers/RegistersReadProofHelpers` successfully.
Local commit `152cf8c` records the checked halt-link, register-value and register-read helper changes.
The classification helper `HaltFlags.jumpCases` failed because its first split selected the outer flag match instead of the instruction match.
Its proof now explicitly exposes the four relevant instruction patterns before splitting; its statement is unchanged.
`WholeRun.Init` still contained the old `layout_facts` theorem over removed panic-word layout fields and one register theorem application with unconstrained device/tape/host arguments.
The dead geometry theorem is removed, its sole old use is removed by the image-proof migration, and the register application now gives those arguments explicitly.

The additional changed statements and moves are:

- Delete `WholeRun.Decoded.initial_state_ram`, which asserted successful initialization equals a RAM-only `init_state` with existential device and tape.
  That equality is false for the new model because initialization installs shared I/O bytes, code-region metadata and the halt marker.
  Its consumers now use the actual successful initializer shape and pointwise RAM-byte preservation.
- Delete `WholeRun.Init.layout_facts`, whose old conclusion was lowest address below output start, panic address equal to output start plus output capacity, I/O end equal to panic address plus 16, and I/O end below RAM.
  The panic and termination words no longer exist at this pin, and the only consumer now uses the checked backing endpoint directly.
- Add `SharedMemoryInitialization.initialMem_get?_above_ram`: for a checked layout and successful shared I/O initialization, every byte address at or above RAM has exactly the same optional map lookup as in the base map.
  A single private buffer-fold lemma proves preservation for all three overlays.
  The guards provide the buffer-capacity bounds; no new execution premise is imposed on any existing theorem.
- Add `SharedMemoryInitialization.initial_state_ram_get?`: after successful instance initialization, RAM offset `o` has exactly the optional byte lookup of `initialRam` at `o`, including out-of-range offsets.
- Add `SharedMemoryInitialization.initial_state_program_end_le_heap_end`: a successfully initialized instance's program endpoint is at or below its checked layout's heap endpoint.
  This factors the geometry previously repeated by the two image-loader proofs.
- Move `WholeRun.lastByte`, `imageByte?`, `imageParcel?`, `imageWord?`, `lastByte_some`, `imageByte?_bounds`, `imageParcel?_eq_some`, `imageWord?_eq_some`, `initialRam_fold_getElem?` and `sailInit_get?_image` from `Decoded.lean` into `WholeRun/ImageMemory.lean`.
  Their names and mathematical signatures are unchanged.
  The last proof now reads the initialized shared memory directly, uses checked array-size equality and has no reconstructed I/O or flag-word cases.
- `WholeRun.CodeInv.initial_image_facts` keeps its statement and now consumes the common program-end bound and image-byte theorem.
- `WholeRun.SystemInv.initialState` keeps its statement and names the initialized RAM/device/tape arguments explicitly.

The new loader lemmas and their migrated image proofs await compilation.
The next targeted build, `.constraints-repin-shared-foundation4.log` with marker `.constraints-repin-shared-foundation4.done`, checks `SharedMemoryInitialization`, `WholeRun.ImageMemory`, `Init`, `SystemInv`, `Bundles`, `SystemBlocks`, row-21 completeness and the jump return-value consumer.
Whitespace and forbidden-diff checks pass before launch.
The full whole-run simulation still depends on the obsolete I/O modules, and the flag-word soundness callers and both RAM-history admissions remain unfinished.

## Resumed integration check and halt-lane elimination

Date: 2026-11-24.
Lean HEAD: `152cf8c`; Jolt: `ff6fc6568`.
The fourth detached foundation check failed only in `HaltFlags.jumpCases` and the new initializer geometry argument.
The first foreground batch subsequently checked `HaltFlags`, row-21 completeness and the register-link consumer except for one index-coercion rewrite.
The latest initializer repair rewrites `output_end = io_end` before comparing their natural-number values.
The link consumer now states the source-length equality with its exact local bytecode row before rewriting.

The full `track-t-build.sh lake build JoltConstraints` integration check is running, with output in `.constraints-repin-foreground2.log`.
The tool transport timed out while the child build continued.
An event-based process-exit watcher records completion in `.constraints-repin-foreground2.done`; the watcher exit code is not the Lake build exit code.
The build result must be read from the completed Lake log.
The partial diagnostics already identify the old `PanicRestriction`, `TerminationRestriction` and `advice_below_input` interfaces as failing consumers of removed fields.
No final library or soundness-closure check has passed.

`Soundness/Layer1/HaltEndRule.lean` adds `selected_halt_of_next_padding`.
Its statement says that, for a selected real bytecode row with `NextIsNoop = 1`, the instruction halt kind is `some (if context.io.panic then panic else success)`.
Its premises are the existing field bound, constraint context and equations, selected-slot equality, real-row lookup and next-padding value; it introduces no program restriction.
The private algebra lemma eliminates the non-halt case by the nonzero field element 2, then identifies the claim from the halt kind.
This is the row-level obligation of the existing stopping theorem and is not yet compiled or integrated.
The stopping theorem itself still uses the obsolete termination-word argument.
`methods/soundness.md` now distinguishes this incomplete re-pin from the old green build and records the pinned stopping and shared-memory rules.

The remaining work is unchanged: replace the separate whole-run I/O simulations, remove all flag-word definitions and callers, finish soundness for both claims, settle the tracer-address restriction, prove both RAM-history completeness targets, migrate the public-I/O completeness assembly, update source references, run the full acceptance checks and commit the checked changes.

## Full integration result and shared-store proof

Date: 2026-11-24.
Jolt pin: `ff6fc6568`; checked Lean source before the new proof edits: `7bae35b`.
The completed `.constraints-repin-foreground2.log` ends with `error: build failed`.
The associated marker's exit zero belongs to the process-exit watcher and is not a passing Lake result.
The successful modules include `SharedMemoryInitialization`, `WholeRun.Init`, `WholeRun.ImageMemory`, `HaltFlags`, `Completeness.HaltEndRule` and `Completeness.RdWriteEqPCPlusConstIfJump`.
The checked shared-memory foundation is committed as `0569dbe`, and the checked halt/jump completeness migration as `574c4ff`.
The full build still fails in the old flag restrictions, `advice_below_input`, `ExecutionPrefix`, `WholeRun.Halt`, the branch completeness bound, `DeviceMemoryObstruction` and `WholeRun.SystemInv`.

The subsequent `.constraints-repin-foundation5.log` batch ran to completion and failed only in the new halt-lane elimination proof and `WholeRun.SystemInv`.
It checked the branch completeness repair, replacing strict transitivity with strict/non-strict transitivity at the padded trace bound.
The initial-state virtual-register proof and success-source scratch-register classification in `SystemInv` now pass; its halt primitive still needed a named preservation rule.
The halt-lane proof needed Boolean equality reduced before algebra and a restricted simplifier to avoid traversing the large characteristic bound.
These are proof-body repairs with unchanged statements.

The new declarations in `theorems/SharedMemoryExecution.lean` are candidates to move to JoltBytecode.
`store_raw_shape` says that an accepted one-byte store produces exactly the old state with that shared memory byte inserted.
`store_doubleword_shape` says that an MMU doubleword store returning `Ok true` produces exactly the old state with `Mmu.write_ram_doubleword` applied to its map, regardless of the RAM/I/O branch.
Both statements retain every other field, including the device, tape, code region and halt marker.
Their consumer obligations already occur in both RAM-history completeness targets and the whole-run memory simulation.
The private `guarded_fold_shape` factors the accepted-step/fold argument, and `byte_inserts_shape` factors the state-update/fold argument.
I read `Mmu::store_doubleword`, `Mmu::store_raw` and `Mmu::store_doubleword_raw` in the pinned tracer before adding these proofs.
The proof does not assume that an unchecked store succeeds or bypass its protection checks.

`Soundness/Layer3/Access.lean` adds two consequences of the pinned RAM claims.
`ramRa_unique_of_memory` takes the existing constraint context/equations and a cycle with `Load + Store = 1`, and proves that exactly one RAM selector equals one.
In particular, the access-count claim rules out the old all-zero selector escape for an executed load or store.
`ramInc_zero_of_selected_protected` takes a selected word whose public C mask is one and proves that its increment is zero.
The proof factors the common increment out of the protected sum and evaluates its remaining selected read.
These are local constraint consequences; address-domain and mask/protected-byte correspondence still need connecting to MMU execution before deciding whether `tracerAddressChecks` can be removed.

The next full batch is `.constraints-repin-integration4.log`, marker `.constraints-repin-integration4.done`.
It builds `JoltConstraints` plus the new shared-store and halt-lane modules explicitly.
The shared-store proofs and new RAM-guard consequences are not yet checked.
There is no completed soundness re-proof or RAM-history completeness result in this checkpoint.
No new admission, axiom, forbidden decision procedure or resource-limit increase was added.
The harness diff scan also needs clarification: its unanchored `decide +kernel` alternative matches deleted baseline lines in the obsolete `DeviceMemoryObstruction` module.
I requested correction to an added-line scan and have not changed the harness.


## Checked RAM-history completeness

Date: 2026-11-24.
Jolt pin: `ff6fc6568`; Lean checkpoint: `ce5f298`.
The targeted `.constraints-repin-memory-history10.log` batch passes.
Both `honestWitness_ramValEqInitialPlusPrefixRamInc` and `honestWitness_ramValFinalEqInitialPlusRamInc` now have checked proofs with unchanged statements.
The proofs compare the witness fold with shared memory, then telescope each selected store increment.
They cover RAM and I/O uniformly, including value-preserving stores to protected words.
The three #1949 admissions remain unchanged.
This milestone supersedes the earlier statements that the two RAM-history proofs remain open.

The checkpoint adds `Completeness/Helpers/PrefixSum.lean`, `RamHistoryProofHelpers.lean`, `RamHistoryReplay.lean` and `RamValReplay.lean`.
The common prefix-fold and prefix-sum lemmas replace a private register-history lemma rather than copying that proof.
`MemoryRowExecution.lean` now contains the shared load/store width classification, metadata and execution facts moved from Layer5, with their moved public statements unchanged.
It adds `accessRow_of_address`, `LoadRow.write_of_run`, `LoadRow.capture_of_run` and `StoreRow.memory_of_run` for the RAM-history callers.
`SharedMemoryExecution.lean` adds the non-store memory frame, successful-load shape and captured-word value lemmas.
These primitive facts are candidates to move to JoltBytecode.
`store_doubleword_shape` changed its successful result premise from `.ok (.Ok true) after` to `.ok result after` for an explicit `result : Result Bool ExecutionResult`; its exact memory-update conclusion is unchanged.
No execution-success assumption was removed from that theorem.

The measured slow modules are `RamHistoryProofHelpers` (21 seconds), `RamHistoryReplay` (31 seconds), and `RamValReplay` (17 seconds).
The two final completeness modules take about four seconds each.
These measurements include module elaboration and compilation, rather than individual tactic timings.
The batch also checks Layer1's `selected_halt_of_next_padding`, Layer3's RAM guard consequences and `WholeRun.SystemInv`.
The corresponding checked commits are `3bc7430`, `b60ee7f` and `ce5f298`.
The full library still fails in the old whole-run and soundness consumers.
The whole-run I/O simulations, flag-word soundness callers, public-I/O completeness assembly, final source-reference pass and full acceptance checks remain open.


## Checked shared-memory soundness steps

Date: 2026-11-24.
Jolt pin: `ff6fc6568`; source checkpoint follows `ce5f298`.
The batch `.constraints-repin-shared-checks12.log` passes for `LoadDoubleword`, `RamStoreAgreement` and both RAM-history completeness targets.
`layout_facts.lean` proves `new_lowest_address_ge_half_ram`, `new_input_end_eq_output_start` and `JoltDevice.readable_of_layout`.
These declarations show that the checked power-of-two I/O allocation lies above unsupported peripherals and that the advice, input, output and gap segments cover its byte addresses.
`Layer3/Layout.lean:130` adds `ram_domain_within_backing`: the verifier's admitted domain ends no later than the tracer's padded backing.
The arithmetic is factored over natural numbers and an opaque checked-domain option to avoid kernel recursion through the layout validator.
No resource limit was raised.

`SharedMemoryExecution.lean:200` adds `ram_doubleword_byte`, the byte-extraction fact for the map's packed doubleword.
`load_doubleword_of_checks` (line 229) and `store_doubleword_of_checks` (line 271) prove execution from the actual address, peripheral and protected-value checks for both RAM and I/O.
The byte-store fold uses the existing `Mmu.ProtectedMemory` relation to transport protection through intermediate byte writes.
These three primitive lemmas are candidates to move to JoltBytecode.
The module takes about 52 seconds to elaborate and compile in this batch.

The new `Layer5/SharedMemoryChecks.lean` contains the local constraint consequences used by the memory steps.
`ram_word_address_checks` (line 35) proves all eight address checks for any admitted word.
`memory_row_address_checks` (line 59) uses the access-count claim to apply those checks to an active memory row.
`unsupported_peripheral_false` (line 82) and `ram_word_peripheral_checks` (line 94) exclude peripheral dispatch from admitted words.
`protected_byte_mask_one` (line 112) relates the MMU's protected-byte predicate to public mask C, assuming that the execution code interval is the bytecode's interval.
`protected_store_of_constraints` (line 150) combines this correspondence, shared-word agreement and the protected-increment claim to prove the actual MMU protected-store check.
Its code-interval equality is an execution invariant, not a new global restriction; carrying that invariant through the prefix assembly remains open.
This module takes about 33 seconds to elaborate and compile.

Changed statements in this file group:

- `Layer5/RamAgreement.lean:24`: `OrdinaryRamAgreement` becomes `SharedRamAgreement`; the old relation required agreement only after an `inRam` premise, and the new relation requires every in-domain word to agree with the shared map.
- Its `advance_pc`, `afterWriteDst`, `initial`, `read`, `noEffect` and `noAccess` theorems now use that full relation; `read` no longer takes an `inRam` premise.
- `RamInitialization.initialRamWord_eq_ram_doubleword`: the old `inRam` premise is removed because initialization now uses the shared map at every index.
- `LoadDoubleword.load_ram_step` becomes `load_shared_step`; its old ordinary-RAM premise and external address-check premise are replaced by the invariant equality between the pre-state's layout and the public context's layout, and its RAM agreement covers every word.
- `StoreDoubleword.store_ram_step` becomes `store_shared_step`; its old ordinary-RAM and external address-check premises are replaced by the layout and code-interval invariant equalities plus full shared-word agreement.
- `RamStoreAgreement.store_ram_step_agreement` becomes `store_shared_step_agreement` with the corresponding invariant premises and full shared-word conclusion.
- `MemoryRows.lean` deletes the old panic-value, panic/termination-load and store-event helpers; those helpers describe removed flag words and have no replacement in the new memory contract.

`load_shared_step` and `store_shared_step` each take about 29 seconds to elaborate and compile.
Neither theorem takes `tracerAddressChecks`, a panic-word premise or a termination-word premise.
This settles the local MMU obligations from the pinned constraints.
Removing the global `tracerAddressChecks` field still requires migrating its callers, rather than claiming that its universally quantified program restriction follows from one satisfying witness.
The old prefix, stopping, whole-run I/O and public-output consumers remain unfinished, and the full library has not passed.

## Prefix migration and code-region frame checkpoint

Date: 2026-11-24.
Jolt pin: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Last checked memory-step commit: `ac7a9e5`.
This section records checked frame proofs and an uncommitted prefix migration; it does not report a green integration build.
I read `CodeGuard::new` and the protected-store checks in the pinned tracer's `tracer/src/emulator/mmu.rs` before connecting the code interval to the shared-store proof.

The first `.constraints-repin-code-frame1.log` build checked `TapeSemantics`, `IOSetupFrame`, `TapeTrace` and `TapeDeviceFrame`.
It failed on four local proof errors in the new source-extent extraction lemmas in `program_facts.lean`.
The repairs reduce the countdown at the final index, obtain a list bound before applying the minimum inequality, and identify singleton flattening with `List.map_eq_flatMap`.
Those repairs and `CodeRegionFrame` await the next batch.
`TapeSemantics` took 16 seconds, `IOSetupFrame` 72 seconds, `TapeTrace` 65 seconds and `TapeDeviceFrame` 64 seconds to elaborate and compile.
These are module timings, not individual tactic timings.

The checked frame declarations are:

- `Soundness/Layer5/TapeSemantics.lean:70`, `execWithTapeAnswer_relation`: a new generic preservation theorem over a state relation, its `InstructionFrame.Rules` and preservation under tape-cursor advance.
- `TapeSemantics.lean:98`, `execWithTapeAnswer_device_relation`: its statement is unchanged; its proof now instantiates the generic theorem.
- `TapeSemantics.lean:114`, `execWithTapeAnswer_codeRegion`: every successful relaxed instruction retains `codeRegion`, including stores and both explicit halts.
- `Completeness/Helpers/IOSetupFrame.lean:26`, `Trace.preState_projection_relation`, and line 58, `Trace.finalTraceState_projection_relation`: the existing trace-fold argument is generalized from the device projection to an arbitrary state projection and reflexive/transitive relation.
- The existing `Trace.preState_device_relation` and `Trace.finalTraceState_device_relation` retain their statements and instantiate those generic trace lemmas.

New statements awaiting validation:

- `program_facts.lean`, `ExpandedRows.source_extents`: filtering one expansion to rows with zero remaining countdown and taking `(address, is_compressed)` yields exactly its source extent.
- `program_facts.lean`, `expand_program_source_extents`: the bytecode's extracted source extents equal the decoded program's source-address/compression list, in order.
- `Soundness/Layer5/CodeRegionFrame.lean`, `initial_state_codeRegion`: successful instance initialization and expansion imply that the initialized `codeRegion` equals `ramCodeRegion` of the materialized bytecode and initialized layout.
- `CodeRegionFrame.lean`, `UntrustedAnswerRun.final_codeRegion`: a certified prefix's final code region equals that public interval computed with its initial layout.
- `Layer6/MemoryRowAppend.lean`, `rawEntry_memory_invariants`: a raw row entry preserves the context layout and that code interval; this discharges the local store theorem's invariant premises without adding a program restriction.

Changed prefix statements awaiting validation:

- `Layer6/ExecutionPrefix.lean`, `RepresentsPrefix.cutRam`: old agreement excluded the synthetic termination index at the next and final columns; new agreement quantifies over every `Fin params.ramSize` index.
- `ExecutionPrefix.lean`, `Represents.finalRam`: the same exception is removed from final agreement.
- `Layer6/PrefixState.lean`, `BoundaryState` and `ExpansionState`: the `terminationWord` field and its conditional zero-word obligation are deleted; all other fields currently retain their old statements, including the old stopping predicates that still require migration.
- `Layer6/RamCutAgreement.lean`, `finalRamWord_ordinary`: the old initialized-run statement with an ordinary-RAM premise is replaced by `finalRamWord_eq_ram_doubleword`, valid for any plain trace and every natural-number index.
- `RamCutAgreement.lean`, `ramAgreement_iff`: old image agreement outside termination was equivalent to ordinary-RAM agreement plus device agreement; new agreement at every index is equivalent to `SharedRamAgreement` for a plain trace, without a constraint context or execution premise.
- `RamCutAgreement.lean`, `ordinary_memory_step` and its supporting termination-index helpers are deleted because the shared-memory load/store steps already provide the full update contract.
- `Layer6/PlainRow.lean`, `representsPrefix_push`: the result now covers every RAM word, and its obsolete device-equality premise is removed; unchanged shared memory and the zero-address constraint suffice.
- `PlainRow.lean`, `rawEntry_state`: its statement is unchanged and its visibility becomes public for the code/layout invariant consumer.
- `PlainRow.lean`, `append_expansion_row_of_termination` is deleted; its general append proof becomes `append_expansion_row`, without the conditional termination-word premise.
- The former `append_expansion_row` wrapper's zero-RAM-address premise is also removed; it is unnecessary when the caller already supplies full prefix agreement.
- `Layer6/MemoryRowAppend.lean`, `ExpansionState.memoryAt`: old output was ordinary-RAM agreement at the prepared state plus a separate device-image agreement at the retained prefix; new output is full shared-word agreement at the prepared state.
- `MemoryRowAppend.lean`, `append_memory_row`: replaces `DeviceMemoryStepAgreement` and a termination-store event with full shared-word agreement at the next and final columns.
- Its `memory_step_mono` and `exists_fin_push` event helpers are deleted.
- `Layer6/MemoryRowExecution.lean`, `load_row_execution`: removes the restrictions, readiness, selected-slot-number, device, conditional termination, device-equality and redundant address-encoding premises; takes shared RAM agreement and the prepared layout equality, and returns execution, register agreement and full next/final shared RAM agreement.
- `MemoryRowExecution.lean`, `store_row_execution`: makes the same replacement, additionally taking the prepared code-interval equality supplied by `rawEntry_memory_invariants`.
- `Layer6/RowStepMemory.lean`, `append_load_row` and `append_store_row`: remove the temporary-restrictions and honest-advice premises; consume the common shared agreement and invariant equalities, without a RAM/device address split.
- `Layer6/RowStepJalr.lean`, `append_nonmemory_row` and `append_jump_row`: remove device equality from the non-memory append contract; full shared-memory agreement depends on the byte map, allowing halt metadata to change independently.

`BoundaryStart`, `ExpansionFinish`, `DivisionAppend`, `RowStep`, `RowStepJalr` and `RowStepTerminal` migrate their callers and structure constructors to these statements.
`BoundaryStart` deletes the initial-device buffer overlays and flag-word-zero helpers, and compares the empty run directly with initialized memory.
`DivisionAppend` removes its termination-store transport proof and compares every shared word in the replay.
No new admission, axiom, forbidden decision procedure or resource-limit increase was introduced.
The added-line scan and `git diff --check` pass at this checkpoint.
`JoltBytecode/` and `LeanRV64D/` remain untouched.

The remaining work still includes explicit-halt prefix/stopping reconstruction, both public panic claims in the exported soundness theorem, deletion of the separate whole-run I/O simulation, migration of public-I/O completeness/output assembly, removal of restriction definitions and old callers, source-reference updates, a green full build, final axiom checks and the complete harness checks.
