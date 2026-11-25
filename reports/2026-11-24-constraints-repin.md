# JoltConstraints repin to ff6fc6568

Date: 2026-11-24.
Jolt revision inspected: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean baseline: `3522261`, branch `split/c-constraints`.
Final update: 2026-11-25.
The re-pin is complete at `3ff14b2`: `lake build JoltConstraints` succeeds and `JoltInstance.soundness` depends only on `propext`, `Classical.choice` and `Quot.sound`.
The section "Final state" below records the final step; the sections after it are the working log and describe the revisions they name.
No push or branch switch has occurred; `JoltBytecode/` changed only through the merge of `split/b-bytecode` and the import trim from `perf/constraints-build-time`, and `LeanRV64D/` did not change.

## Final state (2026-11-25)

The re-pin is complete at `3ff14b2` on `split/c-constraints`.
`track-t-build.sh lake build JoltConstraints` succeeds; the log is `.constraints-repin-final10.log` and ends with:

```
✔ [2474/2475] Built JoltConstraints (2.6s)
Build completed successfully (2475 jobs).
```

`Soundness/soundness.lean` prints the axioms of the main theorem during that build:

```
info: JoltConstraints/theorems/Soundness/soundness.lean:43:0: 'JoltInstance.soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`JoltInstance.soundness` takes no temporary program restriction.
Its premises are the field premise `JoltField F` and `JoltInstance.SoundnessAssumptions`, which contains only `RamRegionFits`.
The completeness assembly, both RAM-history completeness theorems and the three #1949 admissions are as recorded in the sections below.

### Branches merged in this step

- `split/b-bytecode` (merge commit `6f1b2b2`) brings the total HostIO model from Jolt #2410.
  `JoltISA.execHostIOWith` now takes a guest-byte reader that returns `Option`, ignores rejected reads and invalid events, and always retires.
  `JoltISA.execHostIO_result` says each call leaves the state unchanged or only appends bytes to the advice tape.
  `JoltISA.execHostIO_succeeds` says each call retires.
- `perf/constraints-build-time` (merge commit `84d3be2`) brings three commits.
  `ccd6b14` imports only the Mathlib modules each library uses, and adds `ExceptT.run_bind`, `ExceptT.run_liftM`, `bind_map_left` and `bind_assoc` to two `simp` calls in `WholeRun/NonInterference.lean` (`jump_to_eval` and `jump_to_odd`) that needed them after the trim.
  `e2bda0f` tries `rfl` before `simp` in the row checks of `expansion_facts.lean`.
  `8f7e70c` imports only the JoltConstraints modules each file uses.
  No import from that rewrite was reverted.

### Proof repairs

- `WholeRun/Bundles.lean`, `addi_device`: the device-frame proof now gives `preservation_auto` the write rule applied to its value and an explicit rule for the final `pure`.
- `WholeRun/SharedMemorySim.lean`, `ld_outcome`: the lower I/O bound now rewrites the load address to `base + sign_extend imm` before `omega`.
- `WholeRun/SharedMemorySim.lean`, `narrow_store_core`, and `WholeRun/AtomicMemorySim.lean`, `io_amo_word`: `load_raw_value` already states the byte equation in the direction `store_finish` needs, so the extra `.symm` is removed.
- `WholeRun/RunInv.lean`: `aligned_or_below` uses the public `PlatformMemory.toNat_and_neg8` instead of a macro that named a private copy in `SharedMemorySim`, which no longer exists.
- `WholeRun/CodeInv.lean`: `CodeIntact.of_related` gives `Related.ram` its address explicitly, and `initial_image_facts` names `JoltConstraints.initial_state_program_end_le_heap_end` in full.
- `WholeRun/Top.lean` (in `3ff14b2`, not `94ae194`): `HonestTrace.sail_reproduces` calls `HonestTrace.final_halt` by its name in the `WholeRun` namespace, because field notation on `trace` does not find it.

None of these repairs changes a statement.

### HostIO consumers

The old model's byte reader could fail, so several modules carried frame rules for each step of `readHostBytes`.
With the total model each consumer now case-splits on `execHostIO_result`, or zeta-reduces the call's `have` bindings and reuses the generic monadic rules.
These proof-only changes do not alter any statement:
`execHostIO_keeps_state` (`execution_facts.lean`), `JoltHostFrame.execHostIO_frame` (`Completeness/Helpers/HostIOFrame.lean`), `Register42VRegs.execHostIO_frame` (`Completeness/Helpers/RegistersValProofHelpers.lean`), `tracks_hostIO` (`WholeRun/Ghost.lean`), `commutes_hostIO` (`WholeRun/NonInterference.lean`) and `swap_execHostIO` (`Soundness/Layer7/TapeRebuild.lean`).

The following helpers served only the old byte reader and are deleted:
`JoltHostFrame.{pure_rule, bind_rule, read_rule, get_rule, throw_rule, modifyAdvice_rule, loadByte_rule, readHostBytes_frame}`, the same set in `Register42VRegs`, `JoltNextPCFrame.readHostBytes_frame` and `execHostIOWith_frame`, the `SailAndVRegsUnchanged` and `SailUnchanged` namespaces in `execution_facts.lean`, `tracks_readHostBytes`, `commutes_readHostBytes`, `swap_load` and `swap_readHostBytes`.
None had a caller outside these proofs.

### Removed assumptions

- `JoltInstance.HostCallsSucceed` (was in `Soundness/Layer5/HostCallRestriction.lean`, now deleted):

  ```lean
  def JoltInstance.HostCallsSucceed (joltInstance : JoltInstance SourceInstruction) : Prop :=
    ∀ (privateInputs : JoltPrivateInputs)
      (run : JoltConstraints.Soundness.UntrustedAnswerRun joltInstance privateInputs)
      (next : Fin run.bytecode.size) (pre : SailJoltState),
      run.NextStep next pre →
        match run.bytecode[next].instruction with
        | .VirtualHostIO => ∃ post, execHostIO pre = .ok RETIRE_SUCCESS post
        | _ => True
  ```

  It required that every attempted host call in the modelled execution succeed.
  At Jolt `ff6fc6568` the tracer logs and ignores invalid or rejected host calls (`tracer/src/instruction/virtual_host_io.rs`, `tracer/src/emulator/host_io.rs`), and the merged model does the same.
  The one use of the restriction, `host_call_exec_sail_frame`, now obtains the successful call from `execHostIO_succeeds`.
  No premise replaces it.
- `JoltInstance.TemporaryRestrictions` (was in `Soundness/Assumptions.lean`): its only remaining field was `hostCallsSucceed`, so the structure is deleted together with every `restrictions` argument.

`model_review.md` no longer lists the host-call row among the theorem's assumptions, and marks finding 2 of the 2026-10-29 audit (the HostIO END marker) as resolved by the re-pin.

### Statements changed in this step

Every change below removes a premise; no conclusion changes.

| Declaration | File | Old premises removed | New statement |
|---|---|---|---|
| `JoltInstance.soundness` | `Soundness/soundness.lean` | `(restrictions : joltInstance.TemporaryRestrictions)` | same premises otherwise, same conclusion `joltInstance.InLanguage` |
| `JoltInstance.sail_soundness` | `WholeRun/Top.lean` | `(restrictions : joltInstance.TemporaryRestrictions)` | otherwise unchanged |
| `soundness_reconstruct_trace` | `Soundness/TopLevel.lean` | `(restrictions : joltInstance.TemporaryRestrictions)` | otherwise unchanged |
| `soundness_execution_prefix_agreement` | `Soundness/Layer6/PrefixAgreement.lean` | `(restrictions : joltInstance.TemporaryRestrictions)` | otherwise unchanged |
| `JoltInstance.boundary_step` | `Soundness/Layer6/PrefixAgreement.lean` | `(restrictions : joltInstance.TemporaryRestrictions)` | otherwise unchanged |
| `JoltInstance.row_step` | `Soundness/Layer6/RowStep.lean` | `(restrictions : joltInstance.TemporaryRestrictions)` | otherwise unchanged |
| `row_extension` (private) | `Soundness/Layer6/RowStep.lean` | `(restrictions : inst.TemporaryRestrictions)` | otherwise unchanged |
| `host_row_step`, `jal_row_step`, `jalr_row_step` | `Soundness/Layer6/RowStepKinds.lean` | the section variable `(restrictions : inst.TemporaryRestrictions)` | otherwise unchanged |
| `append_host_row` | `Soundness/Layer6/RowStepTerminal.lean` | `(restrictions : inst.TemporaryRestrictions)` and `(honestAdvice : ∀ n : Fin run.rows.size, run.rows[n].someTracerAdvice? = honestTracerAdviceAtStepN inst.program run.rows n)` | otherwise unchanged; the advice premise only fed `run.NextStep`, which the restriction needed |
| `host_call_exec_sail_frame` | moved from `Layer5/HostCallRestriction.lean` to `Layer5/HostCallRegisterFrame.lean` | `(restricted : joltInstance.HostCallsSucceed)` and `(ready : run.NextStep next pre)` | `∃ post, execWithTapeAnswer (run.bytecode[next].instruction.withRuntimeAdvice advice) answer pre = .ok RETIRE_SUCCESS post ∧ post.sail = pre.sail ∧ post.vregs = pre.vregs`, unchanged |
| `host_call_selected_step` | `Soundness/Layer5/HostCallRegisterFrame.lean` | `(restricted : joltInstance.HostCallsSucceed)` and `(ready : run.NextStep nextRow pre)` | otherwise unchanged |

`Soundness/Assumptions.lean` now imports `Layer5.MemoryAccessRestriction`, `Layer5.RuntimeAdvice` and `theorems.execution_facts` in place of the deleted module, so that every downstream module keeps the same import closure.

### Commits

- `94ae194` repairs the whole-run proofs listed under "Proof repairs", except the `Top.lean` repair, which is in `3ff14b2`. It also deletes `Soundness/Layer5/HostCallRestriction.lean`.
- `8e7dae3` ports the HostIO consumers.
  Its message says "No statement changes", but it deletes 29 public declarations: `JoltHostFrame.{pure_rule, bind_rule, read_rule, get_rule, throw_rule, modifyAdvice_rule, loadByte_rule, readHostBytes_frame}` and the same eight in `Register42VRegs`; the `SailAndVRegsUnchanged` namespace (`Preserves`, `pure_rule`, `bind_rule`, `read_rule`, `get_rule`, `throw_rule`, `modify_rule`, `load_rule`, `readHostBytes_rule`); the `SailUnchanged` namespace (`Preserves`, `read_rule`); and `JoltNextPCFrame.readHostBytes_frame` and `JoltNextPCFrame.execHostIOWith_frame`.
  It also deletes four private helpers: `swap_load`, `swap_readHostBytes`, `tracks_readHostBytes` and `commutes_readHostBytes`.
- `3ff14b2` removes `HostCallsSucceed` and `TemporaryRestrictions`.
- The commit that adds this section updates this report, `JoltConstraints/documentation/model_review.md` and `methods/soundness.md`.

The HostIO consumers do not build from the merge `6f1b2b2`, which brings in the total HostIO model, until `8e7dae3` ports them.
The intermediate commits `6f1b2b2`, `84d3be2` and `94ae194` therefore do not build on their own; the branch head builds.

### Checks

- The forbidden-name scan (`terminationThenStall`, `panicStoresOne`, `claimsNoPanic`, `HostCallsSucceed`, `overflowChecks` and their capitalised forms) over `JoltConstraints/*.lean` and `JoltBytecode/*.lean` prints nothing.
- Over `git diff 6b6a9df` outside `JoltBytecode/` and `LeanRV64D/`, the only added line that mentions `sorry`, `admit`, `native_decide`, `bv_decide`, `decide +kernel`, `axiom` or a heartbeat, recursion-depth or instance-synthesis option is a prose sentence in the bytecode re-pin report brought in by the merge. No Lean source adds any of them.
- `git diff --check` reports no whitespace errors.

### Remaining documentation work

`docs/whole-run-theorem.md` still describes the whole-run statement before the re-pin: it shows `sailOutputs`, `sailPanicWord`, the `TemporaryRestrictions` table and the old `BlockConforms` deviations.
`BlockConforms` now has only the `riscv` and `no_code_store` fields.
That page needs a rewrite against `WholeRun/Top.lean`; this step did not change it.
The historical sections of `methods/soundness.md` and of this report still mention the removed restrictions; they describe earlier revisions.

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

## Statement changes earlier in the re-pin

The following records the interfaces changed earlier in the re-pin; the statements changed in the final step are listed under "Final state".

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

## Checkpoint before the final step (shared-public22, superseded)

The re-pin is incomplete because the full library and whole-run simulation have not yet built.
The seventeenth through twenty-first batches checked `JoltInstance.soundness` for both public panic claims and printed exactly `propext`, `Classical.choice` and `Quot.sound` in its axiom closure.
Commit `b852fe3` records that checked proof and removes the three flag-word restrictions and their definition modules.
`TemporaryRestrictions` contains only `hostCallsSucceed`.
The new RAM access-count and protected-increment claims supply the selected word's address and protected-value checks.
The obsolete standalone `TracerAddressChecks` definition and its two dead consumers are removed at `3bb089d`.

The completeness assembly checks at `78ed82d`.
Both requested RAM-history completeness theorems retain their statements and are proved at `ce5f298`; the three #1949 admissions are unchanged.
Native/narrow store inversion checks at `621fcd1`, and atomic inversion at `86d4cfa`.
Conditional-store elaboration remains pending.
The eighteenth build exposed SC scratch-register and continuation normalization errors and a heartbeat timeout without any resource override.
The nineteenth batch checked every conditional-store declaration except `scw_ram_guard`, which still exceeded the default heartbeat budget.
The twentieth batch checked that extracted window/store argument, but the outer SC.W prefix assembly still timed out.
The twenty-first batch checked the window argument but found prefix-state normalization errors and a final guard-transport reduction timeout.
The twenty-second batch repairs those equalities explicitly; the public guard statement remains unchanged.

The working tree deletes `WholeRun/Io.lean`, `IoAmo.lean`, `LoadAddress.lean` and the obsolete `Soundness/Layer5/DeviceMemory.lean`.
Reusable Sail-only facts are in the checked `PlatformMemory` and `PlatformStore` modules.
`SharedMemorySim` and `AtomicMemorySim` compare actual stores in the shared byte map at every address.
They contain no second device I/O equality or flag-word restrictions.
Their decoded-block and whole-run callers have been migrated, including deletion of the old zero-doubleword-load workaround.
These source changes await their conditional-store prerequisite; they are not claimed as checked whole-run results.
The nineteenth build checked the cleanup of the unused tracer-address restriction and all affected soundness consumers.

The methods pin and reviewed Rust citations are updated; commit `cea7d6c` contains the comment-only citation pass.
The complete final declaration-and-line inventory, full root build, exact harness checks, final commits and clean `JoltConstraints/` tree remain outstanding.
The independent blind read-back below certifies the literal main soundness statement's interpretation, not the pending whole-run migration.

## Early core validation (superseded)

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

Current declaration locations for the pending prefix batch:

| File | Declaration | Line |
| --- | --- | --- |
| `JoltConstraints/theorems/program_facts.lean` | `ExpandedRows.source_extents` | 1019 |
| `JoltConstraints/theorems/program_facts.lean` | `expand_program_source_extents` | 1058 |
| `JoltConstraints/theorems/Soundness/Layer5/CodeRegionFrame.lean` | `initial_state_codeRegion` | 16 |
| `JoltConstraints/theorems/Soundness/Layer5/CodeRegionFrame.lean` | `UntrustedAnswerRun.final_codeRegion` | 34 |
| `JoltConstraints/theorems/Soundness/Layer6/ExecutionPrefix.lean` | `RepresentsPrefix` | 52 |
| `JoltConstraints/theorems/Soundness/Layer6/ExecutionPrefix.lean` | `Represents` | 67 |
| `JoltConstraints/theorems/Soundness/Layer6/PrefixState.lean` | `BoundaryState` | 27 |
| `JoltConstraints/theorems/Soundness/Layer6/PrefixState.lean` | `ExpansionState` | 107 |
| `JoltConstraints/theorems/Soundness/Layer6/RamCutAgreement.lean` | `finalRamWord_eq_ram_doubleword` | 14 |
| `JoltConstraints/theorems/Soundness/Layer6/RamCutAgreement.lean` | `ramAgreement_iff` | 24 |
| `JoltConstraints/theorems/Soundness/Layer6/PlainRow.lean` | `representsPrefix_push` | 572 |
| `JoltConstraints/theorems/Soundness/Layer6/PlainRow.lean` | `rawEntry_state` | 1049 |
| `JoltConstraints/theorems/Soundness/Layer6/PlainRow.lean` | `append_expansion_row` | 1134 |
| `JoltConstraints/theorems/Soundness/Layer6/MemoryRowAppend.lean` | `ExpansionState.memoryAt` | 15 |
| `JoltConstraints/theorems/Soundness/Layer6/MemoryRowAppend.lean` | `rawEntry_memory_invariants` | 33 |
| `JoltConstraints/theorems/Soundness/Layer6/MemoryRowAppend.lean` | `append_memory_row` | 51 |
| `JoltConstraints/theorems/Soundness/Layer6/MemoryRowExecution.lean` | `load_row_execution` | 33 |
| `JoltConstraints/theorems/Soundness/Layer6/MemoryRowExecution.lean` | `store_row_execution` | 55 |
| `JoltConstraints/theorems/Soundness/Layer6/RowStepMemory.lean` | `append_load_row` | 34 |
| `JoltConstraints/theorems/Soundness/Layer6/RowStepMemory.lean` | `append_store_row` | 71 |
| `JoltConstraints/theorems/Soundness/Layer6/RowStepJalr.lean` | `append_nonmemory_row` | 16 |
| `JoltConstraints/theorems/Soundness/Layer6/RowStepJalr.lean` | `append_jump_row` | 90 |

The next detached batch is `.constraints-repin-prefix-migration1.log`, with marker `.constraints-repin-prefix-migration1.done`.
It builds `JoltConstraints`, `CodeRegionFrame`, `RamCutAgreement`, `PrefixState`, `MemoryRowExecution` and both RAM-history completeness targets together.
No result is claimed for that batch yet.
The checked frame refactor and documentation checkpoint are committed as `a9a48d6`; the prefix changes remain uncommitted pending integration.

### Explicit-halt prefix migration (pending validation)

The unused replay-after-stall proof is deleted from `Layer7/StallSuffix.lean`.
The following declarations have no remaining Lean caller outside that obsolete proof, and their dependent obsolete helpers are deleted together:

- `StallSuffixInvariant`.
- `stall_jal_immediate_zero`.
- `register_unchanged_of_no_write`.
- `stall_executed_jal_immediate_zero`.
- `stall_next_cycle_of_remaining`.
- `stall_jal_step`.
- `expanded_branch_source_singleton`.
- `expanded_branch_same_address`.
- `stall_branch_model_target`.
- `stall_branch_witness_target`.
- `stall_branch_control_values`.
- `stall_branch_controls_succ`.
- `stall_branch_replay_target`.
- `stall_branch_replay`.
- `stall_branch_step`.
- `stable_jalr_target`.
- `stable_written_jalr_link`.
- `regidx_bne_self_false`.
- `stable_written_jalr_replay_target`.
- `jalr_destination_base_address_eq_iff`.
- `stamp_sequence_instruction_member`.
- `expanded_arch_jalr_singleton`.
- `architectural_jalr_same_source_row`.
- `stall_arch_jalr_preserved_step`.
- `stall_jalr_preserved_base_step`.
- `xreg_address_ne_zero_of_notX0`.
- `selected_written_jalr_base_succ`.
- `stall_jalr_written_base_step`.
- `expanded_virtual_jalr_source`.
- `stall_system_jalr_step`.
- `expanded_jalr_operand_forms`.
- `stable_stall_control_flow`.
- `stall_suffix_initial_jal`.
- `represented_last_branch_invariant`.
- `stall_suffix_initial_branch`.
- `stall_suffix_initial_jalr`.
- `stall_suffix_initial`.
- `stall_suffix_replays_source`.
- `stable_stall_source_no_store`.
- `stall_suffix_no_store`.
- `soundness_stall_suffix_zero_ram_effects`.

The foreground foundation batch `.constraints-repin-prefix-foundation2.log` completed successfully (9,572 jobs).
It checked `program_facts` (34 seconds), `CodeRegionFrame` (96 seconds), `RamCutAgreement` (28 seconds), `ExecutionPrefix` (29 seconds), the pre-halt-migration `PrefixState` (15 seconds), `MemoryRowExecution` (4.3 seconds), and both RAM-history completeness targets (3.0 and 4.9 seconds).
Some prerequisite modules rebuilt in 73–102 seconds, as recorded in that log.
The current halt migration has not yet been checked.

Additional statement changes in the explicit-halt migration:

- `Layer1/HaltEndRule.lean` adds `nextIsNoop_zero_or_one`, `halt_lane_nonzero` and `selected_halt_forces_next_padding`; the last binds any selected syntactic halt to a padding successor under either public panic claim.
- `Layer6/SelectedRows.lean` moves `LastJump.selected_represented_row` into the public `RepresentsRows.selected_row`, generalizing its run argument from `UntrustedAnswerRun` to `Trace` without an execution premise.
- `SelectedRows.lean` adds `ConstraintContext.entry_row` and `ConstraintContext.halt_terminal`, using existing preprocessing admission.
- `Layer5/TapePrefix.lean` retains the unchanged statement of `honestTracerAdviceAtStepN_extract` and its private helpers from `Layer7/TerminationStore.lean`.
- `Layer7/TerminationStore.lean` is deleted, including truncation helpers used only by the old termination-store argument.
- `Layer5/MemoryAccessRestriction.lean`, `UntrustedAnswerRun.NextStep`, replaces `¬ row.StableStall` with `¬ row.Halts` in its earlier-stop and source-boundary clauses.
- `Layer6/PrefixState.lean`, `BoundaryState` and `ExpansionState`, make that same replacement in `noEarlierStop`, `ready`, `next` and `notStopped`.
- `Layer6/PlainRow.lean`, `PlainRow`, newly excludes `JoltSuccess` and `Panic`; they now have an explicit row case.
- `PlainRow.RawRowEntry` replaces its boundary non-stall requirement with non-halt.
- `Layer6/PrefixAgreement.lean`, `boundary_step` and `soundness_execution_prefix_agreement`, replace stable-stall endpoints and earlier-stop exclusions with explicit halts.
- `Layer6/RowStepKinds.lean`, `row_kind`, adds the alternative `∃ kind destination, instruction = (match kind with | .success => .JoltSuccess destination | .panic => .Panic destination)`.
- `Layer5/Jal.lean`, private `jal_write_value` becomes public `jump_write_value`; its JAL instruction equality is replaced by `opcodeFlag row.instruction .Jump = true`.
- `Layer5/Halt.lean` adds `halt_step`, covering both kinds, with the selected jump link write and unchanged shared memory.
- `Layer6/RowStepJalr.lean`, `jump_traits` and `append_jump_row`, replace the JAL-or-JALR shape premise with the Jump flag plus destination metadata; both existing jumps and both halts use the common append proof.
- `Layer6/RowStepTerminal.lean` adds `append_halt_row`, parameterized by the halt kind.
- `Layer6/DivisionAppend.lean`, `RunExtends.prefix_observations`, replaces the StableStall equivalence with Halts equivalence and removes its termination-store equivalence.
- `DivisionArithmeticRow.notStoresTerminationAt` is deleted as unused.
- `Layer7/StallSuffix.lean`, `noncontrol_next_pc`, replaces exclusions of JAL and JALR with `opcodeFlag instruction .Jump = false`, which also excludes halts.
- `Layer6/TerminalNextPC.lean`, private `terminal_noncontrol`, makes the same replacement; its caller derives that no halt can have a real successor from the halt lane.
- `StallSuffix.stall_jal_next_target` and `selected_jalr_next_target` retain their statements but use the unconditional Jump guard in row 14, deleting the ShouldJump argument.
- `Layer7/LastJump.lean` retains only the still-used `unexpanded_zero_of_padding`, `nonterminal_at_last_cycle_impossible` and `selected_terminal_nonjump_flags`; the old stopping classification and its unused private branch/zero-boundary helpers are deleted.
- `Layer7/Stopping.lean` adds `RepresentsRows.halt_kind`: every represented syntactic halt has `haltKind? = some (if context.io.panic then .panic else .success)`.
- `Stopping.soundness_stopping`: old input included temporary restrictions, real-row/no-earlier-stall/advice premises and a cut ending at a stall; new input is an executed represented prefix and a cut at padding, an explicit halt or the domain boundary.
  Its old last-row conclusion was StableStall; its new last-row conclusion is Halts, with nonemptiness and equality at every final shared RAM word.
  The former excluded synthetic termination word is included.
- `TopLevel.soundness_reconstruct_trace` retains its signature and consumes the new stopping contract.

The fresh read-only reviewer `halt_prefix_readback` read comment-stripped declarations independently at Lean HEAD `a9a48d6`.
It recorded these SHA-256 hashes: Stopping `4d878c10205d67d5c337eae73fd6e8c59372f0908c0c284bf2985b314b8e5ab1`; SelectedRows `512ab2b349d3eef55736bc5fb4031e834bc18948b452592ba7849b9e150cfe67`; ExecutionPrefix `d73c641e2a7e01d41706e7e2ddfb1352e11970e73bb6fc3f7a639b00e090d6ef`; PrefixState `90da7b38ef5c5ef19a2b84387c2f5b85b59034d6af7d9a6beae233b379207a66`.
Its literal read-back identified the exact cut disjunction, syntactic Halts, full-domain RAM agreement, no execution certificate for `RepresentsRows.halt_kind`, and the absence of honest-advice from `ExpansionState` itself.
It did not run Lean or issue a fidelity verdict.
My separate comparison with `specs/halt-end-rule.md` finds that these clauses provide the required first-halt cut and both public claims when combined with the prefix invariant's no-earlier-halt clause.
The exported soundness/output assembly still needs to consume the halt-kind equality, and compilation remains required.
Prose-only edits to PrefixState after the read-back update descriptions from stalls to halts; no reviewed type changed afterward.

No new admission, axiom, forbidden decision procedure or raised resource limit was introduced in this batch.
`tracerAddressChecks` remains in the global assumptions until its obsolete whole-run and device consumers are removed; the local shared-memory reconstruction derives its checks directly.
The next detached integration batch is `.constraints-repin-prefix-halt-integration1.log`, with marker `.constraints-repin-prefix-halt-integration1.done`.
It builds `JoltConstraints` and all current prefix/halting targets together.

### Halt claim and shared output assembly (pending validation)

Date: 2026-11-24.
Jolt revision remains `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean HEAD is `22db65c`; the changes below remain uncommitted.
The preceding detached integration build failed, rather than completing the migration.
Its local halt failures were a numeral-cast proof in `halt_lane_nonzero` and the unavailable `JoltField` alias in `Layer5/Halt.lean`.
Those are repaired in this batch, using the explicit characteristic inequality already required by the halt proof.
The build also found remaining device-array references in `advice_below_input`, the obsolete `DeviceMemoryObstruction`, and `WholeRun/Halt`, plus the unported value/width/backing-bound contracts in `WholeRun/Bundles`.
Those latter migrations are still open.

The output assembly now uses two separate consequences of Jolt's pinned checks.
Constraint 26 compares final shared-memory output words with public bytes.
Row 21 identifies the final halt kind, and actual halt execution sets the device panic Boolean to that kind.
No synthetic panic or termination memory word enters either argument.
The existing `execHalt_shape` primitive calculation supplies the actual final panic update; no prepared-PC or register-agreement hypothesis is added to the claim theorem.
These proof edits have not yet passed Lean.

Additional declaration changes:

- `Layer5/Halt.lean`, new `execHalt_afterWriteDst`: for either kind, a canonical destination and prepared PC/link reads determine the explicit post-state obtained by writing that link, resetting nextPC to the source and recording the kind.
  This is the former inline calculation in `halt_step`, factored for reuse; it is a candidate to move into JoltBytecode.
- New `halt_instruction_of_kind`: `instruction.haltKind? = some kind` implies the corresponding `JoltSuccess dst` or `Panic dst` shape for some destination.
  Its proof splits the three alternatives of the halt classifier, not the full instruction set.
- New `execWithTapeAnswer_halt_eq`: runtime-advice patching and the arbitrary tape answer leave either shared halt body unchanged.
- New `execWithTapeAnswer_halt`: combines the preceding execution calculation with the prepared register reads.
- `Layer7/Stopping.lean`, new `represented_final_panic`: a completed executed represented trace has final device panic equal to `context.io.panic`, for both Boolean claims.
  The statement takes the already available bytecode equality and row representation, without any flag-word restriction.
- `Layer8/OutputWords.lean`, `public_words_determine_matches_outputs`: old premises were the device setup relation, an output-array bound, and public-word equality below RAM excluding termination; new premises are final panic equality and equality of the actual final shared-memory words on `[input_start, output_end)`.
  The output capacity follows from `JoltDevice.outputsOf_size`; there is no output-bound premise.
  The conclusion remains `trace.matches_outputs joltInstance`.
- `TopLevel.lean`, `soundness_matches_outputs`: the public signature and conclusion are unchanged.
  Its proof now consumes `Represents.finalRam` for every index, reads the new output-end mask, and combines `represented_final_panic` with the output-byte argument.
  The needed bytecode equality follows from the two successful expansions, rather than becoming a new theorem premise.
- `Layer5/Fence.lean`, `fence_step`: replaces the old ordinary-memory agreement with `SharedRamAgreement`, retaining unchanged-memory execution and next/final agreement over the full shared domain.
- `Soundness/Assumptions.lean`, `JoltInstance.TemporaryRestrictions`: the former `tracerAddressChecks : joltInstance.TracerAddressChecks` field is deleted.
  Together with the previously removed three flag-word fields, the structure now contains only `hostCallsSucceed`.
  No soundness reconstruction consumer uses the tracer field: selected memory rows derive all required address checks from the RAM selector bounds and checked layout.
  The obsolete standalone `TracerAddressChecks` predicate and old device-memory lemmas that mention it remain until the separate whole-run I/O simulation is removed.
  This does not claim the remaining whole-run proof has compiled.

`Completeness/Helpers/RamOutputProofHelpers.lean` is also being migrated:

- Deleted `overlayRamBytes_below_input` and `finalRamWord_eq_ramPublicIoWord`, which reconstructed a second image from device-owned buffers.
  The former statement compared buffer overlays below the input; the latter equated a device-overlay final image with public I/O words.
  Their completeness consumer still needs a direct protected-input/shared-memory replacement.
- New `ramImageWord_congr`: agreement of the eight constituent bytes at two possibly different starts implies equality of the packed words.
- New `outputsOf_get?`: each in-capacity extracted output byte is the zero-default byte in shared memory at `output_start + i`.
- New `finalRamWord_output`: for a checked layout and matching initial/final layouts, the final shared word at output index `q` equals the packed eight bytes extracted by `outputsOf` at offset `8*q`.
- `ramPublicIoWord_output`: its `io` parameter changes from `JoltDevice` to `JoltPublicIo`; the existing checked layout, input-size bound and in-capacity word index remain.
  The conclusion still identifies the public output word with the same packed output bytes; all deleted flag-word geometry is removed from its proof.
- Deleted `ramPublicIoWord_panic`, since the public word image no longer contains panic metadata.
- `ramPublicIoWord_trimmed`: both buffer records change from `JoltDevice` to `JoltPublicIo`, and the panic-equality premise is deleted.
  Layout equality, input equality, trailing-zero output equality, the checked layout and the input-size bound still prove equality at every public word.

No new admission, axiom, forbidden decision procedure, resource raise or change under `JoltBytecode/` or `LeanRV64D/` was introduced.
`git diff --check` passes before the next batch.
A full build, the complete harness checks, removal of obsolete modules, public-I/O completeness, whole-run reconstruction, independent checking of the new output assembly, pin-reference cleanup and final commits remain outstanding.

### Shared public-I/O completeness and new RAM claims (pending validation)

Date: 2026-11-24.
Jolt revision remains `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean HEAD is now `8facfa6`.
That commit contains the checked `HaltEndRule`, `Jal`, `Halt` and `Fence` changes.
The preceding `.constraints-repin-prefix-output2.log` build checked `Layer5/Halt`, `Fence`, `MemoryAccessRestriction` (92 seconds each), `Layer1/HaltEndRule` (94 seconds), `ExecutionPrefix` (8.6 seconds) and the halt-based `PrefixState` (18 seconds).
These are module timings in the concurrent integration build, not isolated proof timings.
The build failed before completing the prefix and output assembly.
The local blockers were the reserved identifier `matches` in `SelectedRows.entry_row` and a let-bound overlay rewrite in `ramPublicIoWord_output`.
The next batch repairs those failures and adds the following shared-memory completeness arguments.

The public-I/O proof uses the initialized input bytes, their zero padding, the MMU's existing protected-memory invariant, and final output extraction.
It no longer reconstructs memory from device-owned arrays or assumes a separate device-buffer placement predicate.
The two new RAM-claim proofs are also now written, but not yet checked.
`honestWitness_ramAccessCount` uses the existing four-width memory-row classification and shows that a retired access cannot record zero.
`honestWitness_ramWriteProtected` combines per-row protected-word preservation with the already checked RAM history step.
Neither adds a restriction on the program or the witness.

Statement inventory for this batch:

- `SharedMemoryInitialization.lean`, `zipIdx_fold_get?`: adds a natural-number `start` parameter; the old fixed `RAM_START_ADDRESS` is replaced by that parameter in the inserted and queried addresses.
  The original initializer consumer supplies `RAM_START_ADDRESS`; input initialization supplies its input-region start.
- Private `buffer_insert_get?_above`: its old two premises `start + bytes.size ≤ RAM_START_ADDRESS` and `RAM_START_ADDRESS ≤ a` become the single exact premise `start + bytes.size ≤ a`.
  The conclusion, preservation of byte `a`, is unchanged.
- New `initialMem_input`: successful initialization under a checked layout yields `some (inputs[a - input_start]?.getD 0)` at every address in `[input_start, output_start)`.
- New `initial_state_input_get?`: instance initialization gives the same input-capacity byte equation for `inst.inputs`.
  Both initialization facts are candidates to move into JoltBytecode.
- `Completeness/Helpers/IOSetupFrame.lean`, new `Trace.preState_relation` and `Trace.finalTraceState_relation`: the trace-fold proofs accept relations at the initial preparation and at links, rather than requiring equal projections.
  The former takes transitivity and the first-row relation; the latter also takes reflexivity for the empty trace.
- Existing `Trace.preState_projection_relation` and `Trace.finalTraceState_projection_relation`: signatures unchanged; they instantiate the new shared fold with equality of projections.
- New `HonestTrace.protected_memory`: returns the existing `Mmu.ProtectedMemory` relation from the initial state to every recorded pre-state and the final state.
- New `HonestTrace.final_protected_memory`: the final component of that contract, used for input-byte preservation.
- `Completeness/Helpers/RamOutputProofHelpers.lean`, new `HonestTrace.publicIo`: a `JoltPublicIo` record containing the final layout, the instance's public inputs, outputs extracted from the final shared byte map, and the final panic claim.
- New `overlayRamBytes_at_word`: an overlay remapped to word `first`, over zero, at `first + q` equals the packed buffer bytes starting at `8*q`.
  The old output-packing proof is factored through this helper; the input-packing proof uses it too.
- New `ramPublicIoWord_input`: every in-capacity public input word packs the supplied input bytes with zero defaults.
- New `input_byte_protected`: checked layout construction makes every byte in `[input_start, output_start)` protected, including input padding.
- New `finalRamWord_input`: each final shared input word of an honest trace packs the instance's original input bytes with zero defaults.
- `Completeness/RamOutputEqPublicIo.lean`, `honestWitness_ramOutputEqPublicIo`: replaces the final device parameter in the constraint with `trace.publicIo`, and deletes `adviceBelowInput`.
  The result still proves constraint 26 for the full public interval, now ending at `output_end`.
- `theorems/advice_below_input.lean`, `JoltDevice.AdviceBelowInput`, is deleted with its three fields: relative input alignment and device-owned trusted/untrusted buffer bounds.
  Its redundant `HonestTrace.advice_below_input` consumer in `Completeness/All.lean` is also deleted.
  The ordinary checked-layout placement lemmas remain in `layout_facts.lean` for initialization and existing consumers.
- `MemoryRowExecution.lean`, new `LoadRow.continuation_of_run`: factors the former execution-prefix calculation from `LoadRow.write_of_run` into the successful doubleword-load continuation.
- New `LoadRow.load_of_run`: a retired load has a successful MMU doubleword read at its accessed address.
- `LoadRow.write_of_run`: signature unchanged; consumes the factored continuation instead of repeating its width cases.
- `Completeness/RamAccessCount.lean`, new private `memory_flag_has_address`: a Load-or-Store flag implies an address recording, using the existing memory-row families.
- New `HonestTrace.ram_access_nonzero`: a recorded address of a retired honest memory row is nonzero, since the pinned MMU rejects the first byte at zero.
- New `honestWitness_ramAccessCount`: the honest witness satisfies the fourth RAM read/write claim at every cycle, including padding.
- `Soundness/Layer5/SharedMemoryChecks.lean`, new `ram_word_byte_geometry`: each byte of an aligned witness word rounds to that word and its remapped index.
  `protected_byte_mask_one` retains its signature and now uses this common arithmetic calculation.
- New `mask_one_protected_byte`: under a checked layout and matching execution code interval, C-mask value one implies MMU protection of each of that word's eight bytes.
- `Completeness/RamWriteProtected.lean`, new `honestWitness_ramWriteProtected`: the honest witness satisfies the third RAM read/write claim using the actual code, input, advice and canary mask.
- `Completeness/All.lean`, `honestWitness_constraintEquations`: its result now supplies `trace.publicIo`, its `adviceBelowInput` premise is removed, and its record includes the two new RAM claims.
- `HonestTrace.allConstraints_prover_sizes`: the public I/O parameter changes from the removed device-buffer representation `JoltDevice` to `JoltPublicIo`.
  The remaining hypotheses and `AllConstraints` conclusion are unchanged.
  The transfer from the honest extracted claim to the verifier claim handles panic via the already assumed `claimsRunOutputs`, independently of memory words.

The fresh read-only `output_claim_readback` reviewer is examining the literal new output/claim interfaces with comments and intent withheld.
Its read-back and the separate source comparison remain pending.
The added-line forbidden-token scan, `git diff --check`, and the protected-tree diff check pass before the next build.
No new admission, axiom, forbidden decision procedure or raised resource limit was added.
The obsolete whole-run I/O/device proof files still block the full build, including the store-value and backing-bound migration in `WholeRun/Bundles`.
The next detached batch builds the full root and every currently touched existing Lean target together, including both new RAM claim modules and the two RAM-history completeness results.


### Shared-public build result and whole-run halt migration (pending validation)

Date: 2026-11-24.
Jolt revision: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean HEAD remains `8facfa6`; the changes in this section are uncommitted.
The `.constraints-repin-shared-public3.log` build failed before checking the new public-I/O assembly.
Its failing modules were `MemoryRowExecution`, `IOSetupFrame`, `SelectedRows`, the old `WholeRun/Halt`, and the obsolete `DeviceMemoryObstruction`.
The generic trace-relation proofs and the main protected-memory fold passed elaboration; the wrapper failed because the extension theorem had been declared in a nested namespace.
The next batch fixes that namespace, dependent array rewrites at the entry row, the load-continuation conversion, and the successful-load existential witness.
These fixes are not yet validated.

The new whole-run halt code uses the two-constructor halt-kind classification rather than enumerating the ISA.
I read `specs/halt-end-rule.md`, `rv64.rs` (`rv64_product_constraint_rows`), `cpu.rs` (`Cpu::halt`), and the two halt instruction implementations at the pin.
`JoltISA.execHalt_vreg_run` already supplies the necessary scratch-register execution calculation in JoltBytecode; no bytecode edit or duplicate primitive proof is needed.
Both halt sources preserve shared memory, restore their source address as nextPC, and record the CPU halt marker and panic claim.
The caller therefore no longer asserts equality of the pre-halt and post-halt devices.

Additional statement changes in `theorems/WholeRun/Halt.lean`:

- Deleted `NextIsEbreak`, whose final condition was `row.instruction = .riscv .EBREAK`.
  New `haltSource` maps success to `.jolt .JoltSuccess` and panic to `.riscv .EBREAK`.
  New `NextIsHalt program state kind` retains the nextPC and program-row lookup conditions and requires `row.instruction = haltSource kind`.
- Deleted private `liftSail_readReg`, `jal_vreg_run` and `ebreak_blockInstrs`, which implemented the obsolete self-jump explanation.
  New private `halt_blockInstrs` identifies the single scratch-register success or panic row.
- Replaced `Block.ebreak_post`.
  Old conclusion: `b.post.jolt_device = b.pre.jolt_device` and nextPC equals the source address.
  New `Block.halt_post`, for either explicit source halt, concludes shared-map equality, layout equality, nextPC equal to the source address, `post.halted = some kind`, and `post.jolt_device.panic = (kind == panic)`.
- Private `ebreak_tail` becomes `halt_tail`, preserving memory and layout through a linked chain and recording the selected kind and its panic claim in the last state.
- New `HaltObservation program halt final`: final and halt share memory and layout; either the next source at halt has kind `kind` and final records that kind and claim, or `halt = final`.
- Private `halt_prefix_aux` and public `HonestTrace.halt_prefix`: prefix blocks exclude both halt sources rather than EBREAK alone.
  Old stopping and device clauses were `(NextIsEbreak program halt ∨ halt = final)` and `halt.jolt_device = final.jolt_device`.
  The new clauses are the single `HaltObservation` contract above.
  Execution certificates, chain endpoints and first-row trace certificates remain.
- New `HonestTrace.final_halt`: a completed honest trace and its final-state certificate imply an actual final CPU halt kind and its matching panic claim, including the `halt = final` alternative.
- Replaced `HonestTrace.matches_outputs_halt` with `HonestTrace.matches_outputs_final`.
  Old parameters included arbitrary halt/final states and equality of their devices, and the output projection read `halt.jolt_device.outputs`.
  New parameters are the final state and its back-row certificate; the output projection is `final.jolt_device.outputsOf final.sail.mem` and the final panic equality is retained.
- Deleted unused `HonestTrace.sailRun_halt`; `HaltPrefix.sailRun` is the actual whole-run consumer and chains the same generic block simulation.

Additional statement changes in `theorems/WholeRun/Top.lean`:

- `SailHalted` gains a halt-kind parameter and replaces its EBREAK-only source condition with `row.instruction = haltSource kind`.
  `SailHalted.of_related` transports `NextIsHalt` for that kind through the same PC relation.
- `HaltPrefix.runs` excludes either halt source.
  The former `stop` and `device` fields become `observation : HaltObservation program halt final`.
  `HonestTrace.haltPrefix` packages the changed certificate.
- Deleted `sailOutputs_congr` and `sailPanicWord_congr` with the removed overlay projections.
- `HaltPrefix.sailRun` retains its signature and supplies the non-EBREAK condition from the stronger two-halt exclusion.
- `HonestTrace.sail_reproduces` retains all input hypotheses.
  Its output comparison now reads `halt.jolt_device.outputsOf s.mem` and `final.jolt_device.outputsOf final.sail.mem`.
  The former memory panic-word condition is replaced by an explicit final CPU halt marker and its claim: `∃ kind, final.halted = some kind ∧ final.jolt_device.panic = (kind == panic) ∧ (SailHalted program s kind ∨ halt = final)`.
  The claim is therefore required in both stopping alternatives.
- `JoltInstance.sail_soundness` retains its input hypotheses.
  It compares the same direct shared-memory outputs to the instance outputs and returns the final CPU halt kind with `joltInstance.panic = (kind == panic)` and the corresponding Sail stopping alternative.
  No memory panic-word observation remains in this statement.
  The legacy per-block I/O premises still await the shared-memory simulation replacement; these statements have not yet elaborated.

`DeviceMemoryObstruction.lean` and its sole root import are deleted.
Its concrete layout, device arrays, ignored termination stores/loads and conflicting selected-store example all describe the removed model and have no remaining proof consumer.
This also deletes the two pre-existing executable kernel-decision commands in that module.
The harness's unanchored `decide \+kernel` alternative currently matches those two *deleted* diff lines.
The added-line scan is clean, and no forbidden procedure was added.
A prior clarification about that harness issue is still unresolved; no harness file was changed.

`methods/soundness.md` now records HEAD `8facfa6`, the checked halt consequences, the host-call-only restriction structure, and the unverified integration status.
`Completeness/completeness.lean` drops the stale description of the two fixed RAM-history bugs; the three #1949 obligations remain.
The final whole-run memory simulation, deletion of `Io.lean`/`IoAmo.lean` and legacy flag restriction definitions, global pin-reference cleanup, full build, axiom closure, complete harness check and final logical commits remain open.

The next detached integration build is `.constraints-repin-shared-public4.done` (`.constraints-repin-shared-public4.log`).
It builds `JoltConstraints` together with all 44 existing touched Lean modules, including the new public-I/O and RAM-claim modules.
The build was started under `track-t-build.sh`; its result is pending.
No code from this continuation has been committed before validation.


### Shared-public fourth build and halt read-back

Date: 2026-11-24.
Jolt revision: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean HEAD: `25bf2f1`.
The `.constraints-repin-shared-public4.log` batch failed in six modules: `WholeRun/Halt`, `Layer7/Stopping`, `Layer6/TerminalNextPC`, `Layer5/SharedMemoryChecks`, `Completeness/RamAccessCount`, and `SharedMemoryInitialization`.
It checked the new load-continuation lemmas, selected entry-row proof, protected-memory trace fold, RAM history replay and both RAM-history completeness results.
The protected-memory trace fold and load-continuation changes are committed as `25bf2f1` (`Prove protected-memory trace frames and load continuations`).
Reported module times included `IOSetupFrame` 733 seconds, `TapeDeviceFrame` 525 seconds and `RamHistoryProofHelpers` 324 seconds; these are concurrent module timings rather than isolated proof timings.

The pending fixes normalize dependent array accesses, call namespaced halt and entry lemmas explicitly, unfold the C-mask's local bindings before splitting its conditional, and derive advice placement from the rounded checked layout rather than the smaller requested capacities.
`ordinary_row_next_pc_value` in `Layer7/LastJump.lean` is restored with its baseline type and proof because `Layer6/TerminalNextPC` still calls it.
These fixes have not yet been checked by a subsequent build.

The fresh read-only reviewer `halt_readback5` read comment-stripped halt and whole-run statements without the intended narrative.
It confirmed that both `sail_reproduces` and `sail_soundness` require a final halt marker and the matching panic claim in both stopping alternatives.
It also identified the exact limits of those existing contracts: `SailHalted` says the current Sail PC points to the selected source halt, the fallback allows `halt = final`, and the Sail theorem remains conditional on `BlockConforms` for the reconstructed prefix.
`HaltObservation` alone gives no marker or claim in that equality alternative; the separate `HonestTrace.final_halt` result supplies them to both public callers.
The reviewer did not build or check axioms, source fidelity, or the remaining per-block I/O restrictions.
The inspected SHA256 values were `377d400d7b6754ea0ed138decb5a8b0693d8b2366c30623b281691abe8f6cef4` for `WholeRun/Halt.lean` and `be57777c259052f4192d6f7c06154ddfe44bf6868a4f7a6df72d9ac6a3ee8f07` for `WholeRun/Top.lean`.

The unimported obsolete restriction-definition modules are deleted:

- `Layer5/PanicRestriction.lean`: `TouchesPanic`, `UntrustedAnswerRun.StoresPanicAt`, `JoltInstance.PanicStoresOne` and `JoltInstance.ClaimsNoPanic`.
- `Layer5/TerminationRestriction.lean`: `TouchesTermination`, `UntrustedAnswerRun.StoresTerminationAt`, `JoltInstance.TerminationThenStall`, `termination_next_jal_zero`, `termination_next_no_jalr`, `jal_zero_exec_stalls` and `termination_next_jal_stalls`.

Their old types depended on removed memory flag regions or imposed the three obsolete program restrictions.
They have no remaining imports or soundness callers; the unconverted `DeviceMemory` file still contains textual uses and must be removed with the old I/O simulation.
The new stopping and claim-binding statements are listed above.
The full root build, actual-value store bundle migration and removal of the old I/O simulation remain open.

The added-line forbidden-token scan, generator admission scan, protected-directory diff check and `git diff --check` pass before the next batch.
The next detached batch, `.constraints-repin-shared-public5.done`, builds the root and all 42 currently touched existing Lean modules together.
No successful full build or completed soundness integration is claimed.


### Shared-public fifth build

Date: 2026-11-24.
Jolt revision: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean HEAD: `844cbd6`.
The `.constraints-repin-shared-public5.log` build checked `WholeRun/Halt`, `Completeness/RamAccessCount`, `Layer7/LastJump`, `Layer6/TerminalNextPC` and `Layer6/ExpansionFinish`.
`WholeRun/Halt` is committed as `1fb59ea` (`Track explicit halt kinds in whole-run prefixes`).
The RAM access-count proof is committed as `844cbd6` (`Prove the honest RAM access-count claim`).
Both RAM-history completeness proofs replayed successfully again.
The batch still failed in `Stopping`, `SharedMemoryInitialization`, `SharedMemoryChecks` and `Branch`.

The next changes preserve all four affected declaration types.
`represented_final_panic` now passes the same normalized natural-index runtime-advice term to the halt rewrite as appears in the executed row.
`initialMem_input` explicitly identifies its local start offset before reading the supplied array byte.
`mask_one_protected_byte` no longer attempts to rewrite a lowest-address expression that simplification already removed from its goal.
`branch_target_ne_zero` is restored with its baseline statement and proof in `Layer7/StallSuffix.lean`, next to the existing shared branch classification it uses.
This restores a still-needed caller in `Layer5/Branch` without introducing a duplicate ISA classification.
The previously pruned copy in `LastJump.lean` remains removed.
The new patch still awaits elaboration.

The next detached batch `.constraints-repin-shared-public6.done` builds `JoltConstraints` and all 40 currently touched existing Lean modules.
The added-line forbidden-token scan and whitespace check pass before launch.


### Shared-public sixth build

Date: 2026-11-24.
Jolt revision: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
The `.constraints-repin-shared-public6.log` batch checked `SharedMemoryInitialization`, the public C-mask converse, shared load and store soundness, `Layer6/MemoryRowExecution`, the restored branch target argument, and `WholeRun/Init`, `ImageMemory` and `SystemInv`.
Both RAM-history completeness theorems replayed successfully.
The input initializer and public mask proofs are committed as `7f02ed3` (`Prove input initialization and protected-word mask checks`).
The prefix memory execution lemmas are committed separately as `Use shared-memory agreement for prefix memory steps`.
The root remains red in four modules: `Stopping`, `RamOutputProofHelpers`, `PlainRow`, and the unconverted `WholeRun/Bundles`.

Pending local fixes preserve the affected result types except for the model-driven prepared-entry change listed below.
`represented_final_panic` normalizes the final row's array access before rewriting its panic field.
`ramPublicIoWord_input` uses the current remapping guard, which excludes both zero and below-lowest addresses, and unfolds the same lowest-address definition in its word-index arithmetic.
`finalRamWord_input` unfolds its local layout before the final byte-index arithmetic.
`PlainRow` calls the namespaced halt-terminal lemma explicitly.
`nonterminal_virtual_row_pc_plus_one` is restored with its baseline type and proof because `PlainRow.interior_progress` still uses it.
Its citation names `NEXT_PC_EQ_PC_PLUS_ONE_IF_INLINE` at the current pin.

Statement change: `Layer7/StallSuffix.lean`, `untrusted_prepared_pc`, keeps every parameter and PC conclusion, but its source-boundary entry condition changes from `¬ last.StableStall` to `¬ last.Halts`.
This is the same model change already made in `RawRowEntry`; the proof discards that conjunct and uses only the prepared-state equality.
No additional premise is introduced.
The whole-run store bundle migration still needs the actual stored value for narrow stores, AMOs and store-conditionals, together with the padded backing bounds.
No completed Sail simulation or unrestricted soundness theorem is claimed.

The next detached batch `.constraints-repin-shared-public7.done` builds the full root and all 37 currently touched existing Lean targets together.
The added-line forbidden-token scan, protected-tree diff check and whitespace check pass before launch.


### Shared-public seventh build and value-aware store inversion

Date: 2026-11-24.
Jolt revision: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean HEAD: `2988dbf`.
The `.constraints-repin-shared-public7.log` batch checked `Layer7/Stopping`, including `represented_final_panic` and `soundness_stopping` for either public panic claim.
It also checked `PlainRow`, `BoundaryStart`, `RowStepJalr`, `DivisionDefs`, `DivisionPrograms`, `DivisionLayout`, `TerminalNextPC`, `ExpansionFinish`, `Branch`, `LastJump`, `StallSuffix`, `OutputWords` and the public-I/O helper module.
The public-I/O helper proofs are committed as `2988dbf` (`Derive public I/O words from shared memory`).
Both RAM-history completeness proofs remain checked with their unchanged statements.
The full root still fails, chiefly in the unconverted `WholeRun/Bundles` and `Layer5/DeviceMemory` modules.
The separate I/O simulation has not been removed.

Five local proof repairs preserve their declaration types:

- `Completeness/RamOutputEqPublicIo.lean` unfolds local bindings before splitting the public I/O mask conditional.
- `Completeness/RamWriteProtected.lean` simplifies the conditional mask's nonzero branch with the available hypotheses.
- `Layer6/MemoryRowAppend.lean` normalizes `Array.size_push` when applying the existing RAM image certificate.
- `Layer6/RowStepTerminal.lean` and `Layer6/DivisionAppend.lean` call the namespaced `ConstraintContext.halt_terminal` declaration explicitly.

These repairs await the eighth batch.
`Soundness/soundness.lean` now prints the axiom closure of `JoltInstance.soundness` when that module elaborates.
There is no closure result yet.

New declarations in `WholeRun/StoreRuns.lean` address the actual-value obligation of the remaining store bundles.
They have no old statements and are not yet validated or integrated into `equivAssumptions_of_retire`:

- Private `floorWidth` maps the three narrow widths to the existing memory-row classification.
- Private `floorLoad_write` takes a retiring floor-load run and concludes that its post-state is the original state with v40 set to the shared containing word.
  It uses the existing `LoadRow.write_of_run` argument.
- Private `floorStore_store` takes a retiring floor-store run and recovers its actual doubleword MMU store of v40 to the containing word.
  It uses `StoreRow.store_of_run`.
- `laneStore_store_of_run` takes the width, registers, immediate, starting and final states, source-read certificates, and a retiring `laneStoreProgram` run.
  It returns an intermediate state with the original Sail state, device and code region, together with the successful MMU store of `fusedSpliceValue` applied to the original shared word, stored source and effective address.
  This covers RAM and the I/O window.
  The proof decomposes the existing lane program and reuses `StoreProgramBlocks.fusedSpliceBlock`; it introduces no ISA-wide case split or duplicate splice arithmetic.
- Private `ramStore_guard` recovers `JoltRamStoreOk address pre value 8` from an actual successful RAM doubleword store.
- `laneStore_ram_guard` adds the RAM lower bound to the same narrow-store execution hypotheses and concludes the guard for its actual merged doubleword in the original state.
  Its source-read hypotheses are available from the existing invariant at the intended bundle caller; no premise has been added to a public soundness result.

The primitive lane-store inversion facts are candidates to move into JoltBytecode after validation.
The root imports the new module, so the required full build also checks these declarations.
The source check read `expand_narrow_store` in `crates/jolt-program/src/expand/memory/shared.rs` and `Mmu::store_doubleword`, `trace_store` and `assert_write_protected_store` in `tracer/src/emulator/mmu.rs` at the pin.
Those routines merge the stored lane into the traced containing word and check protected bytes against the old contents.
The remaining AMO and SC bundle obligations still need their actual computed values; they have not been replaced by address-only guards.

`methods/soundness.md` and `documentation/model_review.md` now distinguish the checked halt-end and public-I/O helpers from the pending full assembly.
The model review removes current-assumption claims about the deleted flag restrictions and records the resolved RAM-history bugs.
Historical sections remain labeled by their original revisions.
No new admission, axiom, forbidden decision procedure or resource-limit change was added.

The next detached batch is `.constraints-repin-shared-public8.done` (`.constraints-repin-shared-public8.log`).
It builds `JoltConstraints` and all 37 currently touched existing Lean module targets together, including `StoreRuns` and the final soundness module.
The result is pending.
Remaining work includes the whole-run shared-memory simulation and deletion of its old I/O modules, the final prefix/soundness assembly, pin-reference cleanup, axiom closure, the complete harness check, and the final logical commits.


### Shared-public eighth build and ninth batch

Date: 2026-11-24.
Jolt revision: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean HEAD: `490c182` (`Prove public I/O completeness from shared memory`).
The eighth detached batch failed; its log is `.constraints-repin-shared-public8.log`.
It checked `Completeness/RamOutputEqPublicIo` (126 seconds), `Layer6/MemoryRowAppend` (128 seconds), `RowStepTerminal` (134 seconds), `DivisionAppend` (139 seconds), `DivisionBlock` (19 seconds), and `RowStepMemory` (30 seconds).
The public-I/O equation is now committed as `490c182`.
The equation's changed statement is recorded above: its public record is `trace.publicIo`, and the obsolete `AdviceBelowInput` premise is deleted.
The final soundness module did not elaborate, and no axiom-closure result is available.

The ninth batch repairs the reported `JoltHaltKind` binder inference in `row_kind`, the conditional C-mask proof in `honestWitness_ramWriteProtected`, and the v40 annotation, address normalization and code-region frame application in `StoreRuns`.
Those repairs preserve the affected baseline theorem types.
The new, still-uncommitted `StoreRuns` interfaces are strengthened as described below.

#### Alignment and actual narrow-store values

`MemoryRowExecution.lean` adds `LoadRow.aligned_continuation_of_run`.
It has exactly the existing `LoadRow.continuation_of_run` parameters and run premise.
Its conclusion is the conjunction of `(sourceValue base pre + imm) &&& width.alignMask = 0` and the old shared-load continuation conclusion.
The existing continuation theorem retains its complete type and now selects the second conjunct.
The proof performs only the four cases of the existing memory-width classification.
It reuses the old execution inversion rather than duplicating it.

The uncommitted `StoreRuns.floorLoad_write`, `laneStore_store_of_run` and `laneStore_ram_guard` now also return the alignment equality for the selected narrow width.
The previous draft statements returned only the register shape, store certificate and guard, respectively.
These draft statements had not compiled or been committed.
Their other parameters and conclusions remain as inventoried in the previous section.
The alignment comes from successful execution, with no added hypothesis.

New `StoreRuns.laneStore_bundle_guard` takes a narrow width, source registers, 12-bit immediate, pre/post states, source-read certificates, RAM membership of the enclosing word, and a retiring `laneStoreProgram` run.
It concludes `JoltRamStoreOk` for the enclosing word, the original state, and
`storeDwordValue (match width with | .byte => 1 | .halfword => 2 | .word => 4)`
applied to the effective address, original shared doubleword and stored source value, with checked row width eight.
It uses the execution-derived alignment and the existing `StoreSplice.fusedByteSplice_eq`, `fusedHalfwordSplice_eq` and `fusedWordSplice_eq` proofs.
No splice arithmetic is copied.
This is the actual-value guard required by the pending source-store bundle migration; it is not yet integrated into that factory.
The primitive alignment and narrow-store inversion facts are candidates to move into JoltBytecode after validation.

I re-read `tracer/src/instruction/floor_access.rs` (`load`, line 39; `store`, line 50), `expand_narrow_store` in `crates/jolt-program/src/expand/memory/shared.rs` (line 384), and `Mmu::assert_write_protected_store` (line 747) at the pin.
The floor-load alignment precedes the containing-word read, and the expansion's floor store writes the merged containing doubleword.

#### Block simulation statement changes

In `WholeRun/BlockStep.lean`, both `block_simulates_retire_via` and `block_simulates_retire` remove exactly this old parameter:

```lean
(hdevice : b.post.jolt_device = b.pre.jolt_device)
```

Their remaining parameters and final conclusion are unchanged:

```lean
∀ s, Related b.pre s → ∃ v s',
  try_step 0 false s = .ok v s' ∧ Related b.post s'
```

The meaning of `Related` already changed in the shared-memory relation migration recorded above.
These statements now derive layout preservation directly from `hruns.executes` and `JoltIOSetupFrame.execProgram_setup`.
The new relation compares shared bytes and uses only layout preservation to carry memory presence and layout construction.
It no longer has device input/output arrays to transport.
No replacement premise is added.
`WholeRun/SystemBlocks.block_simulates_via` retains its statement and stops constructing or passing the old equality.
The unused local run certificate constructed solely for that equality is deleted.

`WholeRun/Bundles.joltRun_device_of_ram` is deleted after removal of its sole source consumer.
Its old parameters were `(i : RiscvInstruction)`, `(hi : i.Lifted)`, states `js js'`, `RamAccess i js`, and a successful honest `joltRun` certificate.
Its old conclusion was `js'.jolt_device = js.jolt_device`.
There is no replacement declaration; executed blocks supply the layout fact directly.
The private legacy device-preservation and value-unaware store helpers in `Bundles` remain unconverted and still fail to elaborate.
Their existence is not evidence of a completed store bundle or whole-run simulation.

A fresh blind read-back of the two changed block-simulation interfaces is in progress.
The ninth detached build will check `JoltConstraints` and every currently touched existing Lean module together.
The required final harness has not passed.
Remaining work includes deletion and replacement of the old I/O simulation, actual-value AMO and SC guards, the final soundness assembly, pin-reference cleanup, complete statement inventory, axiom closure and final commits.

The ninth batch is running detached as `.constraints-repin-shared-public9.done`, with output in `.constraints-repin-shared-public9.log`.
It builds the root plus 39 additional touched existing Lean targets, under the shared build wrapper.
Before launch, the added-line forbidden-token scan, `ConstraintGen` admission scan, protected-tree diff check and whitespace check passed.
These static scans do not establish the final build, final soundness closure or clean-tree condition.
The block read-back packet has SHA-256 `1d4008a99799cd9c0e148170e47aff1a95b0e970098b24acf6264028f1b3e8c7` for `BlockStep.lean`, `817a16ffdba56a17ebf08cf8ec26cc7cd8d4c494fc32f6fe40554dd8eda7ccf9` for `Relation.lean`, and `7de1f49e203c3a693e87d425116b5e5deb37b09fde4240b44974478f63ce248e` for `Blocks.lean`.


### Shared-public ninth build and tenth batch (2026-11-24)

Checked Jolt pin: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Checked Lean base: `3522261`; current committed Lean HEAD: `105ffa7`.
The ninth detached batch exited 1 at 10:17:35.
It checked `MemoryRowExecution` (87 seconds), `WholeRun/BlockStep` (90 seconds), `DivisionBlock` (12 seconds), and `RowStepMemory` (21 seconds).
The alignment-aware load inversion is committed as `31ec98f` (`Recover load alignment from successful execution`).
The block simulation derives layout preservation from execution, without its old full-device-equality parameter, at `105ffa7` (`Derive block layout preservation from execution`).
The ninth batch still failed in legacy `WholeRun/Bundles` and `Layer5/DeviceMemory`, and in three local repairs.
The full library, final soundness theorem and soundness axiom closure remain unchecked.

The local failures were a reserved tactic identifier `protected` in `RamWriteProtected`, an untyped second existential binder in `RowStepKinds.row_kind`, and an inline width match in `StoreRuns.laneStore_bundle_guard` that elaborated with dependent proof arguments.
The first two repairs rename the tactic identifier and give the destination binder type `Dst`; neither changes a mathematical statement.
`StoreRuns.narrowStoreBytes : AccessWidth → Nat` now supplies the width mapping byte ↦ 1, halfword ↦ 2, word ↦ 4.
Replacing the inline match by this definition preserves the guard's value and width.
These repairs await the tenth batch.

The fresh block-statement read-back delivered an interim description only.
It identified deletion of `hdevice : b.post.jolt_device = b.pre.jolt_device` as the sole header change in both block simulation theorems, and retained their universal `hinputs` obligation over every related Sail pre-state and PC decomposition.
It also identified the new relation's admitted layout and full zero-default byte agreement.
No final reviewer verdict was received, and this report does not count the interim message as a completed fidelity review.

#### Additional primitive inversion interfaces, pending validation

`MemoryRowExecution.LoadRow.vreg_post_of_run` takes a width-classified load into a writable virtual register, runtime advice, pre/post states and the successful execution certificate.
It concludes that the post-state is exactly `stateAfterVRegWrite pre destination` of the shared doubleword at the accessed address.
It adds no source-read or address guard premise.
Its consumers are the narrow-store load inversion and the doubleword-AMO inversion.

`MemoryRowExecution.ramStore_guard_of_run` takes an address, actual value, pre/post states, an MMU result, RAM membership and successful `Mmu.store_doubleword` execution.
It concludes `JoltRamStoreOk address pre value 8`, including preservation of protected bytes.
This moves the earlier private `StoreRuns` proof into the shared row owner, with the same type; the private duplicate is deleted.
`MemoryRowExecution.ramLoad_guard_of_run` takes an address, pre/post states, an MMU result, RAM membership and successful `Mmu.load_doubleword` execution.
It concludes `JoltRamLoadOk address pre`, using the padded backing end.
The pending atomic inversion uses it.

`MemoryRowExecution.StoreRow.aligned_store_of_run` takes exactly the old `StoreRow.store_of_run` parameters and run premise.
It concludes the conjunction of natural alignment and that old theorem's successful MMU-store certificate.
`StoreRow.store_of_run` keeps its complete old type and selects the second conjunct.
The proof is factored from its existing four-width execution inversion, rather than copied for a new instruction case.
`StoreRuns.nativeStore_ram_guard` uses it for native SD.
That new theorem takes the two source registers, a 12-bit immediate, pre/post states, RAM membership of the containing word, and successful native SD execution.
Its result is `JoltRamStoreOk` at the containing address for the architectural source value, with checked width eight.

The new `WholeRun/AtomicStoreRuns.lean` supplies four interfaces for the pending actual-value bundle migration.
`dwordRmw_ram_guards` takes a writable old-value virtual register, source registers, selected value source, middle-program constructor, tail, binary result function, pre/post states, RAM membership, a pure middle calculation contract, and a successful LD/middle/SD/tail run.
The calculation contract quantifies over a loaded state with unchanged Sail state and the captured old word, and returns a calculated state with unchanged Sail state and a read of the computed result.
The conclusion gives natural doubleword alignment, the RAM load guard, and the RAM store guard for the computed result applied to the source and original shared word.
It derives layout and code preservation from execution of the middle and transfers the actual-value guard to the original memory.
It does not assume the store guard it proves.
`dwordBinop_ram_guards` specializes that interface to the existing ADD/XOR/AND/OR AMO template and its `AmoDwordMiddleStepInto` calculation certificate.
`dwordSelect_ram_guards` specializes it to the signed/unsigned min/max template and its existing `AmoDwordSelectMiddleStepInto` certificate.
`dwordSwap_ram_guards` specializes it to LD/SD/writeback with the architectural source value and its source-read certificate.
All four have the same alignment/load/store conclusion, parameterized by the actual calculated value.
Their named intended consumer remains `WholeRun/Bundles.equivAssumptions_of_retire`; integration into that consumer is still open.
The word-AMO and conditional-store guards are also still open.
These are draft interfaces awaiting elaboration, not a completed whole-run proof.
The primitive load/store inversions are candidates to move into JoltBytecode after validation; no JoltBytecode file was edited.

I read Jolt's `crates/jolt-program/src/expand/memory/scd.rs` (`expand_scd`) and `shared.rs` (`expand_amo_minmax_d`) at the pin.
The conditional store selects its source or previously loaded word before SD and then clears both reservations.
The existing forward SC equivalence theorem already assumes the protected-store guard and cannot be used to derive that same guard.
A separate execution inversion is required; the report does not claim SC is settled.

#### Code-memory frame simplification, pending validation

`WholeRun/CodeInv.store_doubleword_mem` retains its complete statement and now uses the shared `store_doubleword_shape` theorem and the existing insertion-footprint lemma.
The obsolete private `store_raw_mem` and `store_bytes_mem` proofs are deleted.
`CodeInv.mkeeps_execInstr` retains its complete statement and now applies `JoltConstraints.nonstore_memory`.
It uses the existing `StoreRow` width classification to exclude the four store widths, rather than splitting the ISA again.
The separate Sail and Jolt primitive memory-frame proofs and `jolt_keep` tactic, used only by its old proof, are deleted.
The remaining program-frame combinator and its consumers keep their statements.
`CodeIntact.of_related` retains its statement and uses `heap_end_le_ram_backing_end` to carry its existing image bound to the padded presence interval.
`JoltCodeIntact`, `NoCodeStore`, and all public code-invariant theorem types are unchanged by this batch.
This simplification does not yet delete the separate I/O simulation or its old device-memory dependency.

The tenth batch will build `JoltConstraints` plus every touched existing Lean module, including the two new store-inversion modules.
The final harness, complete statement inventory, pin-reference cleanup, soundness axiom closure and clean-tree requirement remain outstanding.

Before the tenth launch, the added-line forbidden-token scan, `ConstraintGen` admission scan, protected-tree diff check and whitespace check passed.
The batch includes the root and 38 additional touched existing Lean modules.
The new owner declarations are at `MemoryRowExecution.lean:473` (`LoadRow.vreg_post_of_run`), `:490` (`ramStore_guard_of_run`), `:507` (`ramLoad_guard_of_run`) and `:549` (`StoreRow.aligned_store_of_run`).
The new source-store declarations are at `WholeRun/StoreRuns.lean:20` (`narrowStoreBytes`), `:159` (`laneStore_bundle_guard`) and `:198` (`nativeStore_ram_guard`).
The doubleword templates are at `WholeRun/AtomicStoreRuns.lean:18` (`dwordRmw_ram_guards`), `:85` (`dwordBinop_ram_guards`), `:118` (`dwordSelect_ram_guards`) and `:150` (`dwordSwap_ram_guards`).


### Shared-public tenth build and eleventh batch (2026-11-24)

Jolt pin remains `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`; committed Lean HEAD remains `105ffa7`.
The tenth batch exited 1 at 10:34:25.
It failed in `MemoryRowExecution` because the new `LoadRow.vreg_post_of_run` binder used ambiguous `VReg`, with both root and Jolt interpretations in scope.
The binder is now explicitly `JoltISA.VReg`.
That owner-module failure prevented compilation of the store inversions and downstream prefix modules; the absence of further errors is not a successful check of those modules.
Its attempted module build took 141 seconds.
The legacy bundle attempt took 142 seconds and still used removed device-frame APIs, under-applied store guards, heap bounds, and the old address-only AMO/SC path.
The next batch addresses those obligations in the bundle types and begins using the actual-value inversion theorems.
It does not claim that the full bundle proof, whole-run simulation or final soundness assembly is complete.

#### Padded-window construction

`theorems/memory_presence.lean:72` adds `ram_backing_end_le_address_space`.
For any device and configuration with `MemoryLayout.new config = some device.memory_layout`, it proves `Mmu.ram_backing_end device ≤ 2^64`.
It uses the existing checked `max_ram_k?` bound and the exact Nat-valued backing-size definition.
Its named consumer is `WholeRun/Bundles.ram_windows`.

`WholeRun/Bundles.ram_windows` keeps its state, address, platform, presence, RAM-membership, AMO-operator parameters and complete `DwordAtomicWindowAssumptions` result.
Its old address premises were `base.toNat < heap_end.toNat` and `base.toNat + 8 ≤ 2^64`.
Its new premises are a checked layout, `base.toNat < Mmu.ram_backing_end device`, and `base &&& 7 = 0`.
It derives `base.toNat + 8 ≤ backing_end` from alignment of the base and checked backing end, and derives the old no-wrap fact from the new address-space theorem.
This supplies every byte of the padded presence interval, including accesses after `heap_end`.
The caller's local `window` construction takes those actual backing and alignment facts.
Ordinary loads/stores use alignment of their containing word, word AMOs use the aligned word base, and doubleword AMOs use execution-derived alignment.
Reservation windows use their existing width-specific alignment fact.
No premise is added to the public `equivAssumptions_of_retire` theorem.

#### Actual-value bundle statement migration, pending compilation

These are private implementation interfaces in `WholeRun/Bundles.lean`, except where explicitly noted.
The old under-applied `JoltRamStoreOk address state` references represented address-only guards before the pin; the new guard type requires its stored value and checked width.
The new statements below supply those arguments, rather than quantifying over arbitrary values or excluding protected addresses.

| Declaration | Old statement component | New statement component |
| --- | --- | --- |
| `storeBundle` | No source width parameter; address-only store guard; default-width store bundle. | Adds `storeWidth : Nat`; requires the guard for `storeDwordValue storeWidth ea original source`, checked row width 8; returns the same-width store bundle. |
| `amoWordBundle` | Address-only guard at `amoWordBase rs1`. | Guard for `amoWordStoreValue op rs1 original rs2`, checked width 8. |
| `amoDwordBundle` | Address-only guard at `rs1`. | Guard for `amoValue op rs2 original`, checked width 8. |
| `ReservationMemory` | Parameters `(store double) rs1 state`; conditional address-only store guard. | Adds `rs2`; conditional guard for `SystemProofs.scStoreValue double state rs1 rs2`, checked width 8; alignment and load fields unchanged. |
| `reservation_conditions` | Returns the previous `ReservationMemory` and device equality. | Its result uses the new `ReservationMemory store double rs1 rs2 state`; device equality component and other parameters remain unchanged pending removal of the legacy path. |
| `reservationWindow` and `reservationReadBundle` | Read-only `ReservationMemory false double rs1 state`. | Same obligation with the unused value-source index fixed to x0. |
| `reservationStoreBundle` | Previous `ReservationMemory true double rs1 state`. | New `ReservationMemory true double rs1 rs2 state`, hence its actual SC value guard. |
| `MemoryConditions` | Stores and both AMO widths required address-only store guards; LR/SC used the old reservation obligation. | Narrow stores use the merged word for widths 1, 2 or 4; SD uses its full value; word AMOs use `amoWordStoreValue`; doubleword AMOs use `DwordAmoCondition`; LR/SC use the new reservation obligation. |
| `loadProgram_ram` | Tail no-store premise; returns load guard and full-device equality. | No condition on the tail; returns the unchanged load guard from its first executed load. |
| `retire_conditions` | Returns old `MemoryConditions` and full-device equality. | Takes `Step.StepInvariant s.sail`, which its sole public caller already proves; returns the actual-value `MemoryConditions`. |

The old full-device equalities in `loadProgram_ram` and `retire_conditions` were internal transport facts for the deleted device-array interpretation of memory.
The shared-memory relation uses preserved layout directly from execution, as already checked in `BlockStep`.
The new memory obligations are stronger actual-value and alignment obligations required by the pinned model.
The result, premises and quantifiers of public `equivAssumptions_of_retire` are unchanged.
Its source-store cases now pass widths 1, 2, 4 and 8 respectively, rather than using the old default width for every case.

New private `sourceStoreCondition` and `wordAmoCondition` name exactly the corresponding merged/computed eight-byte store guards.
New private `DwordAmoCondition` contains both natural doubleword alignment and the guard for `amoValue op source original`, checked width eight.
The existing doubleword-AMO cases obtain both fields from execution.
New private `dword_templates` proves all nine concrete doubleword expansions equal their swap, binop or select templates.
It handles the two existing rd=x0 scratch allocations once for all templates; it does not split the ISA or repeat a separate allocation proof for each operator.
The four binops reuse `amo_dword_*_middle_after_load_into` and the four min/max operations reuse `amo_dword_*_middle_after_load_for`.
The swap case uses the actual architectural source read.
The existing narrow-store cases now call `laneStore_bundle_guard`, and native SD calls `nativeStore_ram_guard`.
These are real consumers of the new inversion interfaces; compilation remains pending.

The duplicate private `mmu_load_ram` is deleted in favor of `MemoryRowExecution.ramLoad_guard_of_run`.
The private `native_store_ram` is deleted after its sole consumer switches to the actual-value native store inversion.
The old `storePlan_ram` path remains for word AMOs and SC only, and still does not elaborate with the new guard type.
Its address-only classification is sufficient for memory footprints but cannot determine the computed stored value.
The old no-store full-device frame is also still pending deletion with its legacy I/O consumers; it is not a valid general frame for halt rows in the pinned model.
The eleventh batch is expected to continue reporting these legacy blockers until word-AMO and SC inversion and the single shared-memory simulation replace them.
No proof is replaced by a gap or new admission.

The full library, final soundness closure, old I/O-module deletion, word-AMO and SC inversion, remaining pin references, final statement audit and clean committed tree remain open.

Before the eleventh batch, the added-line forbidden-token scan, `ConstraintGen` admission scan, protected-tree diff check and whitespace check passed.
The root and all 39 additional touched existing Lean targets are launched together as `.constraints-repin-shared-public11.done`.


### Shared-public eleventh build and twelfth batch (2026-11-24)

Jolt pin remains `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`; committed Lean HEAD remains `105ffa7`.
The eleventh batch exited 1 at 10:43:45.
Its only reported failure was kernel recursion in `theorems/memory_presence.lean` at the new `ram_backing_end_le_address_space` proof.
The attempted module build took 92 seconds.
That prerequisite failure prevented checking its downstream users, including the pending store inversions, bundle migration and final soundness assembly.

The public backing-end theorem keeps its complete statement.
Its proof now instantiates two private lemmas over arbitrary natural numbers instead of running arithmetic after substituting concrete 64-bit bounds.
`backing_end_le_arithmetic` proves `base + (lowest + 8 * words - base) ≤ bound` from `base ≤ bound` and `lowest + 8 * words ≤ bound`.
`backing_end_le_option` proves the same inequality for the optional RAM-domain representation from `domain = some words` and those same bounds.
These helpers serve the public backing-end bound and introduce no public premise or new admission.
No resource limit changes.

The twelfth batch checks the root and every touched existing Lean module together.
All previously listed whole-run, word-AMO, SC, pin-reference, final closure and committed-tree obligations remain open.
The static checks and exact launch target count below describe this batch; they do not establish compilation.

Before the twelfth launch, the added-line forbidden-token scan, `ConstraintGen` admission scan, protected-tree diff check and whitespace check passed.
The batch includes `JoltConstraints` and all 39 additional touched existing Lean targets.
The completion file is `.constraints-repin-shared-public12.done`.


### Shared-public twelfth build and thirteenth batch (2026-11-24)

Jolt pin remains `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
The twelfth build exited 1 at 11:45:20.
It checked `memory_presence` (86 seconds), `MemoryRowExecution` (189 seconds), both requested RAM-history completeness modules (151 and 230 seconds), `Completeness.RamWriteProtected` (268 seconds), and the soundness row dispatcher (49 seconds).
These are whole-module elapsed times, not individual proof timings.
The primitive owner and bound changes are committed as `613a113` (`Derive shared load shapes and actual RAM store guards`).

`WholeRun/StoreRuns.nativeStore_ram_guard` failed because an implicit instruction argument could not determine the dependent runtime-advice type for `()`.
The proof now names `instruction` explicitly in the no-advice equality.
The two analogous applications in `AtomicStoreRuns.dwordRmw_ram_guards` now name their load/store constructors explicitly as well.
Their statements are unchanged.
`Completeness.All` failed to parse the multiline record update before its remaining layout-dependent fields.
The update now puts every field on its own line; the theorem statement is unchanged.
The old `Layer5.DeviceMemory` also failed on removed fields and retired predicates; that obsolete simulation has not been repaired or retained as a compatibility API.
It remains pending replacement and deletion with the two I/O modules.

#### Common word-lane inversion and its consumers, pending compilation

`WholeRun/AtomicStoreRuns.lean` adds the following contracts, each with a real consumer.
These are execution facts under the pinned model, rather than new assumptions on an instance or witness.

| Declaration | Added statement and consumers |
| --- | --- |
| `wordLaneMerge_continue` | For distinct writable doubleword/lane temporaries, known old word and lane mask, and the replacement read after clearing, reduces the merge program with any tail to its store row on `amoWordLaneMergeState`; used by `wordLaneMerge_ram_guard` and the existing I/O AMO calculation. |
| `wordLaneMerge_ram_guard` | Given those same register-calculation facts, RAM membership and a retiring merge with any continuation, derives `JoltRamStoreOk` for its actual `amoWordLaneMerged` value at width eight; used by `wordRmw_ram_guard`. |
| `wordRmw_ram_guard` | Given a source read, RAM membership, the existing `AmoWordWindowStep` calculation contract and a retiring window, derives word alignment and the actual merged-value store guard on the original shared memory; used by the binop and swap guard theorems. |
| `wordLaneValue_eq_storeValue` | Word alignment and equality of the calculated result's low word with `amoWordSailResult` imply equality between the executed lane merge and `amoWordStoreValue`; used by the binop and swap guard theorems. |
| `wordTemplates` | Jointly equates generated ADD/XOR/AND/OR/swap word expansions with the existing common templates, handling the two x0 scratch allocations once; used by `Bundles.retire_conditions` and the five existing I/O AMO callers. |
| `wordBinop_ram_guard` | The existing binop middle-row certificate, its low-word identity, RAM membership and the executed word-binop template imply the actual `amoWordStoreValue` guard at width eight; used by the four corresponding source cases. |
| `wordSwap_ram_guard` | Source reads, RAM membership and a retiring swap window imply the `amoWordStoreValue .AMOSWAP` guard at width eight; used by the source swap case. |

The new scratch-register facts instantiate `AtomicFamily.amo_word_register_writable` and `amo_word_register_ne`.
They do not repeat allocator case splits per operator.
`IoAmo` now calls the common merge reduction and joint template identity; its duplicate pure merge calculations and five separate expansion-identity proofs are removed.
All existing public theorem types in `IoAmo` remain unchanged at this intermediate checkpoint.
The four binops and swap in `Bundles.retire_conditions` now supply their actual-value `MemoryConditions` through these shared inversions.
No new premise is added to public `equivAssumptions_of_retire`.
The four word min/max operations and SC remain on the old path; the final shared-memory simulation is still open.

I read the pinned expander implementations in `crates/jolt-program/src/expand/memory/amoswapw.rs` (`expand_amoswapw`) and `shared.rs` (`LaneWindow::merge`, lines 149–162; `expand_amo_w`, lines 293–321).
They load the containing doubleword, calculate/extract the lane, clear it, shift the replacement, add it, store the merged word, and write back the old word last.
The new inversion follows that order and checks the actual store; it does not infer an arbitrary-value protected-store guard from an address alone.
These primitive/template facts are candidates to move into JoltBytecode; no protected-tree files were changed.
The thirteenth batch checks the root and every touched existing Lean target together.
Compilation of these new contracts and their downstream consumers is pending.

Before the thirteenth launch, the added-line and new-file forbidden-token scans, `ConstraintGen` admission scan, protected-tree diff check and whitespace check passed.
The batch includes `JoltConstraints` and all 38 additional touched existing Lean targets.
The completion file is `.constraints-repin-shared-public13.done`.


### Shared-public thirteenth build and fourteenth batch (2026-11-24)

Jolt pin remains `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
The thirteenth build exited 1 at 11:59:56.
It checked `WholeRun.StoreRuns` (130 seconds), `Completeness.All` (130 seconds) and `Completeness.completeness` (156 seconds).
These are whole-module elapsed times, not individual proof timings.
The completeness assembly and protected-write completeness proof are committed as `78ed82d` (`Assemble completeness for shared memory and halt claims`).
The source-store execution inversions are committed as `621fcd1` (`Derive actual-value guards for retiring source stores`).
The assembly still depends on the three unchanged #1949 admissions; compilation does not discharge them.

The thirteenth batch reported two local goals in `Soundness/TopLevel.lean` and elaboration failures in `WholeRun/AtomicStoreRuns.lean`.
The old `Layer5/DeviceMemory` also failed on the removed device fields; its replacement and deletion remain open.
The pending atomic prerequisite prevented checking `Bundles`, `CodeInv` and their downstream whole-run users.

`TopLevel.soundness_reconstruct_trace` (line 34) keeps its full statement.
Its proof now extracts nonzero entry and the checked code region from `context.validInputs`, then rewrites source extents using `expand_program_source_extents`.
Those existing context facts discharge the new bytecode-admission guards; no new hypothesis is introduced.
`TopLevel.soundness_prover_accepts` (line 126) also keeps its statement.
Its proof now supplies the explicit nonempty-array form of the existing terminal-halt certificate to the simplified prover guard.

The atomic proofs now expose `EStateM.run` or `Program.Run` at the points where continuation equalities are rewritten, normalize the zero immediate after reducing the memory width, and read virtual registers through `readVReg_run`.
The merge continuation names its concrete three pure rows rather than relying on private lane-source projections to rewrite.
Scratch-register equalities are proved at the named old/doubleword/lane registers before those state updates are simplified.
Architectural reads use `readSrc_xreg_run_of_read`, which preserves the complete current Jolt state when lifting a Sail read.
These are proof repairs; the existing public theorem types are unchanged.
The new dword calculation contract uses explicit `.run` equalities, definitionally equal to its previous function applications.
No new admission or resource-limit change was introduced.

#### Word min/max inversion and removed duplicate calculations

I read `crates/jolt-program/src/expand/memory/shared.rs` (`expand_amo_minmax_w`, lines 328–388) at the pinned Jolt checkout.
Jolt allocates containing-word, lane, old-word, source and take-source temporaries in that order.
It sign-extends the source, compares in the order selected by min/max, computes SUB/MUL/ADD, merges the lane, and writes back the old word last.
The new shared inversion uses that exact order, including sign extension before unsigned comparison.

| Declaration in `WholeRun/AtomicStoreRuns.lean` | New statement and consumers |
| --- | --- |
| `wordSelectTemplates`, line 402 | Jointly equates the four generated min/max word expansions with `amoWordWindowProgram` using `amoWordSelectLaneMiddle` for SLT/SLTU and forward/reverse comparison; used by the four source cases in `Bundles.retire_conditions` and the four existing I/O AMO callers. |
| `wordSelect_result`, line 429 | For Boolean signed/unsigned and min/max choices, selecting between the two equally sign-extended operands gives the corresponding `amoWordSailResult` low word; used by those source cases and existing I/O callers. |
| `wordSelect_ram_guard`, line 448 | The existing comparison-row certificate, low-word selection identity, source reads, RAM membership and a retiring word-select template imply `JoltRamStoreOk` for the actual `amoWordStoreValue` at width eight; used by all four source min/max cases. |

The four `Bundles.retire_conditions` min/max branches now invoke the common actual-value inversion instead of `StorePlan`.
The existing public `equivAssumptions_of_retire` statement is unchanged.
`IoAmo` uses the joint template and result identities instead of four separate allocator case splits and four repeated low-word calculations.
Its public theorem statements are unchanged at this checkpoint; the obsolete I/O simulation itself still awaits deletion.
These new primitive/template facts are candidates to move into JoltBytecode.
No file under the two protected trees was changed.
The next build checks these repairs, the soundness assembly and every remaining touched Lean target together with `JoltConstraints`.

Before the fourteenth launch, the added-line and new-file forbidden-token scans, `ConstraintGen` admission scan, protected-tree diff check and whitespace check passed.
The batch includes `JoltConstraints` and all 33 additional touched existing Lean targets.
The completion file is `.constraints-repin-shared-public14.done`.


### Shared-public fourteenth build and fifteenth batch (2026-11-24)

Jolt pin remains `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`; committed Lean HEAD remains `621fcd1`.
The fourteenth build exited 1 at 12:11:33.
`Soundness.TopLevel` and `WholeRun.AtomicStoreRuns` each ran for 99 seconds before failing.
The obsolete `Layer5.DeviceMemory` ran for 100 seconds and again failed on the removed device fields.
These are module timings; no new individual proof timing is available.
No final soundness closure or whole-run result was checked.

The remaining `soundness_reconstruct_trace` goal was the proposition-valued entry-address guard after all bytecode and code-region checks had been discharged.
Its proof now unfolds `guard` when simplifying with the existing nonzero-entry fact.
The prover-acceptance proof produced no error in the fourteenth batch, but its enclosing module still failed.
Both public statements are unchanged.

The atomic repairs use explicitly typed zero-immediate equalities and equality transport for the address-domain proposition instead of asking `rw` to infer the bit width from a polymorphic zero.
The merge address read now invokes `readSrc_xreg_run_of_read` directly.
The word-select result function is explicitly typed `BitVec 32 → BitVec 64`, fixing the unassigned sign-extension input width.
These are proof changes only.
The fourteenth batch did not report errors in the joint word-select template and low-word selection identities, but the atomic module as a whole did not compile.

#### Conditional doubleword store inversion, pending compilation

I read `crates/jolt-program/src/expand/memory/scd.rs` (`expand_scd`) and `shared.rs` (`expand_sc_success`, lines 13–24) at the pinned checkout.
The expansion checks lower RAM, compares rs1 with the doubleword reservation register, loads the old word, computes the reservation-dependent replacement through SUB/MUL/ADD, stores it, clears both reservation registers, and writes the status.
A failed reservation stores the loaded old word; its protection check must use that value.

| Declaration | New statement or changed private interface |
| --- | --- |
| `AtomicStoreRuns.dwordRmw_ram_guards_of_loaded`, line 20 | The retiring doubleword RMW template supplies alignment, a load guard and the actual-value store guard when its middle calculation is proved on `loaded = stateAfterVRegWrite pre old word`; this exact loaded-state equation preserves other scratch-register facts needed by SC.D. |
| `AtomicStoreRuns.dwordRmw_ram_guards`, line 86 | The previous full statement is retained as a corollary: its middle contract uses only Sail equality and the loaded old-register value; existing AMO consumers are unchanged. |
| `ConditionalStoreRuns.scdTemplate`, line 16 | Equates the generated SC.D program with its shared RAM-check, comparison, load, selector, store, clear and status fragments; used by the SC.D inversion. |
| `ConditionalStoreRuns.scd_ram_guard`, line 40 | Source reads, lower-RAM membership and a retiring generated SC.D imply `JoltRamStoreOk` at width eight for `SystemProofs.scStoreValue true pre address source`; used by the source SC.D bundle branch. |
| `Bundles.reservation_store_plan` | Old: classified `scRows double` for both widths. New: classifies only `scRows false`, its sole remaining SC.W consumer; SC.D no longer uses the address-only plan. |
| `Bundles.reservation_conditions` | Old: returned `ReservationMemory store double ... ∧ t.jolt_device = s.jolt_device`. New: takes the caller's existing `Step.StepInvariant s.sail` and returns only `ReservationMemory store double ...`; the unused full-device frame and its LR proofs are deleted, and the doubleword-store branch uses the actual-value SC.D guard. |

The public `equivAssumptions_of_retire` statement remains unchanged.
The existing caller already supplies the step invariant; it is not a new premise on the exported simulation theorem.
The doubleword inversion is factored once, rather than duplicating the load/store inversion for conditional stores.
The new execution/template facts are candidates to move into JoltBytecode.
The two protected source trees are unchanged.
SC.W inversion, the second I/O simulation's replacement/deletion, remaining pin references, the full build, final statement audit and the final clean committed tree remain open.
The next batch checks the root and all remaining touched Lean targets together.

Before the fifteenth launch, the added-line and new-file forbidden-token scans, `ConstraintGen` admission scan, protected-tree diff check and whitespace check passed.
The batch includes `JoltConstraints` and all 34 additional touched existing Lean targets.
The completion file is `.constraints-repin-shared-public15.done`.


### Shared-public fifteenth build and sixteenth batch (2026-11-24)

Jolt pin remains `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`; committed Lean HEAD remains `621fcd1`.
The fifteenth build exited 1 at 12:20:24.
It reported two local proof errors before the legacy device-memory failure: `TopLevel.soundness_reconstruct_trace`'s zero literal did not match the 64-bit guard, and `dwordRmw_ram_guards_of_loaded` used the source-value equality in the wrong direction.
Both proofs now use the explicit expected type/orientation.
Their statements are unchanged.
No final soundness closure or whole-run result was checked by that run.

I re-read `crates/jolt-program/src/expand/memory/scw.rs`, `scd.rs`, and `shared.rs` (`expand_sc_success`, lines 13–24) at the pin.
SC.W saves its success bit in v32, loads/sign-extends the old word, selects and spills the replacement to v33, reopens the containing word for SW's merge, writes status, and clears the reservations.
The pending inversion follows those fragments and obtains the second opening's guard from the first actual load, whose shared memory is unchanged by the intervening calculation.

| Declaration | Statement or change |
| --- | --- |
| `AtomicStoreRuns.wordOpen_conditions` | New: a retiring AMO word-opening row with lower-RAM membership supplies four-byte alignment, `JoltRamLoadOk` and the successful canonical shared doubleword read; used by both word-AMO and SC.W inversion. |
| `ConditionalStoreRuns.scScratch_reserved` | New: the three allocated SC scratch registers are distinct from both persistent reservation registers; used by both widths' common prefix and SC.W calculation. |
| `ConditionalStoreRuns.scPrefix_continue` | New: source read, lower-RAM membership and scratch/reservation disjointness imply the common RAM-check/comparison prefix continues with the computed equality bit, for an arbitrary continuation. |
| `ConditionalStoreRuns.scTemplates` | New: joint generated-program identities for both SC widths, proved with one allocator classification; used by the two projection identities. |
| `ConditionalStoreRuns.scdTemplate` | Keeps its full statement; its proof is the doubleword projection of `scTemplates`. |
| `ConditionalStoreRuns.scwTemplate` | New: the word projection identifies the generated SC.W prefix, first load, selection, spill, reopen, merge, status and clear fragments. |
| `ConditionalStoreRuns.scwWindow_continue` | New: source reads, alignment, the checked canonical old-word load and the saved success bit imply the pure calculation/reopening fragments continue from a state with the old containing word, lane mask and selected source; used by `scw_ram_guard`. |
| `ConditionalStoreRuns.scw_ram_guard` | New: source reads, lower-RAM membership and a retiring generated SC.W imply the actual-value `JoltRamStoreOk` for `scStoreValue false`, width eight; used by `Bundles.reservation_conditions`. |
| `Bundles.reservation_store_plan` | Restores the original two-width classification because `CodeInv.sc_mem` needs both SC footprints; it is no longer used to infer store legality from an address alone. |
| `Bundles.reservation_conditions` | Keeps its pending fifteenth-batch interface, and its word branch now invokes `scw_ram_guard`; both widths use the actual reservation-dependent value. |
| `Bundles.mmu_store_ram`, `store_body_ram`, `store_row_ram`, `storePlan_ram` | Deleted: their address-only `JoltRamStoreOk` conclusions omit the pinned value-preservation guard and have no remaining consumer. |
| `Bundles.noStoreRow_device`, `noStoreProgram_device` | Deleted: absence of a store does not preserve the full device when a row halts. |
| `Bundles.ScratchProgram`, `scratchProgram_frozen` | New: a program containing only the existing `ScratchRow` class preserves architectural registers and the full device; used by the two existing AMO middle-calculation consumers. |
| `Bundles.addi_device` | New: ADDI preserves the device for any source/destination; used by the two AMO writeback consumers. |
| `IoAmo.io_amo_dword`, `io_amo_word` | Private middle-classification premise changes from `NoStoreProgram` to `ScratchProgram`; the concrete middle programs satisfy it, and the exported block theorem types do not change. |
| `IoAmo.io_amo_dword_binop`, `io_amo_word_binop`, `io_amo_dword_select`, `io_amo_word_select` | Private row-classification premise changes from arbitrary-destination `NoStoreRow` to virtual-destination `ScratchRow`; every supplied arithmetic/comparison constructor satisfies it. |

The new execution and allocation facts are candidates to move into JoltBytecode.
The sixteenth batch will check them and all remaining touched targets together with `JoltConstraints`.
The separate I/O modules, their removed-field references, final pin-citation audit, final statement inventory, root build, axiom closure and clean committed tree remain open.
The methods document now labels its old November 5 pin section as historical, avoiding a second contradictory current-pin declaration.

Before the sixteenth launch, added-line/new-file forbidden-token scans, the generator admission scan, the protected-tree diff check and the whitespace check passed.
The batch includes the root and all 34 remaining touched existing Lean targets.
The completion file is `.constraints-repin-shared-public16.done`.


### Shared-public sixteenth build and seventeenth batch (2026-11-24)

Jolt pin remains `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`; committed Lean HEAD remains `621fcd1`.
The sixteenth build exited 1 at 12:33:23.
`Soundness.TopLevel`, `WholeRun.AtomicStoreRuns` and the old `Layer5.DeviceMemory` each ran for about 93 seconds before failing.
These are whole-module times, not individual proof measurements.
No soundness axiom closure was printed.
The conditional-store prerequisite did not compile because the atomic module failed first.

The entry guard diagnostic now exposes a mismatch between the numeral zero and the explicit `0#64` bitvector literal.
The proof uses the explicit equality `(0 : BitVec 64) = 0#64`, proved by reflexivity, when simplifying the existing valid-input guard.
The new word-opening inversion exposed a mismatch between `~~~7` and `-8`, the masks used by `MemoryWidth.accessed` and `amoWordBase`.
It now explicitly normalizes those masks in the canonical-load equality.
Both repairs preserve the complete theorem statements.
The earlier actual-value equality-orientation repair produced no error in this build, although its module as a whole failed.

#### Shared Sail platform and memory pipeline

The old `WholeRun/Io.lean` contains useful Sail permission and pipeline facts as well as the obsolete duplicated device simulation.
The valid Sail facts now form `WholeRun/PlatformMemory.lean`, with no device arrays, flag-word predicates or device-memory relation.
This is a source refactor: the moved theorem bodies and hypotheses are unchanged.
`Bundles` uses its range arithmetic for RAM PMA selection, the remaining ordinary memory simulation opens its namespace, and the atomic simulation calls its declarations directly.
The new module depends on `Relation`, the fixed hart configuration and the existing bytecode memory libraries; it has no dependency on the pending AMO/SC bundle layer.
No compatibility forwarding declarations were retained in the old I/O module.
The old simulation modules still require replacement and deletion; extracting their reusable Sail facts does not complete that migration.

| Old declaration/file | New declaration/file and statement status |
| --- | --- |
| `Bundles.range_subset_nat` | `WholeRun.PlatformMemory.range_subset_nat`: same wrapping-range comparison and nonwrap hypotheses; now public for both region checks. |
| `Io.mod_of_and`, `mod_of_and1`, `mod_of_and3`, `mod_of_and7` | Same mask-to-divisibility statements in `WholeRun.PlatformMemory`. |
| `Io.aligned_paddr` | Same divisibility-to-Sail-alignment statement in `WholeRun.PlatformMemory`. |
| `Io.io_matching`, `io_checks`, `not_mmio_io` | Same platform PMA/PMP and MMIO-exclusion statements in `WholeRun.PlatformMemory`; they describe Sail's ordinary I/O region without a Jolt device copy. |
| `Io.mem_read_of_plain`, `mem_write_value_of_plain` | Same physical plain-memory reduction statements in `WholeRun.PlatformMemory`, parameterized by permission, MMIO and actual read/write evidence. |
| `Io.byte_of_dword_eq`, `append_bytes` | Same pure byte-packing statements in `WholeRun.PlatformMemory`. |
| `Io.vmem_read_addr_of_mem_read`, `vmem_read_of_mem_read`, `execute_LOAD_of_mem_read` | Same width-generic virtual-memory and source-load reduction statements in `WholeRun.PlatformMemory`. |

All these declarations retain their old quantified types after the namespace change; only their visibility changes from private to public.
The new module adds documentation for the shared range comparison and retains the existing concrete examples on the other declarations.
Its ordinary and atomic consumers have been updated without introducing new hypotheses on exported source simulation theorems.
The next build checks this refactor, the normalization fixes, both conditional-store inversions and every remaining touched target together with the root.

Before the seventeenth launch, added-line/new-file forbidden-token scans, the generator admission scan, the protected-tree diff check and the whitespace check passed.
The batch includes the root and all 36 remaining touched existing Lean targets.
The completion file is `.constraints-repin-shared-public17.done`.


### Shared-public seventeenth build and eighteenth batch (2026-11-24)

Jolt pin: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
The seventeenth build checked the working tree based on Lean HEAD `621fcd1` and exited 1 at 12:41:43.
It checked `Soundness.TopLevel`, `WholeRun.AtomicStoreRuns`, `WholeRun.PlatformMemory` and `Soundness.soundness`.
The first three modules took about 92–93 seconds each and the final soundness module about 56 seconds; these are module times, not individual proof timings.
`#print axioms JoltInstance.soundness` printed exactly `[propext, Classical.choice, Quot.sound]`.
The soundness theorem therefore has no admission or extra axiom in its checked closure.
The root still failed in the new conditional-store inversion and the legacy device-memory simulation.
No whole-run simulation result is claimed.

The checked source groups are now committed locally:

- `86d4cfa`: actual-value guard inversion for doubleword and word atomic expansions.
- `b852fe3`: shared-memory prefix reconstruction, explicit halt-end soundness for both panic claims, deletion of the old three restrictions and termination-store proof layer.
- `b118458`: reusable Sail region checks, byte packing and plain-memory pipeline facts, separated from the obsolete device overlay.

The conditional-store repairs retain every statement up to definitional equality.
They use explicit 7-, 12- and 64-bit literals matching the existing bytecode execution certificates, expose scratch-register aliases before continuation rewriting, and close the joint program-template projection equalities by reflexivity.
They add no premise, resource override or decision-procedure use.

#### Store pipeline and shared bytes

The valid Sail store pipeline and byte-splice equations move from `Io.lean` into `WholeRun/PlatformStore.lean` in the existing `WholeRun.PlatformMemory` namespace.
The ordinary simulation imports this module, and atomic consumers refer directly to its declarations.
No forwarding declarations remain at the old locations.
The old second I/O representation is still present pending its consumers' migration; this extraction alone does not remove it.

| Declaration | Old and new statement |
| --- | --- |
| `toNat_and_neg8` | Same floor-to-eight identity; private in `Io` becomes public in `PlatformMemory`. |
| `vmem_write_of_addr`, `execute_STORE_dword_of_write` | Same source-address and successful-write pipeline statements; namespace/visibility move only. |
| `io_write_checks` | Same aligned access and platform-register hypotheses, same PMP and MMIO conclusions; namespace/visibility move only. |
| `sail_store_b`, `sail_store_h`, `sail_store_w`, `sail_store_d` | Same source operands, region/alignment/permission hypotheses and exact Sail post-state equalities; namespace/visibility move only. |
| `SailStore`, `sailStore_byte`, `sailStore_halfword`, `sailStore_word`, `sailStore_dword` | Same register equality and per-address byte-update relation, and its four canonical store instances; namespace/visibility move only. |
| `lowHalf_byte`, `lowWord_byte`, `fusedSplice_byte_b`, `fusedSplice_byte_h`, `fusedSplice_byte_w` | Same extraction and narrow-store splice equations; namespace/visibility move only. |
| `SailStore.agrees_with_doubleword` | New: a direct lane store and a containing-doubleword rewrite have equal zero-default bytes at every address, given the containing-word base, lane fit, old shared bytes and replacement-byte equations. |
| `SailStore.preserves_present` | New: every address present before a plain store is still present afterwards. |
| `shared_store_finish` | New caller of those two facts: a successful actual Jolt doubleword store and a Sail lane store with the same splice preserve the device, agree on registers and every shared byte, and retain allocated-byte presence. |

These are generic shared-map facts; their statements do not mention device arrays, panic words or termination words.
The last theorem is intended to replace the old store-finish obligation already consumed by ordinary and atomic source simulations.
The new store module and SC repairs await the eighteenth build.

#### Independent blind read-back of main soundness

A fresh read-only reviewer stripped comments/docstrings and read only the Lean theorem and its recursively relevant definitions, without the Jolt checkout, methods documents or author reports.
The reviewer recorded HEAD `621fcd1fdfa1ce461596604fb5c789c086795acf` with the working-tree theorem closure later committed at `b852fe3`.
The theorem file SHA-256 was `d7947c54fd5ae6fbd67e132294d16837fef9be9cfff584b0ae1e1432db708d7f`, and `Soundness.TopLevel` was `c72f4d475e244bdd4cab04a291e7894b618a6dfa79e82e7de0f8c97431814e63`.
The environment was Lean `v4.35.0`, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Sail `1e5b216bf881ef08da160db63b44ecda430802d6`.
The reviewer ran no builds and made no changes.

The literal read-back agrees with the intended deterministic modeled-equation claim:
for any field with characteristic above `2^128 - 2^64`, instance satisfying `RamRegionFits` and universal `HostCallsSucceed`, and witness satisfying `AllConstraints`, the instance has an honest nonempty expanded-bytecode trace ending at its first success/panic halt, matching normalized output bytes and the public panic Boolean, with an accepted prover configuration and passing spoil assertions.
The existential private inputs may differ from the supplied private inputs.
`TemporaryRestrictions` has exactly the one host-call field.
Both panic claims are admitted by the conclusion.
The read-back also confirms the existing scope boundaries: the theorem follows supplied structured source instructions and does not equate them with decoding `memory_init`; the whole-run layer supplies that separate bridge.
The result concerns finite modeled equations, not a cryptographic verifier or PCS security.
It does not require the reconstructed trace's prover dimensions to equal the supplied witness dimensions, and does not impose `ProverChunkConfig` beyond the actual `WitnessParams`/context fields.
Outputs are observed after trimming trailing zeros.
The reviewer found no syntactic contradiction in the assumptions, and did not claim a source-fidelity or proof-completion verdict.
The pin comparison and build/axiom evidence remain the integrator's separate obligations.

Before the eighteenth launch, added-line/new-file forbidden-token scans, the generator admission scan, the protected-tree diff check and the whitespace check passed.
The batch includes the root and all 8 remaining touched existing or new Lean targets.
The completion file is `.constraints-repin-shared-public18.done`.


### Shared-public eighteenth build and nineteenth batch (2026-11-24)

Jolt pin: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean HEAD: `b118458`; the working tree contains the changes below.
The eighteenth build exited 1 at 12:53:15.
It checked `WholeRun/PlatformStore` in about 75 seconds and replayed the three-standard-axiom closure of `JoltInstance.soundness`.
It failed in the obsolete device-memory module and conditional-store elaboration.
No whole-run theorem is claimed as checked by that build.

#### Shared-memory source simulations

The old I/O modules are deleted, together with `Layer5/DeviceMemory` and the now-dead `WholeRun/LoadAddress` workaround.
The replacement source modules are `WholeRun/SharedMemorySim.lean` for ordinary loads/stores and `WholeRun/AtomicMemorySim.lean` for word/doubleword AMOs.
The remaining code in those modules proves Sail pipeline and shared-map execution facts.
No compatibility aliases or forwarding declarations retain the old duplicated I/O relation.
The root and all imports, including private-name references, now use these module names.

I re-read the bytecode MMU shared-map operations and Jolt's pinned `tracer/src/emulator/mmu.rs` load/store paths.
Jolt's tracer checks mapped addresses before reads and stores, reads input/output/gap bytes from its memory backing, and permits protected stores only when their bytes are preserved.
A successful Jolt store changes Sail's memory; it does not preserve the complete Sail state.
The new simulation retains the register frame and compares its actual shared-byte update with Sail's lane store.

| Declaration or group | Old statement | New statement |
| --- | --- | --- |
| `MemRel` | Allocation/layout plus duplicated I/O-byte agreement, panic-word agreement and output-array sizing. | Deleted; `MemoryReady` contains allocation and checked layout only. |
| `Related.memRel` and `MemRel.of_mem_eq` | Construct/transport the duplicated relation. | `Related.memoryReady` and `MemoryReady.of_mem_eq` construct/transport allocation and layout from shared-memory equality. |
| `IoGeo` and `IoGeo.of_layout` | Bundle input/output/panic/termination geometry for the device overlay. | Deleted; `MemoryGeometry` and its constructor contain only `0x40000000 ≤ memLow` and eight-alignment of `memLow`. |
| `NoFlagWordLoad`, `PanicStoreNonzero`, `AmoNoFlagWord` | Exclude loads/stores/atomics touching device flag words, or restrict a panic-word value. | Deleted, with all ordinary/atomic/decode/whole-run premises that referenced them. |
| `NoLowLoad`, `NoZeroDoublewordLoad` and `Block.FirstRowAt.noLowLoad` | Require or derive an address lower bound from prover sizing plus exclusion of recorded address zero. | Deleted; `read_lower` derives `memLow ≤ A` from the actual checked first-byte read and checked layout. |
| `io_dword_eq` | Requires the device-memory relation and flag-word exclusion to identify the loaded word. | Requires allocation/layout, alignment, lower/upper address bounds and the actual eight-byte read; compares the direct shared map. |
| `load_access`, `store_access`, `access_congr`, `amo_access_congr` | Transport classifications together with flag/lower-bound or value restrictions. | Supply/transport only the actual address classification; no flag predicates. |
| `narrow_load_outcome`, `ld_outcome`, `narrow_load_core`, `ld_core` | Receive an independent `memLow` lower bound and device-overlay relation. | Derive the lower bound from execution and use allocation/layout only. |
| `store_effect`, `outputsAfter`, `memoryReady_of_store`, `outputsAfter_eq` and all output/panic/termination overlay byte helpers | Analyze device array updates and synthetic flag words. | Deleted; actual stores are compared directly through `shared_store_finish`. |
| `store_finish` | Compares output-array updates and flag-word cases, and returns the old duplicated relation. | A real Jolt doubleword store plus Sail's matching lane store imply register preservation, device preservation, agreement of every shared byte, and `MemoryReady`. |
| `SailStore.agrees_with_doubleword`, `shared_store_finish` | Eighteenth-batch drafts required all eight old bytes. | Require old-byte agreement only outside the overwritten lane; a full-word store needs no old-byte premise. |
| `systemProject_of_store` | Assumes the complete Sail state is unchanged. | Assumes only its register map and projected virtual registers are preserved; concludes equality of projected register maps. |
| `amo_store_low` | Excludes flag words and concludes the complete Sail state is unchanged. | Derives the mapped lower bound and concludes virtual-register preservation and the actual `state_after_dword_store` effect. |
| `systemProject_regs_after_write` | No previous declaration. | Architectural writeback commutes with register projection under projected-vreg preservation even when memory has changed. |
| `io_amo_dword`, `io_amo_word`, `IoAmoCtx`, `IoAmoEffect`, `io_amo_conv`, `io_amo_core` | Flag-word exclusions, duplicated relation and byte agreement only above RAM. | No flag exclusions; allocation/layout and byte agreement at every address; writeback follows the actual shared store. |
| `io_core`, `block_simulates_io_via`, `block_simulates_io` | Ordinary flag-word, panic-value and lower-bound restrictions; duplicated I/O postcondition. | No such restrictions; direct shared-byte agreement and allocation/layout. |
| `block_simulates_io_amo_via`, `block_simulates_io_amo` | Atomic flag-word exclusion and duplicated I/O postcondition. | No flag exclusion; direct shared-byte agreement and allocation/layout. |
| `block_simulates_decoded`, `block_simulates_image` | Receive ordinary flag/lower-bound/panic-value premises and, for the image theorem, an atomic flag exclusion. | Those premises are removed; simulation still concludes the full `Related` relation. |
| `BlockConforms` | Source classification, code preservation, flag-load exclusion, zero-doubleword-load exclusion, nonzero panic store and atomic flag exclusion. | Source classification and code preservation only. |
| `BlockConforms.simulates` | Additionally takes a separately derived `NoLowLoad` condition. | No separate load-address condition; all memory guards follow from successful execution. |
| `JoltInstance.TracerAddressChecks`, `LoadRow.address_checks`, `StoreRow.address_checks` | Temporary execution-prefix restriction and its two restriction-dependent consumers. | Deleted; selected-row proofs already use `SharedMemoryChecks` derived from the pinned constraints. |

The pure Sail and splice declarations moved into `PlatformMemory` and `PlatformStore` retain their types as recorded in the preceding tables.
The source simulation wrappers for particular load widths and AMO operators retain their operation/result equations and inherit the context changes listed above.
The changed postconditions compare every zero-default shared byte, including the I/O region, instead of reconstructing a second window from device arrays.

#### Conditional-store proof repairs

The SC template proof now supplies its remaining nested conjunction of definitional identities explicitly.
The SC.W continuation keeps a typed `spillRun`, exposes the scratch-register aliases before rewriting, and explicitly identifies the second word-opening program.
The SC.D callback and SC.W reservation-bit equation close by definitional equality after their register reductions.
`wordOpen_prefix_conditions` factors first-row inversion over an arbitrary word-window continuation; its caller is `scw_ram_guard`.
This helper states the alignment, RAM read guard and exact shared loaded word already needed by that caller.
Neither exported SC guard nor the bundle-construction theorem gains a premise or changes its result.
No resource limit was raised to address the earlier timeout.

Before the nineteenth launch, added-line/new-file forbidden-token scans, the generator admission scan, the removed-restriction scan, the protected-tree diff check and the whitespace check passed.
The detached command builds `JoltConstraints` and all 12 remaining touched existing/new module targets under the shared build wrapper.
Its completion file is `.constraints-repin-shared-public19.done` and output is `.constraints-repin-shared-public19.log`.
The full build and clean-tree checks remain pending.


### Shared-public nineteenth build and twentieth batch (2026-11-24)

Jolt pin: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
The nineteenth build checked the working tree based on Lean HEAD `b118458` and exited 1 at 13:15:42.
The only failed prerequisite was `ConditionalStoreRuns.scw_ram_guard`, which reached the default heartbeat limit during reduction.
The rest of that file, including SC.D and the SC.W continuation and first-row inversion, produced no errors.
`PlatformStore` and `MemoryAccessRestriction` checked in about 89 seconds each, and the complete affected soundness and completeness assemblies rebuilt.
`JoltInstance.soundness` again printed exactly `[propext, Classical.choice, Quot.sound]`.
The ordinary and atomic shared-memory simulation modules remained blocked behind the SC prerequisite.

The checked shared-store pipeline is committed locally as `0fca98c` (`Compare Sail lane stores with shared doubleword updates`).
The checked removal of `JoltInstance.TracerAddressChecks` and its two dead consumers is committed as `3bb089d` (`Remove the unused tracer address restriction`).
The `DoublewordAddressChecks` predicate remains because `SharedMemoryChecks.memory_row_address_checks` proves it from the constraints; it is no longer an assumption.
The prefix's `NextStep` definition remains because host-call success uses that execution boundary.

The SC.W proof now names the repeated open/select/spill/reopen fragment `scwWindowRows`.
`scwTemplate` and `scwWindow_continue` replace that expanded expression by this definition, with no change up to definitional equality.
The new private `scwWindow_ram_guard` takes an arbitrary window-entry state, its actual source reads, the saved reservation-equality bit, a RAM lower bound, and its retiring window/merge run.
It concludes the guard for the actual selected and merged containing word, then transports it through the existing setup-frame theorem.
The exported `scw_ram_guard` executes only the RAM-check/reservation prefix and saved-bit copy before calling this helper and transporting the same guard back to the original state.
This extraction avoids reducing the nested prefix state throughout the window proof.
No public SC hypothesis or conclusion changed, and no resource limit was raised.

A citation audit found 227 distinct source paths and 713 path references in Lean comments, with old explicit pin labels in 147 Lean files.
Most cited current paths exist; three stale path spellings/configuration references and line-location mappings still require correction against the pinned checkout.
No citation update is claimed merely from replacing a commit label.
The source-reference audit and final declaration/line inventory remain pending.

Before the twentieth launch, added-line/new-file forbidden-token scans, the generator admission scan, removed-restriction scan, protected-tree diff check and whitespace check passed.
The detached command builds the root and all 8 remaining touched existing/new module targets through the shared wrapper.
Its completion file is `.constraints-repin-shared-public20.done` and log is `.constraints-repin-shared-public20.log`.
The full-root check, final whole-run validation, remaining commits and clean-tree condition are still pending.


### Shared-public twentieth build and twenty-first batch (2026-11-24)

Jolt pin: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
Lean HEAD: `3bb089d` with the working-tree migration described above.
The twentieth batch exited 1 at 13:19:17.
The SC.W window guard extraction produced no error; the only failed declaration was the outer `scw_ram_guard`, again exceeding the default reduction budget.
The final soundness axiom report remained exactly `[propext, Classical.choice, Quot.sound]`.

The new `scwPrefixState` names the state after the RAM check, reservation comparison and saved-bit copy.
The new `scwPrefix_continue` executes those rows before an arbitrary continuation.
The exported guard now calls that prefix theorem, obtains the saved-bit equation, and applies the checked window guard.
All new definitions and lemmas are consumed by that exported guard.
Temporary `trace` checkpoints identify entry, bound, template, prefix and guard milestones if reduction still times out; they do not add assumptions or change checking limits and will be removed before the final commit.
The public guard's statement is unchanged.

The twenty-first detached command builds the root and all 8 remaining touched module targets through the shared build wrapper.
Before launch, added-line/new-file forbidden-token scans, the generator admission scan, protected-tree diff and whitespace checks passed.
Its completion file is `.constraints-repin-shared-public21.done`, with output in `.constraints-repin-shared-public21.log`.

#### Pinned citation audit and remaining host-call model boundary

The numeric-citation audit read the old pinned files and the current `ff6fc6568` files and compared their line sequences.
Of 238 plain numeric Rust citations, 232 have exact unchanged endpoint anchors at one of the stated historical revisions.
The remaining citations concern the changed ECALL expansion, changed SC.W expansion, BEQ's macro-based instruction declaration and the changed HostIO handlers.
The two stale `jolt-trace` preprocessing paths must become their current `jolt-program` paths, and `instructions/b/beq.rs` becomes `instructions/i/beq.rs`.
The `sail-import/rv64d_jolt.json` references describe the local Sail model configuration, not a file in Jolt's Rust checkout.
The anchor audit is evidence for locating citations, not an independent semantic proof.

The current Jolt tracer has changed host-call failure behavior beyond the memory and halt changes covered by this re-pin.
At `tracer/src/emulator/cpu.rs:1118` (`handle_jolt_cycle_marker`) it logs and ignores unknown marker events, restarts duplicate markers, and ignores unmatched end markers.
At line 1166 (`handle_jolt_print`) it logs and ignores invalid print event types, unreadable messages and stdout failures.
`tracer/src/emulator/host_io.rs` (`read_host_bytes`, lines 51–87) checks pointer addition and address limits before reading, reserves fallibly, and rejects unreadable ranges.
`VirtualHostIO::exec` dispatches these handlers in `tracer/src/instruction/virtual_host_io.rs:19–38`.

The frozen JoltBytecode model's `JoltISA/HostIO.lean:43–78` still throws on unknown cycle-marker or print events and makes pointer overflow conditional on `overflowChecks`.
The initialized soundness run disables that overflow flag.
The surviving `HostCallsSucceed` restriction therefore marks a limitation of the frozen execution model; it should not be described as a known invalid-event panic in Jolt at this pin.
Invalid-event success in Jolt and the tracer's checked/fallible host reads are not fully modeled by that frozen layer.
No change under `JoltBytecode/` is made, no extra assumption is added, and this report does not claim unrestricted Rust HostIO fidelity.
The checked Lean soundness result continues to concern the modeled instruction execution under its explicit host-call restriction.
The three removed flag-word restrictions and the removed tracer-address restriction do not depend on this separate HostIO limitation.


### Citation relocation working tree (2026-11-24)

The citation pass changes comments only in 194 Lean files.
It pins GitHub source links to `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`, corrects the old `jolt-trace` preprocessing path and the BEQ instruction path, and updates explicit current-pin labels.
Unchanged source-line anchors are relocated by matching lines in the cited old revisions against the pinned checkout; changed ECALL, SC.W, BEQ and HostIO locations were read separately.
Relocation counts: 274 exact anchors, 6 reviewed changed items, 89 pinned URLs, 14 named/path citation instead of stale lines.
Where an old anchor could not be established, its stale numeric range was removed while retaining a pinned source-file/item citation:

- `common/src/jolt_device.rs`, old location `491-493`.
- `crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs`, old location `662-668`.
- `crates/jolt-claims/src/protocols/jolt/geometry/bytecode.rs`, old location `668-670`.
- `crates/jolt-claims/src/protocols/jolt/geometry/claim_reductions/hamming_weight.rs`, old location `82-90`.
- `crates/jolt-claims/src/protocols/jolt/relations/ram/output_check.rs`, old location `115-128`.
- `crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs`, old location `135-154`.
- `crates/jolt-claims/src/protocols/jolt/relations/registers/val_evaluation.rs`, old location `69-79`.
- `crates/jolt-verifier/src/stages/stage5/instruction_read_raf.rs`, old location `181-201`.

No proof statement or body changes in this citation pass.


### Shared-public twenty-first build and twenty-second batch (2026-11-24)

Jolt pin: `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
The twenty-first build checked the working tree based on `3bb089d` and exited 1 at 13:23:04.
The SC.W window guard produced no diagnostic.
The remaining errors were the copied reservation bit's named-state normalization, the saved reservation-bit equation, and reduction at the final guard transport in `ConditionalStoreRuns.scw_ram_guard`.
Temporary trace checkpoints showed that execution inversion had already obtained the window guard before this final reduction failed.
The soundness axiom closure remained exactly `[propext, Classical.choice, Quot.sound]`.

The twenty-second batch makes the copied-register post-state explicit, closes the saved-bit equation by definitional equality, and supplies source-register and shared-memory equalities before normalizing the final guard.
This changes proof normalization only; the exported SC.W guard's hypotheses and conclusion remain unchanged.
No checking limit was raised.
The temporary diagnostic traces still need removal after the declaration checks.

The citation relocation is committed locally as `cea7d6c` (`Update Jolt source citations to ff6fc6568`).
The commit changes comments in 194 Lean files.
A comparison that strips nested Lean comments while preserving string literals verified that the staged code matched its parent in every changed file.
This establishes that the citation commit changes no Lean declaration or proof body.

Before launch, the added-line/new-file forbidden-token scan, generator admission scan, removed-restriction scan, protected-tree diff and whitespace checks passed.
The twenty-second detached command builds `JoltConstraints` and all 8 remaining touched existing/new module targets through the shared build wrapper.
Its completion file is `.constraints-repin-shared-public22.done`, with output in `.constraints-repin-shared-public22.log`.
The shared-memory simulations and their whole-run callers remain unchecked behind the conditional-store prerequisite.
The root build, final statement inventory, exact harness checks, remaining logical commits and clean-tree condition remain open.
