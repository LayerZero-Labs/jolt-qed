# Step 5: completeness about Jolt's prover

Date: 2026-11-03.
The recorded Jolt pin is `5def437f21a0006e13c063a03f0b5a7c9b93cd6f`; the code cited here was read at the migration target `c6703570588e88033b8722bd4dec47c7f46f3b16` with `git show c6703570:<path>`.
The Lean base is `e299498` on branch `migration/completeness-prover`, in the worktree `/Users/ari.biswas/Lean/jolt-qed-completeness`.
The diff is uncommitted.
It follows `methods/constraints-migration-step5.md`.

## Summary

`JoltInstance.completeness` now says that the honest witness at the sizes Jolt's prover picks satisfies `AllConstraints`.
The old existential statement is kept, unchanged, as `JoltInstance.completeness_someWitness` and is proved from the new theorem by unpacking `InLanguage`.
Every corrected-size helper was adapted to Jolt's sizes; none was deleted without its content moving into an adapted lemma, as listed below.
The one known-false fact, that Jolt's RAM table holds the highest touched word, is the single new `sorry` lemma `HonestTrace.prover_config_holds_highest_slot`.
The verifier's RAM bounds at Jolt's sizes, `HonestTrace.witness_params_ram_bounds`, are now proved in full, including that both bounds compute, so its old `sorry` is gone.
There are still six completeness `sorry` bodies: (01), (08), (11), (37), (38) and the new #1951 item 4 lemma.
No other blocker was found.

## Statement changes

The two main statements are exactly the approved ones; no Lean adjustment was needed.

- `JoltInstance.completeness` (`JoltConstraints/Completeness/completeness.lean:81`) now takes `privateInputs`, `trace`, `claimsRunOutputs`, `spoilAssertsPass`, `config` and `proverAccepts : trace.prover_config joltInstance = some config`, and concludes `AllConstraints joltInstance privateInputs (HonestTrace.honestWitness (F := F) (trace.witness_params config proverAccepts) trace)`.
- `JoltInstance.completeness_someWitness` (`completeness.lean:106`) has the old statement of `JoltInstance.completeness` (base line 69) word for word.

`InLanguage`, `CompletenessAssumptions`, the restrictions, `Trace.prover_config` and every constraint definition are unchanged.
No public theorem gained a premise.
Helper hypotheses changed only as follows, and each caller proves them from premises it already has:

- Every adapted helper takes `proverAccepts : trace.prover_config joltInstance = some config` where it took `accepted : trace.corrected_prover_config = some config`, and speaks of `trace.witness_params config proverAccepts` where it spoke of `trace.corrected_witness_params config accepted`.
- `remap_address_lt` became `remap_address_le` (`JoltConstraints/witness_params.lean:62`): generalized over a bound, from `address < 2^64 → index < 2^61` to `address ≤ bound → index ≤ (bound - lowest) / 8`.
- `min_bytecode_address_lt` (`witness_params.lean:74`): generalized from the bound `2^64` to any positive `bound` above every image address (new hypotheses `positive`, `allBelow`).
- `program_image_len_words_le` (`witness_params.lean:91`): generalized from `program_image_len_words ≤ 2^61 + 2` to `min_bytecode_address / 8 + program_image_len_words ≤ (bound + 9) / 8 + 1` for any positive `bound` above every image address; the old statement is the instance `bound = 2^64`.
- `HonestTrace.floor_load_properties` (`JoltConstraints/Completeness/Helpers/RamReadSelection.lean:173`) and `HonestTrace.floor_store_properties` (`RamReadSelection.lean:216`) each gained a third conclusion: a recorded address at or above `RAM_START_ADDRESS` is below the row's `heap_end`.
  Their six `.2` uses in `ramValues_zero_at_zero` became `.2.1`.

## The known-false lemma

`HonestTrace.prover_config_holds_highest_slot` (`JoltConstraints/prover_config_facts.lean:256`) states, for an honest trace and Jolt's config, `trace.highest_ram_slot < config.ram_K`; its body is `sorry`.
`Trace.highest_ram_slot` (`prover_config_facts.lean:203`) is the largest word index `(address - lowest) / 8` over the run's nonzero RAM addresses, the `touched` that Jolt's prover rounds (`crates/jolt-prover/src/config.rs`, `ProverConfig::derive_from_dimensions`).
Its docstring explains the failure: `K = pow2(max(h, imageEnd))` is `h` itself when `h` is a power of two at least the image's end, for example `h = 1024` gives `K = 1024`, which holds indices `0` to `1023`, and it links a16z/jolt#1951 item 4.
The only use is `HonestTrace.prover_config_ram_fits` (`prover_config_facts.lean:273`), which turns it into the per-address bound behind `HonestTrace.witness_params_ram_fits` (`JoltConstraints/witness_domain.lean:102`), the `RamFits` premise of every honest-witness equation.
It is the Jolt-size version of the old `slot_below_ram_K` (base `trace_facts.lean:149`): at Jolt's formula that arithmetic lemma, `slot ≤ touched → slot < pow2(max(touched, imageEnd))`, is false at `slot = touched`, so it became this lemma, stated for the highest slot of an honest trace.

## RAM bounds at Jolt's sizes

The step's expectation holds: Jolt's RAM size is at most the verifier's maximum `pow2(⌊(heap_end - lowest) / 8⌋)`.
Both numbers Jolt's prover rounds are at most `⌊(heap_end - lowest) / 8⌋`.
The highest touched word is, because Jolt's tracer asserts that every access in RAM starts below `heap_end` (`tracer/src/emulator/mmu.rs`, `assert_effective_address`), and every other access lies below `RAM_START_ADDRESS`.
The image's end is, because `heap_end` lies at least `STACK_CANARY_SIZE = 128` bytes past `program_end` (`common/src/jolt_device.rs`, `MemoryLayout::try_new`).
Both bounds compute: the minimum's image start and end are the ones Jolt's prover already computed, the lowest address is at most `RAM_START_ADDRESS`, and the rounding is at most Jolt's RAM size, which Jolt's prover checked fits 64 bits.
The minimum's lower-half proof carried over.
No new premise was needed; `imageNonempty` was already a premise.

## Declarations

Lines are in the working tree; base lines are at `e299498`.
Every new or changed declaration has a docstring with a concrete example.

| Declaration | File and line | Change, with base name and line |
|---|---|---|
| `HonestTrace.prover_config_trace_length` | `JoltConstraints/prover_config_facts.lean:160` | adapted from `HonestTrace.corrected_prover_config_trace_length` (`trace_facts.lean:116`) and the length part of `HonestTrace.corrected_prover_config_isSome` (`prover_config_facts.lean:157`) |
| `HonestTrace.prover_config_last_jump` | `prover_config_facts.lean:176` | adapted from `HonestTrace.corrected_prover_config_last_jump` (`trace_facts.lean:137`); the proof is the last-jump part of `corrected_prover_config_isSome` |
| `Trace.highest_ram_slot` | `prover_config_facts.lean:203` | new helper definition |
| `HonestTrace.prover_config_ram_K` | `prover_config_facts.lean:216` | new: Jolt's RAM size, unfolded from `ProverConfig.checkedRamSize` |
| `HonestTrace.prover_config_holds_highest_slot` | `prover_config_facts.lean:256` | new `sorry`, adapted from `slot_below_ram_K` (`trace_facts.lean:149`) |
| `HonestTrace.prover_config_ram_fits` | `prover_config_facts.lean:273` | adapted from `HonestTrace.corrected_prover_config_ram_fits` (`trace_facts.lean:158`) |
| `HonestTrace.prover_config_ram_K_ge_two` | `prover_config_facts.lean:306` | adapted from `HonestTrace.corrected_prover_config_ram_K_ge_two` (`trace_facts.lean:209`) |
| `HonestTrace.prover_config_log_trace_length_lt` | `JoltConstraints/witness_params.lean:17` | adapted from `HonestTrace.corrected_prover_config_log_trace_length_lt` (`witness_params.lean:12`) |
| `remap_address_le` | `witness_params.lean:62` | generalized from `remap_address_lt` (`witness_params.lean:53`) |
| `min_bytecode_address_lt` | `witness_params.lean:74` | generalized (base line 63) |
| `program_image_len_words_le` | `witness_params.lean:91` | generalized (base line 73) |
| `HonestTrace.prover_config_log_ram_K_lt` | `witness_params.lean:112` | adapted from `HonestTrace.corrected_prover_config_log_ram_K_lt` (`witness_params.lean:90`); Jolt's prover checks the 64-bit bound, so the proof reads it from `prover_config_ram_K` |
| `HonestTrace.witness_params` | `witness_params.lean:149` | adapted from `HonestTrace.corrected_witness_params` (`witness_params.lean:145`) |
| `HonestTrace.witness_params_chunk_config` | `witness_params.lean:184` | adapted from `..._chunk_config` (base line 177) |
| `HonestTrace.witness_params_trace_length` | `witness_params.lean:233` | adapted (base line 224) |
| `HonestTrace.witness_params_padded` | `witness_params.lean:248` | adapted (base line 235) |
| `HonestTrace.witness_params_bytecode_domain` | `witness_params.lean:261` | adapted (base line 247) |
| `HonestTrace.witness_params_ram_chunks_pos` | `witness_params.lean:280` | adapted (base line 264) |
| `HonestTrace.prover_config_ram_K_pow` | `JoltConstraints/witness_domain.lean:76` | adapted from `HonestTrace.corrected_prover_config_ram_K_pow` (base line 72) |
| `HonestTrace.witness_params_ram_size` | `witness_domain.lean:86` | new: `ramSize = config.ram_K`, shared by three proofs |
| `HonestTrace.witness_params_ram_fits` | `witness_domain.lean:102` | adapted from `HonestTrace.corrected_witness_params_ram_fits` (base line 90) |
| `HonestTrace.prover_config_ram_K_of_nonempty` | `JoltConstraints/Completeness/Helpers/VerifierSizes.lean:57` | new: the RAM size with the image start computed, shared by three proofs |
| `HonestTrace.witness_params_ram_minimum_of_nonempty` | `VerifierSizes.lean:99` | adapted from `HonestTrace.corrected_witness_params_ram_minimum_of_nonempty` (base line 48) |
| `new_heap_end_ge` | `VerifierSizes.lean:149` | new layout fact |
| `HonestTrace.program_end_below_heap_end` | `VerifierSizes.lean:188` | new |
| `HonestTrace.lowest_address_le_ram_start` | `VerifierSizes.lean:210` | new |
| `HonestTrace.highest_ram_slot_le_heap_end` | `VerifierSizes.lean:228` | new |
| `HonestTrace.verifier_ram_minimum_computes` | `VerifierSizes.lean:260` | new |
| `HonestTrace.witness_params_ram_maximum` | `VerifierSizes.lean:322` | new |
| `HonestTrace.witness_params_ram_bounds` | `VerifierSizes.lean:374` | adapted from `HonestTrace.corrected_witness_params_ram_bounds` (base line 119); `sorry` replaced by a proof |
| `HonestTrace.witness_params_one_hot_fits_setup` | `VerifierSizes.lean:402` | adapted (base line 132) |
| `bind_ok_first` | `JoltConstraints/Completeness/Helpers/RamReadSelection.lean:85` | new |
| `JoltISA.Mmu.load_doubleword_below_heap_end` | `RamReadSelection.lean:100` | new |
| `JoltISA.Mmu.store_doubleword_below_heap_end` | `RamReadSelection.lean:121` | new |
| `execInstr_load_access` | `RamReadSelection.lean:140` | new |
| `execInstr_store_access` | `RamReadSelection.lean:155` | new |
| `HonestTrace.floor_load_properties` | `RamReadSelection.lean:173` | conclusion extended (base line 86) |
| `HonestTrace.floor_store_properties` | `RamReadSelection.lean:216` | conclusion extended (base line 121) |
| `HonestTrace.ram_address_below_heap_end` | `RamReadSelection.lean:329` | new |
| `ramValues_zero_at_zero` | `RamReadSelection.lean:436` | proof only: `.2` to `.2.1` |
| `HonestTrace.allConstraints_prover_sizes` | `JoltConstraints/Completeness/All.lean:187` | adapted from `HonestTrace.allConstraints_corrected_sizes` (base line 182) |
| `honestWitness_constraintEquations` | `All.lean:15` | one comment reworded |
| `HonestTrace.entry_lt_bytecode_domain` | `JoltConstraints/Completeness/completeness.lean:42` | adapted (base line 40) |
| `JoltInstance.completeness` | `completeness.lean:81` | restated, proved from `allConstraints_prover_sizes` |
| `JoltInstance.completeness_someWitness` | `completeness.lean:106` | new, the old statement |

`HonestTrace.corrected_prover_config_isSome` (base `prover_config_facts.lean:157`) related Jolt's acceptance to the corrected policy's.
At Jolt's sizes no such bridge is needed, so its three parts are now `prover_config_trace_length`, `prover_config_last_jump` and the unchanged private `HonestTrace.prover_config_addresses_ok` (`prover_config_facts.lean:139`).
Because those Jolt-acceptance facts need `prover_config.lean`, which imports `trace_facts.lean`, the five adapted lemmas from `trace_facts.lean` moved to `prover_config_facts.lean`.
`prover_config_facts.lean` no longer imports `witness_params.lean`, and `witness_params.lean` now imports `prover_config_facts.lean`.
The unchanged helpers `max?_getD_lt`, `min?_getD_lt`, `TraceRow.ram_address_lt`, `HonestTrace.log_bytecode_size_lt`, `clog_succ_eq_log2_succ`, `padded_trace_length_eq_prover`, `padded_trace_length_spec`, `guard_some`, `program_image_len_words_pos`, `min_bytecode_address_ge_ram_start` and `VerifierSizes.chunks_fit_dorySetupLogN` are still used.

Comment and docstring changes only: `HonestTrace.corrected_prover_config` and `remap_address` (`JoltConstraints/honest_trace.lean:294`, `:265`), `Trace.prover_config` (`JoltConstraints/prover_config.lean:129`) and `honestWitness_instructionRaEqChunkProduct` (`JoltConstraints/Completeness/InstructionRaEqChunkProduct.lean:77`).
Documentation changes: `JoltConstraints/model_review.md` (introduction, #1951 item 4 row, the "Jolt's prover accepts the trace" assumption row, "Proofs owed" and the migration note), `JoltConstraints/constraints.md` (status lines and migration item 11), `methods/constraint_proving.md` (one rule) and this report.

## Build results

Every Lake invocation was preceded by `pgrep -fl lake`; the only other Lake process was the soundness agent's build in `/Users/ari.biswas/Lean/jolt-qed-public`.
Builds ran serially in this worktree.
Logs are in `/Users/ari.biswas/Lean/scratch-step5`.

| Log | Command | Exit | Wall time | Result |
|---|---|---:|---:|---|
| `baseline` | `lake build JoltConstraints.Completeness.completeness` | 0 | 4.9s | base `e299498` cached |
| `b1` | `lake build JoltConstraints.prover_config_facts` | 0 | 20.0s | passed |
| `b2` | `lake build JoltConstraints.witness_domain` | 0 | 14.1s | passed |
| `b3` | `lake build JoltConstraints.Completeness.completeness` | 0 | 3:46 | top-down shape, new theorem's body `sorry` |
| `b4` | `lake build JoltConstraints.Completeness.completeness` | 0 | 8.7s | new theorem proved |
| `b5` | `lake build JoltConstraints.Completeness.Helpers.RamReadSelection` | 1 | 12.9s | failed during development |
| `b6` | `lake build JoltConstraints.Completeness.Helpers.RamReadSelection` | 0 | 13.7s | passed |
| `b7`, `b8` | `lake build JoltConstraints.Completeness.Helpers.VerifierSizes` | 1 | 6.4s each | failed during development |
| `b9` | `lake build JoltConstraints.Completeness.Helpers.VerifierSizes` | 0 | 6.6s | RAM bounds proved |
| `b10` | `lake build JoltConstraints.Completeness.completeness` | 0 | 22:51 | full rebuild after the `honest_trace.lean` comment change, alongside the soundness agent's build |
| `b11` | `lake build JoltConstraints.Completeness.Helpers.VerifierSizes` | 0 | 7.9s | after extracting `prover_config_ram_K_of_nonempty` |
| `b12` | `lake build JoltConstraints.Completeness.completeness` | 0 | 14.5s | final |
| `axioms` | `lake env lean /Users/ari.biswas/Lean/scratch-step5/Axioms.lean` | 0 | 6.8s | below |
| `b13` | `lake build JoltConstraints.Completeness` | 0 | 2.9s | final |

`git diff --check` passes.
A source search outside `Soundness/` finds exactly six `sorry` bodies: (01) `RamAddrEqRs1PlusImmMinusLookupIfLoadStore.lean:41`, (08) `RightLookupAdd.lean:58`, (11) `RightLookupEqRightInputOtherwise.lean:57`, (37) `RamValEqInitialPlusPrefixRamInc.lean:27`, (38) `RamValFinalEqInitialPlusRamInc.lean:30`, and `prover_config_facts.lean:261`.
No `native_decide`, `decide +kernel` or `bv_decide` was added, and no heartbeat limit was changed; the two existing limits in `LookupWriteProofHelpers.lean` and `TracePCProofHelpers.lean` are untouched.
The soundness library was not built; no soundness file was edited, and no soundness file uses a renamed or changed declaration.

## Axioms

- `JoltInstance.completeness`: `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`.
- `JoltInstance.completeness_someWitness`: `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`.
- `HonestTrace.witness_params_ram_bounds`: `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.

## Timing

Lean's trace profiler at a 500 ms threshold reports no new or adapted declaration above 0.5 seconds in `prover_config_facts.lean`, `trace_facts.lean`, `witness_params.lean`, `witness_domain.lean`, `VerifierSizes.lean`, `All.lean`, `completeness.lean` or `RamReadSelection.lean`.
`RamReadSelection.lean` takes 12.1 seconds standalone with `-Dprofiler=true`, 3.4 of them importing, as in Step 2 (11.9 seconds); its slowest proof is the unchanged `ramWriteValue_eq_read_add_inc` (`RamReadSelection.lean:576`), at 6.7 seconds.
Under `-Dtrace.profiler=true` that unchanged proof reaches the default heartbeat limit, while ordinary builds pass; it is an existing case split over every instruction and a candidate for the cleanup list.
No proof took more than about ten seconds.

## Questions for Ari

- `HonestTrace.corrected_prover_config` (`honest_trace.lean:294`) is now used by no proof; its comment says so.
  It is kept because deleting a definition needs your approval; `bug-report/ram-k-off-by-one/README.md` still refers to it.
  Delete it?

## Blockers

None beyond the approved known-false lemma.
Stop for review.
