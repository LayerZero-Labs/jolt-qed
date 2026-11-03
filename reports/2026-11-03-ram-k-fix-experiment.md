# RAM size fix experiment (a16z/jolt#1951 item 4)

Date: 2026-11-03.
Jolt commit: the pin `5def437f`, with the two changes that a16z/jolt#1951 item 4 proposes applied to the model only.
Lean commit: `188e490` on branch `experiment/ram-k-fix` (worktree `/Users/ari.biswas/Lean/jolt-qed-ramk-fix`), with the uncommitted changes below.
Ari authorized these model changes on this branch only.

## Result

`lake build JoltConstraints` succeeds (8,837 jobs, about 4.5 minutes wall time).
`HonestTrace.prover_config_holds_highest_slot` is proved, and `HonestTrace.witness_params_ram_bounds` stays proved under the new maximum.
No soundness or completeness proof failed under the change, and no premise was added.

`#print axioms`, run with `lake env lean` on a scratch file outside the repository:

- `JoltInstance.soundness`: `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`.
- `JoltInstance.completeness`: `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`.
- `HonestTrace.prover_config_holds_highest_slot`: `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`.
- `HonestTrace.witness_params_ram_bounds`: `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`.

The only `sorry`s left in `JoltConstraints` are the five existing completeness lemmas:

- (01) `honestWitness_ramAddrEqRs1PlusImmMinusLookupIfLoadStore` (`Completeness/RamAddrEqRs1PlusImmMinusLookupIfLoadStore.lean:33`);
- (08) `HonestTrace.floorAccess_address_nonneg` (`Completeness/RightLookupAdd.lean:50`);
- (11) `HonestTrace.shiftData_address_noWrap` (`Completeness/RightLookupEqRightInputOtherwise.lean:49`);
- (37) `honestWitness_ramValEqInitialPlusPrefixRamInc` (`Completeness/RamValEqInitialPlusPrefixRamInc.lean:18`);
- (38) `honestWitness_ramValFinalEqInitialPlusRamInc` (`Completeness/RamValFinalEqInitialPlusRamInc.lean:21`).

No `bv_decide`, `native_decide` or `decide +kernel` was added, and no limit was raised.
With `-Dprofiler.threshold=1000`, no declaration in the five changed proof files takes more than one second.

## The argument

Jolt's tracer allows a RAM access only if it starts below `heap_end` (`HonestTrace.ram_address_below_heap_end`), and every other recorded address lies below `RAM_START_ADDRESS`, at least 128 bytes below `heap_end`.
So the highest touched word index `h` satisfies `h < ⌈(heap_end - lowest) / 8⌉` (`HonestTrace.highest_ram_slot_lt_heap_end`).
Jolt's prover now picks `K = pow2(max(h + 1, imageEnd))`, so `h < K`.
Jolt's verifier's maximum is now `pow2(⌈(heap_end - lowest) / 8⌉)`, and both `h + 1` and `imageEnd` are at most `⌈(heap_end - lowest) / 8⌉`, so `K` is at most the maximum.

## Model changes

- `ProverConfig.checkedRamSize` (`JoltConstraints/prover_config.lean:67`): the rounded value is `max (touched + 1) imageEnd` instead of `max touched imageEnd`, as in the issue's line `let ram_K = (touched + 1).max(image_end).next_power_of_two()`; the image term and the checked rounding are unchanged.
  Its docstring was rewritten.
- `JoltConstraints.VerifierSizes.maxRamSize` (`JoltConstraints/verifier_sizes.lean:38`): the rounded value is `(totalBytes + 7) / 8` (Jolt's `total_bytes.div_ceil(8)`) instead of `totalBytes / 8`.
  Its docstring was rewritten.

## Statement changes

- `HonestTrace.prover_config_ram_K` (`JoltConstraints/prover_config_facts.lean:218`): the size is `2 ^ Nat.clog 2 (max (highest_ram_slot + 1) imageEnd)`; it was `max highest_ram_slot imageEnd`.
- `HonestTrace.prover_config_ram_K_of_nonempty` (`JoltConstraints/Completeness/Helpers/VerifierSizes.lean:57`): the same `+ 1` in its size conjunct.
- `HonestTrace.highest_ram_slot_le_heap_end` became `HonestTrace.highest_ram_slot_lt_heap_end` (`JoltConstraints/Completeness/Helpers/VerifierSizes.lean:230`): from `highest_ram_slot ≤ (heap_end - lowest) / 8` to `highest_ram_slot < (heap_end - lowest + 7) / 8`.
- `remap_address_le` became `remap_address_lt` (`JoltConstraints/witness_params.lean:63`): from `address ≤ bound → index ≤ (bound - lowest) / 8` to `lowest < bound → address < bound → index < (bound - lowest + 7) / 8`.
  Its only caller is `HonestTrace.highest_ram_slot_lt_heap_end`, which proves both hypotheses.

No approved statement, no assumption and no premise changed.
`JoltInstance.soundness`, `JoltInstance.completeness`, `HonestTrace.prover_config_holds_highest_slot` and `HonestTrace.witness_params_ram_bounds` keep their text.

## Proof changes

- `HonestTrace.prover_config_holds_highest_slot` (`JoltConstraints/prover_config_facts.lean:255`): the `sorry` is replaced by a three-line proof from `HonestTrace.prover_config_ram_K`; its FIXME docstring was rewritten.
- `HonestTrace.prover_config_ram_K` (`prover_config_facts.lean:218`): proof unchanged.
- `HonestTrace.highest_ram_slot_lt_heap_end` (`Completeness/Helpers/VerifierSizes.lean:230`): adds the lowest-address and canary facts for positivity and the strict bound.
- `HonestTrace.witness_params_ram_maximum` (`Completeness/Helpers/VerifierSizes.lean:327`): the maximum is `2 ^ Nat.clog 2 ((heap_end - lowest + 7) / 8)`, and its `2^61` bound is restated for it; docstring updated.
- `verifier_ram_image_end_bounded` (`JoltConstraints/Soundness/Layer7/ProverAccepts.lean:234`): its local `wordsBound` is restated for `(heap_end - lowest + 7) / 8 ≤ 2^61`.
- `represented_ram_size_computes` (`Soundness/Layer7/ProverAccepts.lean:279`): the witness size is `2 ^ Nat.clog 2 (max (touched + 1) (finish + 1))`, still below `2^62`.
- `HonestTrace.witness_params_ram_minimum_of_nonempty`, `HonestTrace.verifier_ram_minimum_computes`, `HonestTrace.witness_params_ram_bounds`, `HonestTrace.prover_config_ram_K_ge_two`, the `Soundness/Layer3/Layout.lean` lemmas and `DeviceMemoryObstruction.layout_ram_bound` build unchanged.

## Docstring-only changes

- `Trace.prover_config` (`prover_config.lean:138`), `Trace.highest_ram_slot` (`prover_config_facts.lean:204`), `HonestTrace.prover_config_ram_fits` (`prover_config_facts.lean:275`), `HonestTrace.witness_params_ram_fits` (`witness_domain.lean:102`), `JoltInstance.completeness` (`Completeness/completeness.lean:81`) and `HonestTrace.allConstraints_prover_sizes` (`Completeness/All.lean:186`) no longer call `HonestTrace.prover_config_holds_highest_slot` known-false.
- `HonestTrace.witness_params_ram_bounds` (`Completeness/Helpers/VerifierSizes.lean:382`): its example now rounds `max(1001, 4137)`.

## Effect on soundness

Soundness uses the verifier's maximum only abstractly, through `JoltInstance.ram_size_in_bounds` and `JoltInstance.RamRegionFits` (`Soundness/Layer3/Layout.lean`), so no soundness proof needed a change beyond the two Layer 7 bounds above.
The text of `RamRegionFits` is unchanged, but it now bounds the larger maximum: when `heap_end - lowest` is not a multiple of 8 and `⌊(heap_end - lowest) / 8⌋` is a power of two, the maximum doubles, and `lowest + 8 * maximum ≤ 2^64` excludes more instances.
The concrete layout in `DeviceMemoryObstruction.layout_ram_bound` has `heap_end - lowest = 168`, whose maximum stays 32.
The example outside the build, `bug-report/ram-address-wraparound/layout_check.lean`, still checks with `lake env lean`: its maximum stays `2^61`.

## Documents

- `JoltConstraints/model_review.md`: the summary, the #1951 item 4 row, the "Jolt's prover accepts the trace" row and "Proofs owed" now say the fix is modeled on this branch, the gap count is five, and the `HonestTrace.prover_config_holds_highest_slot` row is removed.
- `JoltConstraints/constraints.md`: the status line no longer calls the lemma known-false.
- Left unchanged: the Step 5 history in `JoltConstraints/constraints.md` (item 11) and the rule in `methods/constraint_proving.md` that keeps `HonestTrace.prover_config_holds_highest_slot` as a gap.
