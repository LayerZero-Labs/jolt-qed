# Helper C staging report

Work was done on `feat/soundness` in `/Users/ari.biswas/Lean/jolt-qed-public` on 2026-10-23.
Helper C now follows from exactly three named staged obligations in `JoltConstraints/Soundness/Layer7/ProverAccepts.lean`.
All three parts remain `sorry`, as requested.
C's statement and hypotheses are unchanged.
No commit was made by this task.

## Audit before editing

I read `AGENTS.md`, `methods/layer6/reuse.md`, `methods/layer7/helper-d-report.md`, `methods/layer7/helper-c.md`, the Layer 7 section of `methods/soundness.md`, and the relevant entries in `JoltConstraints/model_review.md`.
I found no false claim in the helper C plan or missing premise that requires changing C.
The reasoning below supports the staged statements; it does not constitute completed Lean proofs of them.

The Jolt source audit used `git show` and `git grep` at pin `5def437f21a0006e13c063a03f0b5a7c9b93cd6f`.
At that pin, `jolt/crates/jolt-prover/src/config.rs`, `ProverConfig::derive_from_dimensions`, checks the last jump, checked trace padding, checked RAM sizing, and the public trace maximum.
The Lean definitions at `JoltConstraints/prover_config.lean:42`, `:58`, `:70`, and `:123` give precisely the three obligations used here.
The final trace-maximum check is included in the padding obligation.
The 256-cycle floor agrees with `jolt/crates/jolt-verifier/src/config.rs`, `MIN_PADDED_TRACE_LENGTH`, in the modeled base/Dory configuration.
The verifier RAM bounds agree with `jolt/crates/jolt-program/src/preprocess/ram.rs`, `compute_min_ram_k` and `compute_max_ram_k`.

### 1. Last jump and branch stalls

`soundness_last_row_is_jump` at `JoltConstraints/Soundness/Layer7/LastJump.lean:634` needs a run ending at the witness boundary or immediately before padding.
C's `UntrustedAnswerTrace` does not itself supply that boundary condition.
`soundness_stopping` at `JoltConstraints/Soundness/Layer7/Stopping.lean:17` accepts a cut that already ends in a stable stall; this case does not establish that the retained last instruction is a jump.
Thus applying the last-jump theorem directly to C's trace would leave an unsupported premise.

The branch alternative appears excluded by the existing branch-specific constraint argument.
The relevant declarations in `JoltConstraints/Soundness/Layer7/StallSuffix.lean` are:

| Declaration | Line | Use in the future proof |
|---|---:|---|
| `stable_stall_control_flow` | 2689 | Classify the executed final stable stall as JAL, JALR, or a branch |
| `expanded_control_read_not_temporary` | 326 | Justify use of represented branch operands |
| `represented_last_branch_registers` | 2787 | Obtain the final branch's operand agreement in the register table |
| `stall_branch_model_target` (private) | 1399 | A stable executed branch is taken and has immediate zero |
| `expanded_branch_same_address` (private) | 1341 | A selected row at this source address is the same singleton branch row |
| `stall_branch_replay_target` (private) | 1626 | Its constrained next unexpanded PC equals the nonzero source address |
| `stall_suffix_initial_branch` | 2866 | Establish the branch replay invariant at the cut |
| `stall_branch_step` | 1703 | Preserve the branch control operands and source address on subsequent real cycles |

A taken zero-offset branch keeps targeting its source address, which is nonzero for accepted expanded bytecode.
At a transition to padding, `nextUnexpandedPCEqShift` and the padding row's zero unexpanded PC would instead require that target to be zero.
At the final witness cycle, `nextUnexpandedPCEqShift` directly requires zero.
Following branch replay to either boundary therefore gives a contradiction.
The existing padding-zero argument is `unexpanded_zero_of_padding`, private at `JoltConstraints/Soundness/Layer7/LastJump.lean:68`.
The shift equation is defined at `JoltConstraints/Constraints/NextUnexpandedPCEqShift.lean:11`.

This branch-specific route does not require `NextPCNoWrap`.
The general `stall_suffix_replays_source` at `StallSuffix.lean:3077` does require that premise for its other cases, so it cannot simply be called from C.
The staged part retains the actual execution certificate in `UntrustedAnswerTrace`; it does not infer an instruction from an isolated post-state.
The audited branch arguments use the source compression metadata and accepted PC map, including address uniqueness.
Several useful facts listed above are private; a later authorized proof task may need to expose them in their existing files.
This staging task does not duplicate their proofs or edit those files.

### 2. Checked trace length

Write `n` for the row count, `T = 2^logT` for the witness length, and `M` for the public maximum.
Representation and `ConstraintContext.traceLengthBound` give `n ≤ T ≤ M`.
The context's floor gives `256 ≤ T ≤ M`.
Let `P = 2 ^ Nat.log2 M`, the largest power of two at most `M`.
Then `T ≤ P`, while `NoMaxLengthTrace` gives `n ≠ P`, hence `n + 1 ≤ P`.
Both checked addition and checked rounding fit because `P ≤ M < 2^64`.
The rounded result is at most `P`; taking its maximum with 256 still stays within `M`.
This handles non-power-of-two public maxima as well as power-of-two maxima.

The relevant context fields are at `JoltConstraints/constraint_context.lean:28` and `:33`, and the restriction is `JoltConstraints/Soundness/Assumptions.lean:62`.
The future arithmetic proof can use `Nat.log2_eq_log_two`, `Nat.le_log_of_pow_le`, `Nat.pow_log_le_self`, `Nat.clog_le_of_le_pow`, and `Nat.pow_le_pow_right`.
The existing `ProverConfig.checkedTraceLength_eq` describes a successful result, but does not itself establish the required success.
The staged statement is arithmetic only, with no witness context or execution arguments.

### 3. Checked RAM size

The address equation is `ConstraintEquations.ramAddressEqRamRaf`, whose definition is `JoltConstraints/Constraints/RamAddressEqRamRaf.lean:14`.
Together with the RAM selector constraints, it says a nonzero raw address equals the layout base plus eight times a selected in-domain index.
The exact reusable facts are `ramRa_unique_of_address_ne_zero` at `Soundness/Layer1/Ram.lean:109`, `ramAddress_of_selected` at `Soundness/Layer1/RamReads.lean:19`, and `ramAddress_eq_of_selected` at `Soundness/Layer3/Address.lean:29`.
These paths are relative to `JoltConstraints/`.

`RepresentsRows.ramAddress` supplies the equality with an actual 64-bit address needed by `ramAddress_eq_of_selected`.
`ram_address_value_lt_char` at `Soundness/Layer1/Ram.lean:32` bounds the selected address below the field characteristic without requiring `RamRegionFits`.
Consequently, the field equality gives a natural-number equality and the nonzero trace address is at least the layout's lowest address.
Zero is deliberately ignored by `ExecutionDimensions.observe`, matching the prover's no-access sentinel.
`TraceRow.ram_address_eq` at `witness_domain.lean:56` and `TraceRow.ram_address_lt` at `witness_params.lean:41` connect the recorded addresses to these observations and their 64-bit bounds.

`initial_state_device` at `layout_facts.lean:568`, together with `context.publicIo`, identifies the trace's initial layout with the constraint and verifier layout.
`context.ramSizeBounds`, at `constraint_context.lean:35`, certifies successful `VerifierSizes.minRamSize` and `maxRamSize` calculations and places the witness domain between them.
The minimum-size computation already validates the image-start remapping and the first image-end addition.
Its image end is at most the minimum RAM size, hence at most the maximum RAM size.
The maximum RAM size is at most `2^61`: it rounds `(heap_end - lowest) / 8`, where `heap_end` is a 64-bit word.
The prover's extra image sentinel therefore makes the end at most `2^61 + 1`, whose rounding is at most `2^62` and fits the host size.
Every touched slot is below `2^61` because the raw address is a 64-bit word.
The address fold must still be connected to these bounds in the future proof; the existing `ExecutionDimensions.checkedTouched_fold` proves the forward implication from successful checking, so success must not be assumed circularly.

The lower bound comes from the constraints and representation, and overflow is controlled by verifier size bounds and 64-bit addresses.
No new restriction, `RamRegionFits`, or `NextPCNoWrap` premise is needed for this part.
Unlike execution reconstruction, C already receives the encoding of each actual RAM address through representation.
The staged result claims that the modeled prover computes a RAM size; it does not claim that its existing highest-touched-slot rounding policy contains every accessed slot.

## Staged statements and caller

All declaration names below are in namespace `JoltInstance`.

| Declaration | File and line | Status |
|---|---|---|
| `represented_trace_ends_in_jump` | `JoltConstraints/Soundness/Layer7/ProverAccepts.lean:17` | New staged obligation |
| `checked_trace_length_fits` | `JoltConstraints/Soundness/Layer7/ProverAccepts.lean:40` | New staged obligation |
| `represented_ram_size_computes` | `JoltConstraints/Soundness/Layer7/ProverAccepts.lean:62` | New staged obligation |
| `soundness_prover_accepts` | `JoltConstraints/Soundness/TopLevel.lean:155` | Proved from the three parts; original statement preserved |

The first part takes C's field, instance, witness, constraint context and equations, completed relaxed trace, bytecode equality, and only `RepresentsRows` from the stronger representation premise.
Its conclusion is:

```lean
trace.rows.size = 0 ∨ trace.execution_dimensions.ends_in_jump = true
```

The second part is:

```lean
theorem checked_trace_length_fits
    (rows logT : Nat) (maximum : BitVec 64)
    (rowsBound : rows ≤ 2 ^ logT)
    (witnessBound : 2 ^ logT ≤ maximum.toNat)
    (floor : 256 ≤ maximum.toNat)
    (notMax : rows ≠ 2 ^ Nat.log2 maximum.toNat) :
    ∃ padded, ProverConfig.checkedTraceLength rows = some padded ∧
      padded ≤ maximum.toNat
```

C supplies `rowsBound` from representation, `witnessBound` from the context, `floor` by transitivity of the context's floor and upper bound, and `notMax` by applying its existing `NoMaxLengthTrace` premise to this trace.

The third part takes the field, instance, witness, context and equations, an ordinary `Trace`, its initialization equality, its row-count bound, and the RAM-address observation equality for each represented cycle.
It does not take bytecode equality, operand agreement, final-memory agreement, or a stopping certificate.
Its conclusion is:

```lean
∃ ramK, ProverConfig.checkedRamSize trace.execution_dimensions
  trace.initialState.jolt_device.memory_layout
  (min_bytecode_address joltInstance.program.memory_init)
  (program_image_len_words joltInstance.program.memory_init) = some ramK
```

C supplies its inherited `trace.initialized` certificate and `represented.rowsBound` and `represented.ramAddress` projections.
The caller then unfolds the checked prover configuration and discharges its guards and option computations with the three conclusions.
Every new helper is used by C.
No existing theorem gained a hypothesis, and no approved statement, definition, restriction, or language predicate changed.
The only changes to C outside its proof are its new import and updated docstring.
There are no new `bv_decide`, `native_decide`, `decide +kernel`, explicit axioms, or proof-limit overrides.

## Validation

`lake build JoltConstraints` failed in the other agent's unfinished `JoltConstraints/Soundness/Layer6/DivisionAppend.lean:25`.
The reported `rfl` goal compared `some value` with `none` in a `VirtualAdvice` case.
The build successfully built the new `JoltConstraints.Soundness.Layer7.ProverAccepts` module in 4.5 seconds.
I did not edit any division file or `PlainRow.lean`.

The authorized fallback passed all 8595 jobs:

```text
lake build JoltConstraints.Soundness.Layer7.ProverAccepts
```

Checking all current `TopLevel.lean` contents through standard input was also blocked: the failed dependency build left `DivisionAppend.olean` unavailable.
I therefore extracted C's exact current declaration, without changing its statement or proof text, into standard input under namespace `JoltInstance`, importing `JoltConstraints.Soundness.Layer7.ProverAccepts`.
That declaration checked successfully, followed in the same check by the axiom commands below.
This validates the new C proof and its module dependency; it does not claim that the current full `TopLevel.lean` import graph builds.

| `#print axioms` target | Result |
|---|---|
| `JoltInstance.soundness_prover_accepts` | `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound` |
| `JoltInstance.represented_trace_ends_in_jump` | `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound` |
| `JoltInstance.checked_trace_length_fits` | `propext`, `sorryAx` |
| `JoltInstance.represented_ram_size_computes` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` |

A separate successful check traversed C's dependency closure using Lean's `CollectAxioms.collect` and inspected declaration values for direct `sorryAx` applications.
It found exactly `checked_trace_length_fits`, `represented_trace_ends_in_jump`, and `represented_ram_size_computes`.
C has no direct `sorry`, and no other dependency in its closure directly applies `sorryAx`.

C's proof elaboration took 0.034325 seconds with one worker and `-Dtrace.Elab.async=true -Dtrace.profiler=true -Dtrace.profiler.threshold=10000`.
The profiler threshold controls reporting, not proof resources.
No completed new or changed proof exceeded ten seconds.
The three staged bodies are unproved, so their build time is not evidence of proof completion.
A textual comparison with HEAD confirmed that C's statement and hypotheses are unchanged.
Checks confirmed exactly three staged `sorry` bodies, none inside C, and no trailing whitespace in the owned Lean files.

Only `JoltConstraints/Soundness/TopLevel.lean`, the new `JoltConstraints/Soundness/Layer7/ProverAccepts.lean`, and this requested report were edited by this task.
Other agents' concurrent edits and commits were left alone.
The scope excludes `methods/soundness.md` and `JoltConstraints/model_review.md`; their next authorized update should replace C's undivided obligation with these three staged parts.
Work stops here for review, without proving the parts.

## Padded length

`JoltInstance.checked_trace_length_fits` is now proved at `JoltConstraints/Soundness/Layer7/ProverAccepts.lean:40`.
Its statement and hypotheses are unchanged, and no new declaration was added.
The other two staged helper C obligations remain open.
No commit was made.

I checked the plan against `ProverConfig.checkedTraceLength` at `JoltConstraints/prover_config.lean:42`, `MemoryLayout.checkedAdd` at `JoltConstraints/Constraints/MemoryLayout.lean:36`, and `VerifierSizes.checkedNextPowerOfTwo` at `JoltConstraints/verifier_sizes.lean:11` before editing.
The pinned `ProverConfig::derive_from_dimensions` in `jolt/crates/jolt-prover/src/config.rs` uses checked addition, checked next-power-of-two rounding, and the minimum padded length in that order.
The pinned base/Dory `MIN_PADDED_TRACE_LENGTH` is 256 in `jolt/crates/jolt-verifier/src/config.rs`.
The proof bounds the row count plus one by the largest power of two at most the public maximum, then bounds both checked operations and the 256 floor by that maximum.
It applies equally when the public maximum is not a power of two.

`lake build JoltConstraints.Soundness.Layer7.ProverAccepts` passed with 8595 jobs; its final module compiled in 3.0 seconds.
`git diff --check` passed.
`#print axioms JoltInstance.checked_trace_length_fits` returned `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
No changed proof took more than ten seconds, and there is no new `bv_decide`, `native_decide`, `decide +kernel`, axiom, or proof-limit override.
I edited only `JoltConstraints/Soundness/Layer7/ProverAccepts.lean` and this report.

## Ends in a jump

`JoltInstance.represented_trace_ends_in_jump` is proved at `JoltConstraints/Soundness/Layer7/ProverAccepts.lean:68`, with its statement and hypotheses unchanged.
The work stayed on `feat/soundness` in `/Users/ari.biswas/Lean/jolt-qed-public`.
No commit was made by this task.

I checked the claims in `helper-c-jump.md` and section "1. Last jump and branch stalls" against their definitions and proofs before editing and found no incorrect claim or missing premise.
`UntrustedAnswerTrace.stops` supplies the stable stall, and its underlying run supplies the execution certificate required by `stable_stall_control_flow` and `stall_branch_model_target`.
`represented_last_branch_registers` uses `expanded_control_read_not_temporary` to recover the branch operands.
`expanded_branch_same_address` uses `expanded_same_source_rows`, whose proof uses accepted PC-map address uniqueness.
The branch model proof uses `source_is_compressed`, and neither branch initialization nor branch replay requires `NextPCNoWrap`.
The general `stall_suffix_replays_source` still requires that premise and is not used here.

At pin `5def437f`, Jolt's prover checks nonempty traces' `ends_in_jump` in `jolt/crates/jolt-prover/src/config.rs` (`ProverConfig::derive_from_dimensions`).
The dimension summary reads the final row's Jump flag in `jolt/crates/jolt-program/src/execution/trace.rs` (`ExecutionDimensions::from_rows`).
The corresponding Lean summary is `Trace.execution_dimensions`, and `JoltISA.Instr.is_jump` recognizes JAL and JALR.
The branch constraint is in `jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs` (`rv64_eq_constraint_rows`), and the next-cycle address with zero at the end is in `jolt/crates/jolt-witness/src/witnesses/pc.rs` (`NextUnexpandedPc::extract`).
I also checked `jolt/tracer/src/emulator/cpu.rs` (`Cpu::tick`) at stopping-rule merge commit `0249591a`.

The proof starts the branch invariant at the last represented cycle, including when the trace fills the witness.
Each real replay has a nonzero next unexpanded PC because its target is an accepted bytecode address.
If the next cycle were padding, `unexpanded_zero_of_padding` and `nextUnexpandedPCEqShift` would make that target zero.
Induction therefore carries the real branch invariant through every remaining witness cycle.
At the final cycle, the shift equation requires zero directly, contradicting the replay target.
The existing control-flow classification then leaves JAL or JALR, and unfolding the dimension summary finishes the theorem.

All declarations below are in namespace `JoltInstance`.
Paths are relative to `JoltConstraints/Soundness/Layer7/`.

| Declaration | File and line | Change |
|---|---|---|
| `represented_branch_stall_replays` | `ProverAccepts.lean:16` | New forward induction: every witness cycle from the final represented branch has nonzero next unexpanded PC. |
| `represented_trace_ends_in_jump` | `ProverAccepts.lean:68` | Replaced its staged `sorry` with the proof. |
| `selected_last_represented_row_at_end` | `StallSuffix.lean:197` | Extracted the selection proof, using `represented.rowsBound` so it also covers a full witness. |
| `selected_last_represented_row` | `StallSuffix.lean:257` | Derived the original statement from the extracted selection lemma. |
| `stall_branch_replay` | `StallSuffix.lean:1734` | Extracted the branch-step proof, exposing nonzero next PC and preservation at any successor cycle. |
| `stall_branch_step` | `StallSuffix.lean:1800` | Derived the original statement from `stall_branch_replay`. |
| `represented_last_branch_invariant` | `StallSuffix.lean:2917` | Extracted initialization at the branch's own represented cycle, without assuming a successor cycle or a stable stall. |
| `stall_suffix_initial_branch` | `StallSuffix.lean:2956` | Reused the extracted initialization, then applied the existing branch step. |
| `unexpanded_zero_of_padding` | `LastJump.lean:70` | Made public in place; its statement and proof are unchanged. |

These are the four new declarations, three existing proofs derived from their extractions, the completed target, and the sole lemma made public.
Every new lemma is used.
No existing theorem statement or hypothesis changed; a textual comparison against HEAD checked this in all three Lean files.
The original selection wrapper retains its now-unused `cutBound` parameter, preserving its statement.
No definition, restriction, language predicate, or other approved statement changed.
There are no new `sorry`s, explicit axioms, `bv_decide` uses, native decision proofs, or proof-limit overrides.
All new or changed proof bodies are under 60 lines.

`lake build JoltConstraints` failed in the other agents' unfinished files: `Soundness/Layer5/DeviceMemory.lean:508` and `:510`, and `Soundness/Layer6/DivisionAppend.lean:878`, at the time of the check.
The former reported an unsolved goal and a parser error; the latter reported a dependent rewrite failure.
The authorized scoped build passed all 8650 jobs:

```text
lake build JoltConstraints.Soundness.Layer7.ProverAccepts
```

This includes both modified supporting modules.
The full-build attempt also rebuilt `LastJump`, `ProverAccepts`, and the existing `Stopping` caller successfully.
`git diff --check` passed for the owned Lean files.

`#print axioms JoltInstance.represented_trace_ends_in_jump` returned:

```text
propext
sys_enable_experimental_extensions
Classical.choice
Quot.sound
JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5
```

There is no `sorryAx` dependency.
The last entry comes from the existing `bv_decide` at `JoltConstraints/Completeness/NextUnexpandedPCEqPCPlusImmIfShouldBranch.lean:104`, already listed under "bv_decide" in `JoltConstraints/model_review.md`.
Separate axiom checks of all four new declarations and the newly public padding lemma also found no `sorryAx`.
The remaining staged `represented_ram_size_computes` was left unchanged.

With one worker and `-Dtrace.Elab.async=true -Dtrace.profiler=true -Dtrace.profiler.threshold=10000`, the target proof elaborated in 0.069 seconds and the forward replay proof in 0.037 seconds.
The extracted selection, branch replay, and branch initialization proofs took 0.262, 0.478, and 0.162 seconds respectively.
No new or changed proof exceeded ten seconds.
The `StallSuffix` module build took 18 seconds in total; that is not a single proof's time.
The profiler options only report timings and do not raise proof limits.

Only `ProverAccepts.lean`, `StallSuffix.lean`, `LastJump.lean`, and this report were edited by this task.
The other agents' files, `methods/soundness.md`, and `JoltConstraints/model_review.md` were left alone.
Work stops here for review.

## RAM size

`JoltInstance.represented_ram_size_computes` is proved at `JoltConstraints/Soundness/Layer7/ProverAccepts.lean:278`, without changing its statement or hypotheses.
The task stayed on `feat/soundness` in `/Users/ari.biswas/Lean/jolt-qed-public` and made no commit.

I read `AGENTS.md`, `methods/layer6/reuse.md`, section "3. Checked RAM size" above, and `methods/layer7/helper-c-ram.md` before editing.
I checked the plan's claims against the definitions and existing proofs and found no incorrect claim or missing premise.
The address equation and selector lemmas recover a natural-number address above the layout base using the represented 64-bit address and `ram_address_value_lt_char`.
This does not require `RamRegionFits`.
`TraceRow.ram_address_eq` connects each recorded address to `TraceWitness.RamAddress`, and `TraceRow.ram_address_lt` supplies the 64-bit bound.
The existing `initial_state_memory_layout` in `Soundness/Layer3/State.lean` already proves the required layout identification from `initial_state_device` and `context.publicIo`; the final proof reuses it.

I checked Jolt's pinned code with `git show` at `5def437f`.
`jolt/crates/jolt-prover/src/config.rs` (`ProverConfig::derive_from_dimensions`, `checked_remap_address`) performs the two checked subtractions, image remapping, image-end additions, and power-of-two rounding used by the model.
`jolt/crates/jolt-program/src/preprocess/ram.rs` (`compute_min_ram_k`, `compute_max_ram_k`) supplies the verifier's checked image extent and maximum based on `(heap_end - lowest) / 8`.
`jolt/common/src/jolt_device.rs` (`MemoryLayout::get_lowest_address`, `MemoryLayout::remap_word_address`) identifies the same lower address and zero sentinel.
`jolt/crates/jolt-program/src/execution/trace.rs` (`RamAddressBounds::observe`, `ExecutionDimensions::from_rows`) ignores zero while collecting the minimum and maximum nonzero addresses.

The proof uses the existing `ExecutionDimensions.boundsFor_fold` induction to identify the recorded nonzero endpoints.
Their lower bounds make both checked subtractions succeed, and the upper address bound makes the highest touched word index less than `2 ^ 61`.
It does not assume successful checking through `ExecutionDimensions.checkedTouched_fold`, whose implication runs in the opposite direction.
Successful verifier sizing bounds the image's exclusive word end by the verifier minimum, then maximum, then `2 ^ 61`.
Adding the prover's sentinel and rounding the maximum of that end and the touched index produces at most `2 ^ 62`, which fits the 64-bit host range.
This proves that the modeled RAM-size computation succeeds; it does not change or establish containment for the prover's existing highest-touched-slot rounding policy.

The new declarations and completed target are in namespace `JoltInstance`, all in `JoltConstraints/Soundness/Layer7/ProverAccepts.lean`.

| Declaration | Line | Result |
|---|---:|---|
| `represented_ram_addresses_bounded` | 162 | Every recorded address is below `2 ^ 64` and is zero or at least the constraint layout's lowest address. |
| `checked_touched_of_address_bounds` | 208 | A list satisfying those address bounds passes checked remapping, with touched index below `2 ^ 61`. |
| `verifier_ram_image_end_bounded` | 234 | Successful ordered verifier sizes certify image remapping and addition, with exclusive image end at most `2 ^ 61`. |
| `represented_ram_size_computes` | 278 | The original staged conclusion, proved by assembling the address, image, and rounding bounds. |

The following existing private lemmas were made public in place, with explanatory docstrings and no change to their statements or proofs:

| Declaration | File and line |
|---|---|
| `ExecutionDimensions.boundsFor_fold` | `JoltConstraints/prover_config_facts.lean:62` |
| `ProverConfig.checkedRound_some` | `JoltConstraints/prover_config.lean:82` |

Every new helper is used by the completed target, and each publicized lemma is used by a new helper.
The list helper takes only addresses, a layout, and address bounds; the image helper takes only a program, layout, and successful ordered verifier sizes.
No existing statement or hypothesis changed, and no definition, restriction, or language predicate changed.
There are no new `sorry`s, explicit axioms, `bv_decide` uses, native decision proofs, or proof-limit overrides.
The three new proof bodies have 26, 13, and 21 lines, and the target proof has 38 lines.
A textual comparison against HEAD confirmed that the target statement is unchanged, both exposed proofs are unchanged, and the existing jump and padded-length sections are byte-for-byte unchanged.
Only the imports and RAM-size portion of `ProverAccepts.lean` changed.

The requested module build passed all 8654 jobs:

```text
lake build JoltConstraints.Soundness.Layer7.ProverAccepts
```

The final module compiled in 3.9 seconds with no new warnings.
`git diff --check` passed for the owned files.
No full-library build result is claimed for this task.

`#print axioms JoltInstance.represented_ram_size_computes` returned exactly:

```text
propext
Classical.choice
Quot.sound
```

The target has no `sorryAx` or `bv_decide` dependency.
All three new helpers have the same axiom list.
`ExecutionDimensions.boundsFor_fold` also has that list; `ProverConfig.checkedRound_some` uses only `propext`.
There is no remaining `sorry` in `ProverAccepts.lean`.

With one worker and `-Dtrace.Elab.async=true -Dtrace.profiler=true -Dtrace.profiler.threshold=10000`, the address, touched-index, image-end, and target proofs elaborated in 0.099384, 0.037031, 0.023710, and 0.048003 seconds respectively.
No new or changed proof took more than ten seconds.
These profiler settings report timings without raising proof limits.

This task edited only `JoltConstraints/Soundness/Layer7/ProverAccepts.lean`, the two files containing the publicized lemmas, and this report.
The other agents' files, `methods/soundness.md`, and `JoltConstraints/model_review.md` were left alone.
Work stops here for review, without a commit.
