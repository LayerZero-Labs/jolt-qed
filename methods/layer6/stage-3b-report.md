# Layer 6 stage 3b report

Part A is present at commit `dc3cd2b` on `feat/soundness`.
I reread `stage-3b.md` and checked its claims before editing.
The staged declarations are in `BoundaryStart.lean`, the Part A `RegisterAgreement.toOn` and `RegisterAgreementOn.mono` helpers are proved, and `BoundaryState` and `ExpansionState` have the fields described by the plan.
The empty run is constructible from `context.expands` and `context.initialized`, and its execution, start, and linkage conditions have empty domains.
`JoltConstraints/program.lean` makes entry address zero select padding slot zero, while `BytecodePC.lean` and the entry selector constraint determine the selected slot at cycle zero.
The accepted bytecode layout and source-address uniqueness facts needed to turn a nonzero entry slot into a source start are present in `ProgramLayout.lean` and `program_facts.lean`.
Jolt's preprocessing inserts the no-op sentinel, validates address runs, and records the first PC in `jolt/crates/jolt-program/src/preprocess/bytecode.rs:32-58,125-172,224-231` at pin `5def437f`.
Jolt's tracer initializes an empty output buffer and a false panic bit in `jolt/tracer/src/lib.rs:352-390` and `jolt/common/src/jolt_device.rs:134-143` at that pin.
Jolt's witness builds initial RAM before any rows and writes the final panic and termination words in `jolt/crates/jolt-witness/src/backend/trace/ram.rs:80-129,132-195` at that pin.
No plan claim was found false.

The following declarations were added or changed.
The times are proof-elaboration seconds from Lean's asynchronous profiler with one worker; no proof exceeded ten seconds.

| Declaration | File and line | Result | Time |
| --- | --- | --- | ---: |
| `first_row_of_entry_slot` | `JoltConstraints/Soundness/Layer6/BoundaryStart.lean:19` | New private staged lemma with `sorry`. | 0.000457 s |
| `empty_run_ram_word` | `JoltConstraints/Soundness/Layer6/BoundaryStart.lean:37` | New private staged lemma with `sorry`. | 0.000233 s |
| `boundaryState_empty` | `JoltConstraints/Soundness/Layer6/BoundaryStart.lean:54` | Original statement unchanged; its proof constructs the empty run and closes `BoundaryState` using the two staged lemmas. | 0.181086 s |
| `expansion_start` | `JoltConstraints/Soundness/Layer6/BoundaryStart.lean:146` | Original statement unchanged; proved from `BoundaryState.ready`, `atBoundary`, and Part A's live-set restriction helper. | 0.159559 s |
| `context_initial_termination_zero` | `JoltConstraints/Soundness/Layer7/TerminationStore.lean:483` | Made public in place; its statement and proof are unchanged. | 0.009399 s |

`first_row_of_entry_slot` is the remaining bytecode-layout obligation: for a nonzero `get_first_pc` result, identify the row at slot minus one and prove it starts the unique source instruction at the entry address.
Its premises contain only the program image, expanded rows, preprocessing result, slot, and nonzero condition; no trace row is treated as an execution certificate.
The needed argument is not a short existing proof in `reuse.md`, so I staged it rather than adding a long layout proof here.
`empty_run_ram_word` is the remaining RAM-image obligation: on an initialized empty run, show that empty outputs and false panic leave every nontermination word equal to the initial image, including the panic word's initial zero from the checked layout.
Its termination exclusion is essential because `finalRamWord` sets that word to one for an unpanicked empty run.
The device-region disjointness argument is not a short existing proof in `reuse.md`, so I staged it separately.
These are proof obligations, not added soundness premises.

`lake build JoltConstraints` passed with 8805 jobs, and `git diff --check` passed for the files I edited.
`#print axioms JoltInstance.expansion_start` has no `sorryAx`.
`#print axioms JoltInstance.boundaryState_empty` still has `sorryAx` through the two staged helpers.
`#print axioms JoltInstance.soundness` still reports `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`, and the existing `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5` axiom.
No `bv_decide` use or proof limit was added.
I did not edit the concurrently modified `DivisionBlock.lean` or make a commit.

## Stage 4b

I checked the plan against `get_first_pc`, `preprocess_slots`, `expand_program_layout`, `rows_first_starts`, `rows_after_last`, `JoltInstance.initial_state`, the RAM-image definitions, and the checked-layout lemmas before editing.
The pinned Jolt preprocessing, tracer, device-layout, and RAM-witness paths cited above agree with those claims.
I found no false claim in the plan.

The following declarations in `JoltConstraints/Soundness/Layer6/BoundaryStart.lean` are new or changed.
Times are proof-elaboration seconds from Lean's asynchronous profiler with one worker.

| Declaration | Line | Result | Time |
| --- | ---: | --- | ---: |
| `first_row_of_entry_slot` | 19 | Proved with its staged statement unchanged; preprocessing locates the bytecode row, and the expansion layout makes the first matching row a source start. | 0.286555 s |
| `initialized_device_words` | 105 | New private staged lemma with `sorry`: initialization leaves outputs empty and panic false, and its initial RAM image is zero at the panic word. | 0.000305 s |
| `empty_run_ram_word` | 121 | Proved with its staged statement unchanged, using `initialized_device_words` for the initial panic word. | 0.082995 s |

The remaining `initialized_device_words` proof must extract the input-size check and device fields from `JoltInstance.initial_state`, then use the checked `MemoryLayout.new` geometry to show that the panic word lies beyond the advice and input overlays and below ordinary RAM.
The existing `initialRamWord_termination_zero` proof in `JoltConstraints/Soundness/Layer7/TerminationStore.lean:408` supplies the analogous argument for the termination word, but its conclusion does not cover the panic word.
This is a named proof obligation, not an added premise of either target lemma.
The `first_row_of_entry_slot` proof is 69 lines of slot and list-index bookkeeping; its elaboration is below one second.
No private lemma was made public, and no `bv_decide` use or proof limit was added.

`lake build JoltConstraints` passed with 8806 jobs, the direct Lean check of `BoundaryStart.lean` passed with the expected warning for the new staged lemma, and `git diff --check` passed.
`#print axioms JoltInstance.boundaryState_empty` reports `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`.
The remaining `sorryAx` is reached through `initialized_device_words`.
I changed no files outside `BoundaryStart.lean` and this report, and made no commit.

## Stage 4c

I checked the task's claims against the current Lean definitions and Jolt at pin `5def437f` before editing.
Jolt's tracer checks the three supplied buffer lengths in `jolt/tracer/src/lib.rs` (`create_emulator`), and Jolt's device layout rounds the input maximum and places output, panic, and termination in order in `jolt/common/src/jolt_device.rs` (`MemoryLayout::try_new`).
Jolt's prover initializes RAM from the advice and input buffers before writing the final panic and termination words in `jolt/crates/jolt-witness/src/backend/trace/ram.rs` (`initial_ram_state`, `final_ram_state`).
I found no false plan claim.
The bytecode start claim needs an expansion certificate; it is false for an arbitrary array of rows, so the new helper takes only the bytecode as data together with a proof that some program expands to it.

| Declaration | File and line | Change |
| --- | --- | --- |
| `new_input_size_bound` | `JoltConstraints/layout_facts.lean:483` | New public theorem relating the configured input maximum to the rounded layout maximum. |
| `initialRamWord_after_output_zero` | `JoltConstraints/Soundness/Layer7/TerminationStore.lean:410` | New public shared zero-word theorem for byte addresses from the output start to before ordinary RAM. |
| `initialRamWord_termination_zero` | `JoltConstraints/Soundness/Layer7/TerminationStore.lean:453` | Original statement unchanged; proof now applies the shared theorem at the termination word. |
| `first_address_row_starts` | `JoltConstraints/Soundness/Layer6/BoundaryStart.lean:17` | New private bytecode helper for a first row at its address in expanded bytecode. |
| `first_row_of_entry_slot` | `JoltConstraints/Soundness/Layer6/BoundaryStart.lean:63` | Original statement unchanged; proof delegates its source-start step to the new helper. |
| `initial_state_empty_outputs_and_input_bound` | `JoltConstraints/Soundness/Layer6/BoundaryStart.lean:119` | New private helper extracting empty output, false panic, and the input-size check from initialization. |
| `initialized_device_words` | `JoltConstraints/Soundness/Layer6/BoundaryStart.lean:152` | Original statement unchanged and now proved using the rounded input bound and shared zero-word theorem. |
| `empty_run_ram_word` | `JoltConstraints/Soundness/Layer6/BoundaryStart.lean:216` | Original statement unchanged; final-RAM unfolding now occurs once before the panic case split. |

`context_initial_termination_zero` keeps its statement and proof; its private termination-word helper now uses the generalized theorem.
No approved statement, core definition, or theorem premise changed, and no `bv_decide` use or proof limit was added.
No new or changed proof took more than ten seconds; the five new or changed `BoundaryStart.lean` proofs each elaborated in under 0.21 seconds.
`lake build JoltConstraints` passed with 8806 jobs, and `git diff --check` passed.
`#print axioms JoltInstance.boundaryState_empty` reports `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
I edited only `BoundaryStart.lean`, `TerminationStore.lean`, `layout_facts.lean`, and this report, and made no commit.
