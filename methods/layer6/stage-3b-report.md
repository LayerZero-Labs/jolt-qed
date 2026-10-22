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
