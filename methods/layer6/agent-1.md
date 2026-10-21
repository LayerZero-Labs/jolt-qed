# Agent 1: restructuring, interfaces, induction and integration

Read `README.md` in this directory first, then `AGENTS.md`.
You are the lead: you set up the interfaces the other four agents build against, prove the induction, and merge everyone's work.
Work in a worktree under `/Users/ari.biswas/Lean/` on a branch `layer6-agent-1` from the head of `feat/soundness`.

## Phase 0: restructure and stage, then stop for Ari's review

### 0.1 Files the proof can import

`Layer6/ExecutionPrefix.lean` is imported by the Layer 7 files, so it cannot import their helpers.
Restructure, changing no statement:

- Move `RepresentsRows`, `RepresentsPrefix` and `Represents` into a new `Layer6/Represents.lean`.
- Move the single-row witness and model facts about JAL, JALR and branch rows into a new `Layer6/ControlRows.lean`, make them public, and remove duplicates.
  From `Layer7/StallSuffix.lean`:
  - `selected_represented_row`, `selected_operand_register`, `register_unchanged_of_no_write`;
  - the JAL facts: `stall_jal_lookup_target`, `stall_jal_next_target`, `stall_jal_exec_target`;
  - the branch facts: `stall_branch_control_flags`, `stall_branch_table_decision`, `stall_branch_lookup_decision`, `stall_branch_controls_succ`;
  - the JALR facts: `selected_jalr_lookup_target`, `selected_jalr_next_target`, `tape_jalr_target`;
  - `selected_jump_link_write_value`, `branch_instruction_of_flag`;
  - the run-row PC facts: `untrusted_row_pc`, `untrusted_row_next_pc`, `noncontrol_next_pc`.

  From `Layer7/LastJump.lean`: `jump_instruction_of_flag`.
  Delete LastJump's private copies of `selected_represented_row` and `branch_instruction_of_flag`.
  Rename the `stall_` facts that are not about stalls (for example `jal_lookup_target`, `branch_lookup_decision`).
- Move `UntrustedAnswerRun.truncate` and its lemmas, `honestTracerAdviceAtStepN_extract` and `soundness_prefix_next_step` from `Layer7/TerminationStore.lean` into a new `Layer6/RunPrefix.lean`.
- Move `soundness_execution_prefix_agreement` into a new `Layer6/PrefixAgreement.lean`, which may import the Layer 5 step lemmas, `BytecodePC.lean` and the new shared files.
  `Soundness/TopLevel.lean` imports it; the Layer 7 files import only `Represents.lean`, `ControlRows.lean` and `RunPrefix.lean`.
  Delete `ExecutionPrefix.lean` if it ends up empty.

Build after this step alone, and commit it, so the other agents start from a working restructured tree.

### 0.2 Register agreement over live registers (decision for Ari)

Stage, in `Layer5/Registers.lean`, a structure `RegisterAgreementOn (live : Fin 128 → Prop) witness t state`: `AllRegistersPresent` plus agreement at every live register.
Define `RegisterAgreement` as the case where every register is live, so every existing statement keeps its meaning.
Generalize the helper API to the live form, with the existing names as the full case:
- `.read` and `.rs1Value`/`.rs2Value` require the read register to be live;
- `.write` makes the destination live;
- `.noWrite` keeps the live set;
- `.advance_pc` and `.initial` carry over.

State how HostIO fits: its step makes temporary 40 not live.
`ExpansionFacts.expand_temps_ok` (temporaries 40-47 are written before they are read inside each expansion) makes the temporaries irrelevant at every source boundary.

Before staging, measure the porting cost and put it in your report: how many of the 77 step lemmas use agreement only through this API.
Then give Ari the comparison:

- (A, recommended) live-register agreement, with the existing lemmas ported (agent 5);
- (B) keeping full agreement and handling temporary 40 locally, which fails when HostIO is followed by rows that do not write register 40, or by a second HostIO.

Ari decides; do not start the port.

### 0.3 The induction invariant

Stage, in `PrefixAgreement.lean`, a structure `PrefixState witness context n run` for a run whose rows are the witness's first `n` cycles:

- `run` is an `UntrustedAnswerRun` with `run.rows.size = n` and the context's bytecode;
- every retained cycle is real, and no retained row before the last is a stable stall;
- `RepresentsRows` holds for the retained rows;
- runtime advice is honest for every row of every completed source instruction.
  Rows of the instruction still in progress are exempt, because a VirtualAdvice row's honesty follows only from the asserts after it (agent 3).
- The endpoint comparison at cycle `n`:
  - register agreement on the live set;
  - `OrdinaryRamAgreement` between `witness.RamVal · n` (or `RamValFinal` when `n` is the last cycle) and the run's state;
  - the device-word agreement agent 4 defines; stage its name and type in Phase 0;
  - the run's last post-state, or the initial state when `n = 0`.
- When cycle `n` is real and not past a stall: the slot selected at cycle `n` is the run's next row (`UntrustedAnswerRun.NextStep`, `Layer5/MemoryAccessRestriction.lean:29`), and the prepared pre-state has the Sail PC at that row's address.
  AUIPC, JAL, JALR and the branches need that PC fact.

### 0.4 The step interface and the dispatcher

Stage one statement shape, `RowStep`, that every row family satisfies:

- Inputs: `PrefixState n run`, cycle `n` real, the run not ended by a stable stall, and the selected row's instruction in the family.
- Output: a run with `n + 1` rows extending `run` and `PrefixState (n + 1)`.

Stage one `RowStep` lemma per family, with `sorry`, in the file of the agent who owns it:

- Agent 2: `Layer5/Jalr.lean` and `Layer5/Branch.lean`.
- Agent 3: `Layer5/AdviceLoad.lean` and `Layer5/Advice.lean`.
- Agent 4: `Layer5/LoadDoubleword.lean`, `Layer5/StoreDoubleword.lean`, and the SC families' files.
- Agent 5: an adapter file per existing family, such as `Layer5/Adapters/Arithmetic.lean`.

Then prove the dispatcher in `PrefixAgreement.lean`: split on the selected row's instruction and apply the matching lemma.

Agent 3 also needs a completion hook, to establish honest advice when a division expansion ends.
Stage it as `division_advice_honest`: for a run whose last row ends a DIV, DIVU, DIVW, DIVUW, REM, REMU, REMW or REMUW expansion, every advice row of that expansion is honest.
The invariant uses it at source boundaries.

### 0.5 Initialization, cut and source boundary

Stage with `sorry`:

- `prefixState_zero`: the empty run satisfies `PrefixState 0`.
  It uses `RegisterAgreement.initial`, `OrdinaryRamAgreement.initial` (`Layer5/RamInitialization.lean:107`), agent 4's initial device agreement, and `selected_entry` (`BytecodePC.lean:22`).
- `prefix_source_boundary`: when a row ends its source instruction and the next cycle is real, the next selected slot is the first row of the source instruction at the run's nextPC.
  It uses NextUnexpandedPC and the PC constraints, `selected_interior_predecessor` (`BytecodePC.lean:101`) and the PC map.
  This is the open "source-boundary transition" of Layer 6.
- `prefix_cut`: from `PrefixState n run` and one of the three stopping cases, the conclusion of `soundness_execution_prefix_agreement`.
  `cutRam` comes from the RAM and device agreement at `n`.

Then prove `soundness_execution_prefix_agreement` from these by induction on `n`.
Stop at the first stable stall, the first padding cycle, or the last cycle.

### 0.6 Report and stop

Build, run the axiom audit of `JoltInstance.soundness`, and stop.
Its `sorryAx` must come only through the staged statements and helpers C and D.

Write the report to `methods/layer6/phase0_report.md`, containing:
- every staged statement, with its owner;
- the porting count;
- the A/B comparison;
- the commit hash the other agents branch from.

## Phase 1: your own proofs, in parallel with the others

After Ari approves Phase 0, prove `prefixState_zero`, `prefix_source_boundary` and `prefix_cut`, and the invariant bookkeeping inside the dispatcher.
Agent 4 owns the device part of `prefixState_zero`.
Use `padding_from`, `selected_next_of_remaining` and `selected_interior_predecessor` (`BytecodePC.lean`), and the Layer 7 cut lemmas where they apply.

## Phase 2: integration

Merge the agents' branches into `layer6-agent-1` in this order: agent 5, then agents 2, 3 and 4.
Agent 5 changes the register-agreement form the others' adapters use.
After each merge, build and resolve conflicts without changing any approved statement.
Then:
- merge `layer6-agent-1` into `feat/soundness`;
- build;
- run the axiom audit for `JoltInstance.soundness`, whose only `sorryAx` must come through helpers C and D;
- update "Proofs owed" in `JoltConstraints/model_review.md` and the status lines in `methods/soundness.md`.

## Files you own

`Layer6/Represents.lean`, `Layer6/ControlRows.lean`, `Layer6/RunPrefix.lean`, `Layer6/PrefixAgreement.lean`, `Layer6/ExecutionPrefix.lean`, `Layer6/BytecodePC.lean`, `Layer5/Registers.lean`, `Soundness/TopLevel.lean`.
You also own the import lines of the Layer 7 files, and the moves of declarations out of them.
