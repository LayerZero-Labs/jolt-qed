# Layer 6 stage 2: audit stop

Stopped before implementation because the plan contains a false claim.
Read `AGENTS.md`, `methods/layer6/stage-1-report.md` and `methods/layer6/stage-2.md` in that order.
The checkout is on `feat/soundness` and was clean when this task began.

## Incorrect claim

`methods/layer6/stage-2.md:21` says:

> every restriction is stated over `UntrustedAnswerRun.NextStep`, which needs honest advice.

The second part is correct: `NextStep.honestRuntimeAdvice` requires honest advice for every retained row (`JoltConstraints/Soundness/Layer5/MemoryAccessRestriction.lean:33`).
The universal claim about restrictions is false.
Three fields of `JoltInstance.TemporaryRestrictions` are not stated over `NextStep`:

| Restriction field | Actual definition | Source |
|---|---|---|
| `noStoreConditional` | Every source row in `program.instructions` must be neither SC.W nor SC.D, including unreachable rows | `JoltConstraints/Soundness/Assumptions.lean:45`, field at line 81 |
| `noMaxLengthTrace` | Every completed `UntrustedAnswerTrace` has a real-row count different from the largest permitted power-of-two witness domain | `JoltConstraints/Soundness/Assumptions.lean:62`, field at line 99 |
| `claimsNoPanic` | `joltInstance.panic = false` | `JoltConstraints/Soundness/Layer5/PanicRestriction.lean:88`, field in `Assumptions.lean:113` |

For example, `NoStoreConditional` rules out an unreachable SC.W source row without referring to an execution prefix, a next row or advice.
`ClaimsNoPanic` checks the instance's claimed panic bit directly.
These are counterexamples to the stated classification of the restriction bundle.

## Proposed correction

Narrow the claim to the four operational restrictions that actually take `NextStep`:

- `TracerAddressChecks`, in `JoltConstraints/Soundness/Layer5/MemoryAccessRestriction.lean:86`.
- `HostCallsSucceed`, in `JoltConstraints/Soundness/Layer5/HostCallRestriction.lean:33`.
- `TerminationThenStall`, in `JoltConstraints/Soundness/Layer5/TerminationRestriction.lean:59`.
- `PanicStoresOne`, in `JoltConstraints/Soundness/Layer5/PanicRestriction.lean:63`.

Their instruction cases concern LD/SD, HostIO, or termination-related JAL/JALR behavior; their other cases return `True`.
The intended rationale can distinguish these operational restrictions from the three program, completed-trace and public-claim restrictions above.
This is a scope error in the plan's explanation, not a demonstrated counterexample to the proposed division-block split or the approved `boundary_step` statement.
No change to the restriction definitions is proposed.

The plan was not amended or silently reinterpreted because the task explicitly requires stopping if any claim is wrong.
The remaining Stage 2 claims and proposed statements have not all been certified; the audit must resume after this correction.

## Work and validation

No Lean declaration, theorem statement, proof, invariant, restriction or existing documentation was changed.
No new declarations were staged, so there are no declaration timings or new `bv_decide` uses to report.
No build or axiom audit was run because implementation stopped during the required preliminary audit.
The Stage 1 validation results remain historical results, not a new Stage 2 check.
Only this report was added.
No commit was made.

## Resumed audit after the plan correction

The initial audit stop above is preserved unchanged.
Ari corrected the restriction classification and authorized resuming the audit and implementing the unchanged design.
I reread the amended plan and checked the remaining claims before editing Lean files.
No further blocking mismatch was found.

- The corrected classification agrees with all seven fields of `TemporaryRestrictions` and their definitions cited above.
- `nonterminal_at_last_cycle_impossible` and `nonterminal_before_padding_impossible` in `JoltConstraints/Soundness/Layer7/LastJump.lean:350,401` exclude a selected interior row at the final cycle or immediately before padding under their stated selection, domain and expansion hypotheses.
  `selected_next_of_remaining` in `Layer6/BytecodePC.lean:67` gives the consecutive next slot.
  These are facts about selected, expanded bytecode rows, not arbitrary uncertified trace rows.
- All eight generated division programs contain exactly one `VirtualAdvice` in the nonzero-destination case and only an ADDI no-op in the zero-destination case.
  Their rows contain no load, store, jump, branch, HostIO or tape read.
  Checked the eight definitions in `JoltBytecode/JoltISA/ExpansionsAutomated.lean`, the `SourceInstruction.expand` dispatch in `JoltConstraints/expansions.lean`, and `ExpandedSource.ofPureProgram` in `JoltConstraints/expansion_helpers.lean`.
  A search of the generated and handwritten expansion definitions found the eight generated advice sites and no additional advice-emitting expansion.
- Checked the corresponding pinned expander functions with `git show 5def437f:<path>`: `jolt/crates/jolt-program/src/expand/division/{div,divu,divw,divuw,rem,remu,remw,remuw}.rs` and `shared.rs` (`expand_unsigned_word_div_rem`).
  Checked the zero-destination rewrite in `jolt/crates/jolt-program/src/expand/mod.rs` (`expand_source_instruction_with_provider`) and the guest custom decoder in `jolt/crates/jolt-program/src/image/decode.rs` (`decode_custom`).
  The modeled `JoltCustomInstruction` has no source-level `VirtualAdvice`; advice tape loads are different instructions.
- `ExpansionFacts.expand_temps_ok` in `JoltConstraints/expansion_facts.lean:916` proves the first-access property defined in `expansion_temp_liveness.lean` for every supported expansion.
  The property means that a temporary is written before its first read, not that every temporary must be written by every expansion.
  This supports ignoring incoming temporary values and retaining agreement once a temporary has been written.
- `runtimeAdvice_agrees_of_noAdvice` in `Layer5/RuntimeAdvice.lean:25` proves that an ordinary row's recorded and honest advice are both absent.
  Together with the existing prefix's honest-advice hypothesis and the next-state linkage, this supports `NextStep` before every row in the ordinary case.
  Advice absence alone does not supply linkage or the no-earlier-stop certificate; the invariant carries those separately.
- Checked every division family's `*Program_sound` and `*Program_concrete` signature under `JoltBytecode/InstructionEquivalence/Instructions/ALUAdviceFamily/`.
  DIV, DIVU and DIVW prove advice uniqueness; DIVUW and the four remainder families prove the final Sail state without requiring unique advice.
  All eight concrete-execution results use honest advice and permit arbitrary initial instruction-temporary values.
  These results do not by themselves prove preservation of the rest of `SailJoltState`; the block proof must also establish the register/device frame facts described below.
- `Jal.lean` retains an explicit no-wrap premise when comparing the field return address with a 64-bit word.
  `expansion_finish` retains the soundness assumptions for the source-boundary transition, including `pcNoWrap`.

## Implemented declarations and timings

All declarations below are in `JoltConstraints/Soundness/Layer6/PrefixAgreement.lean` and namespace `JoltInstance`.
Only `boundary_step` was proved; the four requested pieces remain staged with named `sorry` bodies.
The four auxiliary definitions name expressions shared by the invariant and staged statements and have no additional proof obligations.

| Declaration | Line | Status | Command elaboration | Proof elaboration |
|---|---|---|---|---|
| `expansionRowCount` | 81 | New definition | 0.012 s | — |
| `ExpansionHasAdvice` | 89 | New definition | 0.002 s | — |
| `ExpansionLive` | 99 | New definition | 0.003 s | — |
| `RunExtends` | 112 | New definition | 0.001 s | — |
| `ExpansionState` | 130 | New structure | 0.448 s | — |
| `expansion_start` | 189 | Staged | 0.005 s | 0.0005 s |
| `row_step` | 205 | Staged | 0.093 s | 0.0006 s |
| `division_block` | 236 | Staged | 0.082 s | 0.0006 s |
| `expansion_finish` | 261 | Staged | 0.043 s | 0.0004 s |
| `boundary_step` | 283 | Proved from the four staged pieces | 0.006 s | 0.236 s |

Timings come from `lake env lean -j1 -Dtrace.Elab.async=true -Dtrace.profiler=true -Dtrace.profiler.threshold=0 JoltConstraints/Soundness/Layer6/PrefixAgreement.lean`.
The staged proof timings measure elaboration of `sorry`, not completed proofs.
No new or changed proof took more than ten seconds.

`boundary_step` opens the selected source, splits on `ExpansionHasAdvice`, invokes `division_block` in the advice case, and otherwise inducts on the remaining row count using `row_step`.
Both paths produce exactly the source's row count of additional rows, then call `expansion_finish`.
The row count is the first row's remaining stamp plus one, so it is positive and establishes the target's strict progress conclusion.
The proof body contains no `sorry`.

## Invariant and representation choices

`first` is a `Fin context.bytecode.size`, allowing it to remain fixed as the run grows.
The context and each run expand the same program, so their bytecode equality is derivable from their existing certificates.
The structure contains exactly the information requested by the plan, with the layout clause separated into `starts`, `done_le`, `retained`, `ordered` and `priorBoundary`.

| Fields | Honest-witness justification and example |
|---|---|
| `represents`, `real`, `noEarlierStop`, `terminationWord` | These retain the corresponding `BoundaryState` formulas unchanged, so an actual unfinished SLL prefix still has represented observations, real rows, no earlier stall and zero termination RAM if no store has touched it |
| `starts`, `done_le`, `retained`, `ordered` | The current source begins at `first`, and its first `done` rows occupy the suffix of the run in order; after SLL's first row, `done = 1` and that suffix selects `first` |
| `priorBoundary` | The prefix before the current source is empty or ends at a completed source, as when a REM follows a completed ADDI |
| `registers` | Persistent registers always agree, and a temporary written in the unfinished source also agrees; temporary 40 becomes live after SLL's first row and becomes irrelevant when the source finishes |
| `next` | An unfinished source has another real witness cycle selecting slot `first + done + 1`, with an actual next row and prepared state satisfying the entry/linkage clause of `NextStep`; SLL's second cycle selects its MUL row |
| `notStopped` | Before the first row this follows from the incoming hypothesis, and inside the source a nonterminal row cannot be a stable stall; the final row may stall because this field is then conditional on a false inequality |

`ExpansionState` has no honest-advice field.
`ExpansionLive` tests bytecode destinations among the first `done` rows; `ordered`, `retained` and bytecode equality identify them with the executed suffix.
At the full row count its temporary branch is disabled, permitting REM's witness temporary 40 to hold 5 while the honest run's holds 0.
The `next` field writes out exactly the entry/linkage clause of `NextStep`, retaining `source_is_compressed` and the final-row stall condition without assuming honest advice.

`RunExtends` equates the old row array with the initial segment of the new row array after identifying bytecode types.
It preserves recorded runtime advice and pre/post states of every old row; it does not assert equality of unused answer-function entries.
`row_step` and `division_block` separately state their exact row-count increments, so extension is an actual conclusion rather than an informal intent.
No extension equation was added to the already approved `boundary_step` statement.

## Staged statements and hypotheses

`expansion_start` takes the current boundary, the real next cycle and absence of a final stable stall, and returns a source index with `ExpansionState` at `done = 0` on the same run.
It requires no additional field, constraint or soundness-assumption premises beyond the context and incoming boundary data.
The boundary's `ready` field supplies the selected first row and prepared state, and its remaining fields specialize to the empty suffix.
For example, before a nonzero-destination SLL, temporary 40 is not yet live and the next instruction is VirtualPow2.

`row_step` takes the target's field, soundness assumptions, temporary restrictions, context and equations, plus an unfinished expansion state, honest advice for the existing run and the absence of an advice row in the entire source.
It returns a run retaining the old rows, one additional row, the state at `done + 1`, and honest advice throughout.
For example, executing SLL's VirtualPow2 row initializes temporary 40 and makes it available to the subsequent MUL row.
The first-access property supplies the required operand agreement without demanding agreement on incoming dead temporaries.
The four operational restrictions can be applied because honest advice and the invariant's entry/linkage and stopping conditions supply `NextStep`.
The no-advice premise is essential: REM with quotient 5 cannot satisfy a rowwise honest execution whose newly written, live temporary 40 must equal zero.

`division_block` takes the field condition, context and equations, an expansion state at `done = 0`, honest advice for the earlier run, and existence of an advice row in this source.
It returns an extension by the full row count, a completed expansion state and honest advice for every row.
It needs no execution-step restrictions for this arithmetic-only block, and the source-boundary PC comparison is left to `expansion_finish`.
The proposed later proof is supported by these hypotheses as follows:

1. Use source-start and expansion certificates to identify one of the eight division programs with a nonzero destination.
2. Reconstruct the witness's block execution using its advice and the Layer 5 row semantics, tracking only live registers so incoming temporary values need not be reconstructed.
3. Apply the matching `*Program_sound` theorem, obtaining either honest advice itself or the correct final Sail state.
4. Apply `*Program_concrete` from the same prepared starting state to construct the returned honest block.
5. Prove the additional frame facts from the block's arithmetic/assertion instructions, whose writes target instruction temporaries and the architectural destination, and compare represented operands, PCs and unchanged RAM.
6. Restore only persistent-register agreement at the completed boundary and preserve the earlier rows and their honest advice.

For `rem a0, a1, zero` with `a1 = 7`, the witness can use quotient 5 and the returned run uses quotient 0.
`remProgram_sound` and `remProgram_concrete` both give the final architectural result `a0 = 7`.
The nine rows have identical PCs and RAM observations, their architectural source operands agree, and temporary reads are exempt under `RepresentsRows`.
The returned state is completed, so no equality is required for the differing quotient temporary.
The witness-advice execution is an intermediate construction; the conclusion appends honest rows to the original run.

`expansion_finish` takes the field condition, soundness assumptions, context and equations, a completed expansion state and honest advice for every row, and concludes `BoundaryState` for the same run.
The layout identifies the final terminal row, completed liveness drops temporary agreement, and the remaining agreement fields transfer directly.
The open obligation is establishing readiness across the source boundary from constraints and actual execution with the retained no-wrap assumption.
For example, after an uncompressed ADDI at 0x1000, a real following cycle selects the instruction at 0x1004 with its own source compression flag used to prepare the pre-state.

All hypotheses of the four staged statements are supplied by the compiled `boundary_step` caller.
No approved theorem acquired a new premise.

## Checks before staging

Every state is attached to an initialized, executing, linked `UntrustedAnswerRun`, and suffix/boundary assertions use actual row membership.
No conclusion about an instruction is inferred from an arbitrary standalone post-state.
`row_step` and `expansion_finish` retain `assumptions.pcNoWrap` through the soundness-assumptions bundle for the field/word comparisons they may need.
The next-state clause uses `source_is_compressed`; it does not substitute an interior row's compression flag.
Source identification and any all-rows-at-an-address reasoning must use successful preprocessing and its PC-map uniqueness facts available from the context.
No new axiom, restriction, machine-semantics definition or language condition was added.

## Validation and scope

`lake build JoltConstraints` passed with 8800 jobs.
`git diff --check` passed before appending this report.
A textual comparison with the saved pre-task file confirmed that `BoundaryState`, `boundaryState_empty`, the `boundary_step` statement and the entire `soundness_execution_prefix_agreement` declaration are unchanged.
The four new statements remain unproved, and the original empty-boundary gap remains untouched.
No new `bv_decide`, `native_decide`, `decide +kernel` or raised limit was used.

`#print axioms JoltInstance.soundness` retains the existing axiom names: `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound` and `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5`.
`boundary_step` reports the first five, without a native bit-vector axiom dependency.
A transitive constant-dependency traversal checked that the exact reachable declarations directly using `sorryAx` are:

- `JoltInstance.boundaryState_empty`.
- `JoltInstance.expansion_start`.
- `JoltInstance.row_step`.
- `JoltInstance.division_block`.
- `JoltInstance.expansion_finish`.
- `JoltInstance.soundness_prover_accepts` (C).
- `JoltInstance.soundness_spoil_asserts_pass` (D).

The audit script is `/private/tmp/layer6-stage2-axioms.lean`; build, profiling and axiom logs are `/private/tmp/layer6-stage2-{build,profile,axioms}.log`.
The “Proofs owed” table in `JoltConstraints/model_review.md` and the current status in `methods/soundness.md` now track these gaps.
The user's correction to `methods/layer6/stage-2.md` was preserved without further edits.
Apart from naming shared expressions and spelling out row extension, the corrected plan required no design change.
Work remains uncommitted on `feat/soundness`, and stops after this report for review of the four staged statements.
