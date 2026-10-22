# Layer 6 stage 1 report

## Audit findings

Read `AGENTS.md` and checked every design claim and requested statement in `methods/layer6/stage-1.md` before editing.
No blocking mismatch was found.
The two boundary obligations are staged statements, not completed proofs of source-instruction reconstruction.

- The prefix theorem's only caller is helper A in `JoltConstraints/Soundness/TopLevel.lean`, now line 43.
  Layer 7 imports the representation definitions from `ExecutionPrefix.lean`; moving only the theorem to `PrefixAgreement.lean` introduces no import cycle.
- The REM counterexample is valid: when the divisor is zero, every 64-bit quotient passes the expansion's checks while the honest tracer supplies zero.
  Checked `JoltBytecode/JoltISA/ExpansionsAutomated.lean:170`, `JoltBytecode/InstructionEquivalence/Instructions/ALUAdviceFamily/Rem.lean:102`, and the pinned sources `jolt/crates/jolt-program/src/expand/division/rem.rs:15-24`, `jolt/tracer/src/instruction/rem.rs:44-58` and `jolt/tracer/src/instruction/virtual_assert_valid_unsigned_remainder.rs:23-25` at `5def437f`, using `git show`.
  Architectural operands and the final result agree even when quotient temporary 40 differs.
- `ExpansionFacts.expand_temps_ok` (`JoltConstraints/expansion_facts.lean:916`) proves the `tempsReadAfterWrite` property (`JoltConstraints/expansion_temp_liveness.lean:80`) for every supported expansion.
  Thus incoming values of temporaries 40–47 are dead at source boundaries, rather than necessarily equal or zero there.
  This agrees with Jolt's expansion allocator, `jolt/crates/jolt-program/src/expand/allocator.rs:133-143` at `5def437f`.
- `last_row_terminal` (`JoltConstraints/Soundness/Layer7/LastJump.lean:455`) proves terminality at padding or the last witness cycle under its selected-row and boundary hypotheses.
  Its public caller `soundness_last_row_is_jump` at line 612 supplies those hypotheses from represented rows.
  `TraceRow.StableStall` (`JoltConstraints/honest_trace.lean:36`) explicitly includes terminality.
  These facts support complete-source cuts; they are not claims about an uncertified standalone row.
- Honest advice is an explicit construction obligation, not a consequence of terminality alone.
  `honestTracerAdviceAtStepN` (`JoltConstraints/honest_trace.lean:194`) computes advice from the expansion's starting state, and `honestTracerAdviceAtStepN_extract` (`JoltConstraints/Soundness/Layer7/TerminationStore.lean:234`) confirms that later rows do not change an earlier row's honest advice.
  Jolt's tracer supplies and patches these values in `jolt/tracer/src/instruction/mod.rs:210-238` at `5def437f`.
  The staged invariant retains the plan's separate `honestAdvice` field and requires `NextStep` in full.
- The termination-word exception needs the separate zero-before-store invariant.
  Jolt's device loads zero there and ignores termination stores (`jolt/common/src/jolt_device.rs:146-150,175-180` at `5def437f`), while the prover's initial RAM starts at zero and overlays program, advice and input data (`jolt/crates/jolt-witness/src/backend/trace/ram.rs:80-129`).
  The model has the same behavior in `JoltBytecode/JoltISA/JoltDevice.lean:203` and `JoltConstraints/witness_helpers/ram_state.lean:68`; `context_initial_termination_zero` in `Layer7/TerminationStore.lean:483` already establishes the initial zero fact.
- The next selected slot is row index plus one, as in `host_call_selected_step` (`JoltConstraints/Soundness/Layer5/HostCallRegisterFrame.lean:25`).
  `UntrustedAnswerRun.NextStep` (`Layer5/MemoryAccessRestriction.lean:29`) carries honest advice, no earlier stop and the entry/linkage rule, including `source_is_compressed`.
  `selected_entry` (`Layer6/BytecodePC.lean:23`) supports the empty boundary; readiness is conditional on a real next cycle, so padding slot zero does not require a nonexistent bytecode row.

## Implemented declarations

Only the outer induction was proved.
The declaration timings below come from Lean's command and asynchronous proof traces, with `-j1 -Dtrace.Elab.async=true -Dtrace.profiler=true -Dtrace.profiler.threshold=0`.
The staged proof times measure elaboration of `sorry`, not proofs of the obligations.

| Declaration | File and line | Status | Command elaboration | Proof elaboration |
|---|---|---|---|---|
| `JoltConstraints.Soundness.RegisterAgreementOn` | `JoltConstraints/Soundness/Layer5/Registers.lean:34` | New structure | 0.016 s | — |
| `JoltInstance.BoundaryState` | `JoltConstraints/Soundness/Layer6/PrefixAgreement.lean:28` | New structure with exactly eight fields | 0.109 s | — |
| `JoltInstance.boundaryState_empty` | `JoltConstraints/Soundness/Layer6/PrefixAgreement.lean:66` | Staged with `sorry` | 0.003 s | 0.0005 s |
| `JoltInstance.boundary_step` | `JoltConstraints/Soundness/Layer6/PrefixAgreement.lean:82` | Staged with `sorry` | 0.007 s | 0.0005 s |
| `JoltInstance.soundness_execution_prefix_agreement` | `JoltConstraints/Soundness/Layer6/PrefixAgreement.lean:103` | Moved with unchanged statement; proved from the two staged lemmas | 0.052 s | 0.058 s |

No new or changed proof took more than ten seconds.
The prefix proof uses strong induction on `params.traceLength - run.rows.size`.
It returns the current run at any of the three cut conditions; otherwise selected-bytecode flags establish that the next cycle is real, and `boundary_step` supplies a larger bounded run.
The original theorem body contains no `sorry`.

`TopLevel.lean:14` now imports `PrefixAgreement.lean` explicitly.
`ExecutionPrefix.lean` retains its original definitions and structures.
The current-status paragraph in `methods/soundness.md` and the “Proofs owed” table in `JoltConstraints/model_review.md` now track the two staged boundary lemmas.
The preexisting edit to “Running the Layer 6 agents” and the untracked stage plan were preserved.

## Invariant audit

These explanations describe why the fields hold at complete-source boundaries of an honest witness and what the staged reconstruction must establish for a constraint-satisfying witness.

| Field | Justification and example |
|---|---|
| `represents` | The retained execution supplies the witness PC, eligible operands and RAM addresses, and the RAM history gives the state after the retained rows outside the synthetic termination word; after `rem a0, a1, zero`, architectural observations agree even if temporary 40 differs |
| `real` | Retained rows execute actual bytecode rather than padding; all nine rows of the REM example are real |
| `noEarlierStop` | The reconstructed prefix stops at its first stable stall; a self-looping `jal x0, 0` may be the last row but cannot have another retained row after it |
| `honestAdvice` | Each expansion is executed with advice computed from its starting state; the REM example records quotient zero, independently of witness quotient five |
| `atBoundary` | Every induction step completes its source instruction, and a stable stall is terminal by definition; the ninth REM row has remaining count zero |
| `registers` | At the next cycle the register table is the previous row's post-state on persistent registers, with Sail register presence retained; REM agrees on `a0` while temporary 40 may differ, and preparing the next PC preserves source-register values |
| `terminationWord` | Initially the termination word is zero, and without any executed store touching it its RAM history stays zero; a load before the SDK's termination store therefore reads zero |
| `ready` | Entry selection or the preceding source's next PC identifies the next selected source row, with honest advice and no earlier stop supplied by the invariant; after an ordinary ADDI, the next real cycle selects the following instruction and uses its source compression flag to prepare the state |

`terminationWord` quantifies over `address : Fin params.ramSize` with an equality to the exact index used by `RepresentsPrefix.cutRam`.
This states the required column value without introducing an extra RAM-bounds field or a new premise to soundness.
`ready` and `boundary_step` express “the last row is not a stable stall” as `∀ last ∈ run.rows.back?, ¬ last.StableStall`, which also handles the empty run.

## Staged-statement audit

`boundaryState_empty` takes only `joltField`, the witness, context and constraint equations.
It returns an initialized `UntrustedAnswerRun` with `rows = #[]` and the boundary invariant.
The run's initialization certificate identifies its initial state with the state supplied by `context.initialized`; register and RAM initialization establish agreement, retained-row conditions are vacuous, and a real entry cycle supplies readiness.
For example, an entry ADDI begins with the zero register table and the loaded program/input RAM image before any row executes.
Returning the empty run existentially avoids adding and proving a separate empty-run constructor in this stage.

`boundary_step` retains the target's field, instance, soundness assumptions, temporary restrictions, private inputs, witness, context and equations, and adds only the induction data: the current run, its `BoundaryState`, a strict cycle bound, a real next cycle and no final stable stall.
Every added hypothesis is available to its caller, as the compiled outer induction demonstrates.
For an honest witness, executing the next complete source instruction produces a strictly larger boundary prefix; for example, the REM example adds nine rows, uses honest quotient zero and restores persistent-register agreement.
For an arbitrary constraint-satisfying witness, establishing execution and all eight fields remains the staged obligation.
The conclusion deliberately requires progress and the invariant, without an array-extension equation, as the plan permits.

The four “Before staging a statement” checks are respected.
Both statements use an initialized, executing, linked `UntrustedAnswerRun`; last-row conditions quantify actual membership in `rows.back?`.
`boundary_step` retains `assumptions.pcNoWrap` through the unchanged assumptions bundle for later field/word PC comparisons.
`NextStep` retains `source_is_compressed`, rather than using an interior row's compression flag.
The context's successful preprocessing and expansion certificates supply the accepted PC map and its address-uniqueness facts when later proofs need them.
The outer induction itself performs only natural-number row-count arithmetic and selected-bytecode flag reasoning.

## Scope and validation

There was no substantive deviation from the plan.
No existing theorem gained a hypothesis, and no restriction, language definition, `NextStep` field or protected representation definition changed.
A textual check against `HEAD` confirmed the moved target statement is identical and the protected representation declarations are unchanged.
A separate comparison confirmed that removing the new `RegisterAgreementOn` block restores `Registers.lean` exactly.
No new `bv_decide`, `native_decide`, `decide +kernel`, raised limit or other axiom was introduced.

`lake build JoltConstraints` passed with 8800 jobs.
`git diff --check` passed before this report was written.
The axiom audit used `#print axioms JoltInstance.soundness` and a transitive constant-dependency traversal that checks the exact set of reachable declarations directly using `sorryAx`.
That set is:

- `JoltInstance.boundaryState_empty`.
- `JoltInstance.boundary_step`.
- `JoltInstance.soundness_prover_accepts` (C).
- `JoltInstance.soundness_spoil_asserts_pass` (D).

`JoltInstance.soundness` reports the same axiom names as before: `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound` and the existing `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5`.
The prefix theorem reports the first five and has no native bit-vector axiom dependency.
Build, profiling and axiom logs are in `/private/tmp/layer6-stage1-*.log`; the dependency-check script is `/private/tmp/layer6-stage1-axioms.lean`.

Work remains uncommitted on `feat/soundness`.
Stage 1 stops here for review of the two staged lemmas.
