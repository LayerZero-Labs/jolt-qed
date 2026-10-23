# Helper D report

Work was done on `feat/soundness` in `/Users/ari.biswas/Lean/jolt-qed-public` on 2026-10-23.
Helper D now follows from the shared assertion constraint proof and one staged source-expansion obligation.
It is not yet free of `sorryAx`.
I stopped under the plan's instruction to stage a missing fact that needs further proof development, and under `AGENTS.md`'s requirement to have its caller checked before proving it.
No commit was made.

## Claims checked before editing

I read `AGENTS.md`, `methods/layer6/reuse.md`, `methods/layer7/helper-d.md`, and the relevant status and proof obligations in `methods/soundness.md` and `JoltConstraints/model_review.md`.
The Jolt source audit used `git show` and `git grep` at `5def437f21a0006e13c063a03f0b5a7c9b93cd6f`, rather than the checked-out Jolt HEAD.
The plan's mathematical claims hold for the modeled source instruction set.

| Claim | Checked evidence |
|---|---|
| Helper D is open, and L requires passing spoil asserts | The original `Soundness/TopLevel.lean` D body was `sorry`; `JoltConstraints/language.lean:24` requires `trace.SpoilAssertsPass` |
| A spoil assert has a nonzero immediate and requires equal pre-state operands | `JoltConstraints/honest_trace.lean:322`, `Trace.SpoilAssertsPass` |
| Successful tracing alone does not establish equality | At the pin, `jolt/tracer/src/instruction/virtual_assert_eq.rs`, `VirtualAssertEQ::exec`, warns and continues when a nonzero-immediate assertion has unequal operands |
| Representation excludes instruction-temporary operands | `Soundness/Layer6/ExecutionPrefix.lean:29`, `RepresentsRows.rs1` and `.rs2`; temporaries are addresses 40–47 |
| A represented row is selected by the witness | `Soundness/Layer7/StallSuffix.lean:105`, `selected_represented_row`, applies with the actual row index and the bound from `RepresentsRows.rowsBound` |
| The guest custom assertion reads architectural registers | `JoltConstraints/expansion_helpers.lean:23` stores `regidx` operands; `JoltConstraints/expansions.lean:123` constructs `.xreg` operands; at the pin, `jolt/crates/jolt-program/src/image/decode.rs`, `decode_custom`, `format_b_operands`, `rs1`, and `rs2`, use five-bit register indices |
| Built-in expansions introduce no spoil asserts | The Lean generated programs in `JoltBytecode/JoltISA/ExpansionsAutomated.lean` and the handwritten expansion files contain no `VirtualAssertEQ` constructor; the custom native case supplies it in `SourceInstruction.expand`; the pinned built-in recipes under `jolt/crates/jolt-program/src/expand/` contain no equality-assert emission, and `jolt/crates/jolt-program/src/asm.rs`, `__jolt_asm_stmt!`'s `assert_eq` arm, fixes the immediate to zero |
| The constraints enforce equality | `Soundness/Layer5/AssertionsBinary.lean` already derives the assertion predicate from the selected lookup and Assert flag; at the pin, `jolt/crates/jolt-riscv/src/instructions/assert/assert_eq.rs`, `AssertEq`, selects both register operands and the Assert flag, while `jolt/crates/jolt-lookup-tables/src/instructions/virt/assert_eq.rs`, `LookupQuery`, selects Equal and returns the equality indicator |

The existing comment above `Trace.SpoilAssertsPass` cites SC.W and SC.D as equality-assert examples.
That example citation is stale: the pinned `expand_scw` and `expand_scd` no longer emit `VirtualAssertEQ`.
This does not invalidate the plan's claim that built-in expansions introduce no nonzero-immediate equality assertions.
The audit concerns the modeled `SourceInstruction` type; inline source instructions are explicitly outside that type's scope in `expansion_helpers.lean`.

## Staged obligation and stopping point

`JoltInstance.source_spoil_assert_read_not_temporary` is the sole new `sorry`.
Given an actual `expand_instruction source = some rows` certificate, membership of a row in those rows, and that row's nonzero-immediate `VirtualAssertEQ`, it states that both source operands lie outside instruction temporaries 40–47.
The caller obtains the certificate and membership from the existing `expand_program_source_of_row` theorem.
The lemma takes only source-expansion data, without a witness or execution state.

I checked `ExpansionFacts.expand_ok`, `expand_temps_ok`, `expand_instruction_checks`, `expand_instruction_property`, and the proof of `expanded_control_read_not_temporary` for a reusable derivation.
Their sequence checks establish initialization before temporary reads and specific control-flow properties, but do not establish the absence of spoil asserts.
The distinction is concrete: Lean accepted the following checker example by kernel `decide`, supplied through standard input and not added to the repository.

```lean
example : ExpansionFacts.sequenceOk
    [JoltISA.Instr.ADDI (.vreg 40) (.xreg (.Regidx 0)) 0,
     JoltISA.Instr.VirtualAssertEQ (.vreg 40) (.vreg 40) 2] = true := by
  decide
```

This arbitrary sequence passes the checker and reads a temporary in a spoil assert; it is not claimed to be the expansion of any modeled source instruction.
Consequently, the missing proof must use actual source-expansion structure, not merely `sequenceOk`.
I staged that source fact instead of introducing an exhaustive instruction case split or changing the existing checker definitions.
Its source-code audit supports the statement, but is not a Lean proof of it.
No change to an approved statement or definition is proposed.

## Declarations

Paths in this table are relative to `JoltConstraints/`.
Times are proof-elaboration seconds measured from the current file contents with one worker and `-Dtrace.Elab.async=true -Dtrace.profiler=true -Dtrace.profiler.threshold=10000`.
The threshold filters profiler output; no proof resource limit was changed.

| Declaration | File and line | Change | Seconds |
|---|---|---|---:|
| `JoltConstraints.Soundness.binaryAssertion_passes_of_inputs` | `Soundness/Layer5/AssertionsBinary.lean:65` | New public extraction of the existing constraint argument, parameterized by two input words | 0.611 |
| `JoltConstraints.Soundness.binaryAssertion_passes` (private) | `Soundness/Layer5/AssertionsBinary.lean:111` | Preserves its statement; obtains the input words from register agreement and calls the extraction | 0.018 |
| `JoltInstance.source_spoil_assert_read_not_temporary` | `Soundness/Layer7/SpoilAsserts.lean:17` | New staged source-expansion obligation | Not a completed proof |
| `JoltInstance.expanded_spoil_assert_read_not_temporary` | `Soundness/Layer7/SpoilAsserts.lean:33` | Lifts the staged obligation to expanded bytecode using `expand_program_source_of_row` | 0.001 |
| `JoltInstance.represented_spoil_asserts_pass` | `Soundness/Layer7/SpoilAsserts.lean:56` | Proves every row's assertion from `RepresentsRows`, selection, input equations, and the shared assertion proof | 0.379 |
| `JoltInstance.soundness_spoil_asserts_pass` | `Soundness/TopLevel.lean:172` | Replaces D's direct `sorry` with the Layer 7 theorem, preserving D's statement | 0.001 |

The unchanged `binaryAssertion_step` caller also checked, with proof elaboration taking 0.046 seconds.
No measured changed proof exceeded ten seconds, and each completed new or changed proof body is below 60 lines.
Both the original D statement and the private `binaryAssertion_passes` statement were compared textually with HEAD and are unchanged.
No existing theorem gained a hypothesis.
The new extracted helper takes equalities identifying the two instruction inputs with words; its existing caller supplies them through `RegisterAgreementOn.registerInputs`, and D supplies them through `RepresentsRows` and `instructionInputs_of_selected_bytecode`.
The new run theorem uses `RepresentsRows` and `UntrustedAnswerRun`, requiring no final RAM or stopping facts.
There are no new `bv_decide`, `native_decide`, `decide +kernel`, axioms, or heartbeat overrides.
The three assertion-kind cases in the extracted proof were moved from the existing proof, without duplicating the constraint argument.

## Validation

`lake build JoltConstraints` failed in the other agent's unfinished `Soundness/Layer6/DivisionAppend.lean` edits.
The errors were at line 23, where `Unit` did not match a dependent `RuntimeAdvice` type, and line 29, where `rfl` did not close an instruction match.
That build successfully built `JoltConstraints.Soundness.Layer7.SpoilAsserts`.
I did not edit `DivisionAppend.lean`.

The authorized fallback command passed all 8658 jobs:

```text
lake build JoltConstraints.Soundness.Layer5.AssertionsBinary JoltConstraints.Soundness.Layer7.SpoilAsserts
```

The current contents of `Soundness/TopLevel.lean` were also checked successfully through `lake env lean --stdin`, followed in the same invocation by the axiom commands below.
This checked the current D body against the available compiled imports, without relying on an old compiled D theorem or claiming that the unfinished dependency sources build.
Whitespace checks passed for the owned source files.

| `#print axioms` target | Result |
|---|---|
| `JoltInstance.soundness_spoil_asserts_pass` | `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound` |
| `JoltInstance.represented_spoil_asserts_pass` | `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound` |
| `JoltInstance.expanded_spoil_assert_read_not_temporary` | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` |
| `JoltInstance.source_spoil_assert_read_not_temporary` | `propext`, `sorryAx`, `Quot.sound` |
| `JoltConstraints.Soundness.binaryAssertion_passes_of_inputs` | `propext`, `Classical.choice`, `Quot.sound` |
| `JoltConstraints.Soundness.binaryAssertion_step` | `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound` |
| `JoltInstance.selected_represented_row` | `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound` |
| `expand_program_source_of_row` | `propext`, `Classical.choice`, `Quot.sound` |

D's remaining `sorryAx` comes through the staged source-expansion obligation.
The extracted assertion proof and the reused selection and expansion-lifting facts do not reach `sorryAx`.

Only the three allowed Lean files and this requested report were edited by this task.
`methods/soundness.md` and `JoltConstraints/model_review.md` were outside the allowed edit list.
For their next authorized update, D's outstanding obligation should be recorded as `source_spoil_assert_read_not_temporary`, with the source-expansion argument above.
Work stops here for review of that staged statement.

## Spoil-assert fact

The staged source fact is now proved, and helper D no longer depends on `sorryAx`.
No commit was made.

I checked the new plan against the code before editing.
The generated and handwritten Lean expansion programs contain no `VirtualAssertEQ`, and `git grep` found no `VirtualAssertEQ` in the pinned Jolt built-in expansion recipes under `crates/jolt-program/src/expand/` at `5def437f`.
The native custom case in `JoltConstraints/expansions.lean:123` constructs the assertion from architectural `.xreg` operands.
The native checker in `JoltConstraints/expansion_facts.lean:600` includes `tempsReadAfterWrite [instruction]`, whose one-row form forbids any first read of registers 40–47.
The existing per-source checker proofs compiled without changes after the new sequence check.

| Declaration | File and line | Change |
|---|---|---|
| `ExpansionFacts.noSpoilAsserts` | `JoltConstraints/expansion_facts.lean:166` | New sequence check requiring every `VirtualAssertEQ` immediate to be zero |
| `ExpansionFacts.sequenceOk` | `JoltConstraints/expansion_facts.lean:177` | Definition strengthened by the new conjunct |
| `ExpansionFacts.sequenceOk_noSpoilAsserts` | `JoltConstraints/expansion_facts.lean:228` | New projection used by the source fact |
| `JoltInstance.source_spoil_assert_read_not_temporary` | `JoltConstraints/Soundness/Layer7/SpoilAsserts.lean:17` | Replaced its `sorry` with a proof via `expand_instruction_property`; statement unchanged |

The proof bodies of the seven existing `sequenceOk` projections at `JoltConstraints/expansion_facts.lean:185`, `:191`, `:197`, `:203`, `:209`, `:215`, and `:221` were adjusted to project through the new conjunct.
Their written statements are unchanged; because `sequenceOk` is stronger, their checker assumption is semantically stronger.
No previously existing theorem statement or hypothesis was added or changed, and no new `bv_decide`, `native_decide`, `decide +kernel`, axiom, or resource-limit override was introduced.

With `lake env lean -Dtrace.Elab.async=false -Dtrace.profiler=true -Dtrace.profiler.threshold=10000 JoltConstraints/expansion_facts.lean`, elapsed synchronous file checking was 17.081 seconds before and 17.506 seconds after the edit.
The existing `ExpansionFacts.csrrs_ok` proof was the only declaration reported above ten seconds: 10.525 seconds before and 10.783 seconds after.
The threshold only filtered profiler output.

`lake build JoltConstraints.expansion_facts` passed with 8462 jobs, and `lake build JoltConstraints.Soundness.Layer7.SpoilAsserts` passed with 8658 jobs.
`lake env lean JoltConstraints/Soundness/TopLevel.lean` and `git diff --check` passed.
The full `lake build JoltConstraints` failed in the other agent's concurrent `Soundness/Layer6/DivisionAppend.lean` work because `DivisionPrograms.olean` was absent when that job started; `DivisionPrograms` built later in the same run.
I did not edit either division file.

`#print axioms JoltInstance.soundness_spoil_asserts_pass` returned `propext`, `sys_enable_experimental_extensions`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
`#print axioms JoltInstance.source_spoil_assert_read_not_temporary` returned `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
