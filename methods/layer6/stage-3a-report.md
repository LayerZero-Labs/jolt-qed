# Layer 6, stage 3a report

## Part A

Read `AGENTS.md`, `stage-2-report.md`, `reuse.md`, and `stage-3a.md` in the requested order, then checked Part A's claims against the code before editing.
The audit found no Part A blocker: `PrefixAgreement.lean` contained the six listed definitions and structures, five staged lemmas, and two proved callers, and both requested register helpers follow from the existing agreement fields.
The new import structure is acyclic.

Moved the declarations as specified:

- `JoltConstraints/Soundness/Layer6/PrefixState.lean`: `BoundaryState` (line 26), `expansionRowCount` (64), `ExpansionHasAdvice` (72), `ExpansionLive` (82), `RunExtends` (95), and `ExpansionState` (113).
- `JoltConstraints/Soundness/Layer6/BoundaryStart.lean`: `boundaryState_empty` (line 16) and `expansion_start` (30), still staged with `sorry`.
- `JoltConstraints/Soundness/Layer6/DivisionBlock.lean`: `division_block` (line 19), still staged with `sorry`.
- `JoltConstraints/Soundness/Layer6/RowStep.lean`: `row_step` (line 15), still staged with `sorry`.
- `JoltConstraints/Soundness/Layer6/ExpansionFinish.lean`: `expansion_finish` (line 16), still staged with `sorry`.
- `JoltConstraints/Soundness/Layer6/PrefixAgreement.lean`: retains the proved `boundary_step` (line 21) and `soundness_execution_prefix_agreement` (84), importing the four staged-lemma files.

A text comparison against the pre-edit files confirmed that all 13 existing declarations, including their docstrings, statements, and proofs, are unchanged.
`Registers.lean` differs only by these two proved helpers, each with a docstring and example:

| Declaration in `JoltConstraints/Soundness/Layer5/Registers.lean` | Meaning | Proof elaboration time |
| --- | --- | --- |
| `RegisterAgreementOn.mono`, line 44 | Restrict agreement to any smaller live set, retaining register presence. | 0.001405 s |
| `RegisterAgreement.toOn`, line 55 | Restrict full agreement to any live set, using `RegisterAgreementOn.mono`. | 0.002163 s |

Measured the new proofs with Lean's elaboration trace and profiler using `-j1`.
No new proof exceeds ten seconds.
No premises, restrictions, existing definitions, proof limits, `sorry`s, or `bv_decide` uses were added or changed.

`lake build JoltConstraints` passed (8805 jobs), and `git diff --check` passed.
`#print axioms JoltInstance.soundness` retains `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`, and the existing `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5` axiom.
A traversal of the compiled dependency graph confirmed that the reachable declarations directly using `sorryAx` are exactly `boundaryState_empty`, `expansion_start`, `row_step`, `division_block`, `expansion_finish`, `soundness_prover_accepts` (C), and `soundness_spoil_asserts_pass` (D), all in namespace `JoltInstance`.
Both new register helpers depend only on `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

Only Part A's named files were edited; an unrelated untracked `methods/layer6/stage-3b-report.md` was left untouched.
Part B was not attempted, no commit was made, and work stops here for Ari's review.

## Part B

Reread `AGENTS.md`, the earlier reports, `reuse.md`, and Part B before implementation, and checked the proposed argument against the code.
No blocking mismatch was found.
The approved `division_block` statement is unchanged, and its proof now composes five named staged lemmas without a `sorry` in its body.
The five component proofs remain for review and later implementation.

### Audit findings

Checked all eight generated programs in `JoltBytecode/JoltISA/ExpansionsAutomated.lean`, their dispatch through `SourceInstruction.expand` and `ExpandedSource.ofPureProgram`, and every corresponding `*Program_sound` and `*Program_concrete` signature in `JoltBytecode/InstructionEquivalence/Instructions/ALUAdviceFamily/`.
For nonzero destinations each program contains exactly one VirtualAdvice row, only the twelve arithmetic/advice/assertion row kinds listed below, and a final architectural destination write.
Zero destinations expand to a no-op and cannot satisfy the advice-bearing premise.
`ExpansionFacts.expand_temps_ok` establishes the first-write-before-read property used by the shared sequence statement.

Checked the pinned expander and tracer implementations with `git show 5def437f:<path>`: `jolt/crates/jolt-program/src/expand/division/{div,divu,divw,divuw,rem,remu,remw,remuw}.rs`, `division/shared.rs` (`expand_unsigned_word_div_rem`), and the eight matching `jolt/tracer/src/instruction/*.rs` implementations of `RISCVTrace::trace`.
The generated row families and `SourceInstruction.honestTracerAdvice` agree with those implementations, including REM's honest quotient magnitude zero when its divisor is zero.
DIV, DIVU and DIVW soundness gives advice uniqueness; combining this with concrete execution and determinism gives the uniform final-Sail-state statement used here.
DIVUW and the remainder soundness theorems give that final Sail state directly.

The existing general device-setup frame preserves layout, inputs and advice buffers, rather than equality of the complete device.
The staged honest-run lemma therefore explicitly owes the stronger arithmetic-program frames for device, tape, host settings and virtual registers outside instruction temporaries, using `StatePreservation.Preserves` and the register-write primitives.
This is a proof obligation already required by step 4, not a new premise of `division_block`.

### Declarations

All declarations below are in `JoltConstraints/Soundness/Layer6/DivisionBlock.lean`, in namespace `JoltInstance`.
Every new declaration has a docstring and a division example.

| Declaration | Line | Status and purpose |
| --- | --- | --- |
| `DivisionKind` | 16 | New eight-case classification, avoiding separate sequence statements per division. |
| `DivisionKind.source` | 23 | New definition selecting the existing source constructor. |
| `DivisionKind.program` | 38 | New definition selecting the existing generated program. |
| `DivisionKind.result` | 53 | New definition selecting the existing architectural result function. |
| `DivisionKind.honestAdvice` | 68 | New definition reading the single word from `SourceInstruction.honestTracerAdvice`. |
| `expansionInstructions` | 75 | New definition extracting the stamped block's instructions. |
| `patchAdviceWord` | 83 | New instruction-list helper replacing only the VirtualAdvice value. |
| `DivisionArithmeticRow` | 91 | New predicate for the twelve row kinds, excluding memory, tape, control flow and HostIO. |
| `ArithmeticAdviceSequence` | 104 | New certificate for a successfully terminating straight-line program family, exactly one advice row, allowed row kinds and temporary liveness. |
| `division_expansion_layout` | 120 | Staged step 1: identify the source, nonzero destination, exact row count and generated program family. |
| `arithmetic_advice_sequence_run` | 150 | Staged step 2: construct the witness-advice run and its completed expansion state, together with an actual `Program.Run` certificate. |
| `division_program_result` | 180 | Staged step 3: derive the uniform architectural Sail result from the generated program's successful run. |
| `DivisionFinalAgreement` | 193 | New relation equating the complete states except instruction temporaries 40–47. |
| `division_program_honest` | 210 | Staged step 4: construct the honest program run from the same start and establish `DivisionFinalAgreement`. |
| `division_append_honest` | 231 | Staged step 5: append the honest rows, transfer represented observations and the completed invariant, and establish honest advice throughout. |
| `division_block` | 271 | Existing statement, now proved from the five staged lemmas. |

The shared step-2 statement takes an arbitrary program family certified by `ArithmeticAdviceSequence`, not a division kind.
It starts from `ExpansionState` at zero completed rows, whose register agreement excludes incoming instruction temporaries, and returns a completed state whose agreement again excludes those temporaries.
Its intended induction uses `ExpansionLive` and the first-access certificate for intermediate rows, existing bytecode progress and nontruncation lemmas, and `Program.Run` composition.
No Layer 5 proof was ported in this stage.

The required Layer 5 steps are:

| Row kinds | Existing step and location |
| --- | --- |
| ADDI | `addi_step`, `Soundness/Layer5/AddImmediate.lean:76` |
| SUB, MUL | `arithmetic_step`, `Soundness/Layer5/Arithmetic.lean:109` |
| XOR | `xor_step`, `Soundness/Layer5/Xor.lean:62` |
| VirtualNegateIf | `virtualBinary_step`, `Soundness/Layer5/VirtualBinary.lean:117` |
| VirtualSignExtendWord, VirtualZeroExtendWord | `unaryWord_step`, `Soundness/Layer5/UnaryWord.lean:224` |
| VirtualAssertValidDiv0, VirtualAssertValidUnsignedRemainder | `binaryAssertion_step`, `Soundness/Layer5/AssertionsBinary.lean:111` |
| VirtualAssertMulUNoOverflow | `mulAssertion_step`, `Soundness/Layer5/AssertionMulOverflow.lean:70` |
| VirtualAssertLTE | `assertLTE_step`, `Soundness/Layer5/AssertLessThanEqual.lean:66` |
| VirtualAdvice | No Layer 5 constraint-to-execution step exists yet. |

The existing steps require full `RegisterAgreement`; the port must also adapt their shared operand and register-update helpers to agreement on live registers.
VirtualAdvice additionally needs a new step extracting a 64-bit witness word from its RangeCheck lookup and register write equation, then using its existing instruction semantics.
The instruction-level `virtual_advice_run` and `virtual_advice_run_ex` lemmas do not themselves establish this constraint-to-execution result.

### Hypotheses and staging checks

No approved statement, restriction, language definition or existing invariant was changed, and no premise was added to `division_block`.
The new helper hypotheses are discharged by its compiled caller: preprocessing from `context.entryIsRust`; source classification, row count and sequence shape from step 1; prepared state, register presence, extension and witness execution from step 2; the Sail result from step 3; and honest execution plus final agreement from step 4.
Each staged lemma is used by the caller.

Execution claims use `UntrustedAnswerRun` or an explicit successful `Program.Run`; no post-state property is treated as an execution certificate.
Step 2 retains `JoltField` for the existing field/word bounds and constrains the witness advice through the lookup, without assuming that an arbitrary field element is a 64-bit word.
No source-boundary PC arithmetic was moved into this block; that remains with `expansion_finish` and its existing assumptions.
The prepared starting state uses the existing `NextStep` clause, including `source_is_compressed`, rather than an interior row's compression flag.
The source-identification lemma takes successful preprocessing explicitly, supplying the PC-map uniqueness needed by `instructionAt`.
For REM of 7 by zero, witness quotient 5 and honest quotient 0 are allowed to differ only in instruction temporaries; both executions produce architectural destination 7 and the same persistent final state.

### Validation and scope

`lake build JoltConstraints` passed (8805 jobs), and `git diff --check` passed.
A text comparison confirmed that the `division_block` statement is unchanged and its proof body contains no `sorry`.
Profiling with `lake env lean -j1 -Dtrace.Elab.async=true -Dtrace.profiler=true -Dtrace.profiler.threshold=0 JoltConstraints/Soundness/Layer6/DivisionBlock.lean` measured its proof elaboration at 0.019605 seconds.
No declaration took more than ten seconds in that profile; the five staged bodies only elaborate their named gaps.
No `bv_decide`, `native_decide`, `decide +kernel`, or raised proof limit was introduced.

The axiom traversal checked that `division_block` reaches `sorryAx` through exactly `division_expansion_layout`, `arithmetic_advice_sequence_run`, `division_program_result`, `division_program_honest`, and `division_append_honest`.
`#print axioms JoltInstance.soundness` retains the same axiom names recorded in Part A, including the existing branch-target bit-vector axiom.
`division_block` has no bit-vector axiom dependency.
At the time of this build, the full soundness traversal additionally reached `row_step`, `expansion_finish`, C, D, and Agent 2's private `BoundaryStart.first_row_of_entry_slot` and `BoundaryStart.empty_run_ram_word` gaps.
Those concurrent boundary changes are outside this Part B implementation and audit.
The audit script and logs are `/private/tmp/layer6-stage3a-part-b-axioms.lean` and `/private/tmp/layer6-stage3a-part-b-{build,profile,axioms}.log`.

This task edited only `DivisionBlock.lean` and this report; no private lemma needed a visibility change.
Concurrent changes in `BoundaryStart.lean`, `Layer7/TerminationStore.lean`, and `stage-3b-report.md` were left untouched.
No commit was made, and work stops after this Part B section for review.
