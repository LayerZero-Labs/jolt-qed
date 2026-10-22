# Layer 6, stage 4a report

## Part A: live-register steps

### Audit before implementation

No incorrect claim or blocking gap was found in Part A.
The audit covered its motivation, the register-helper generalization, all eight named step families, and the VirtualAdvice statement before implementation.
Part B was not undertaken.

`BoundaryState.registers` and `ExpansionState.registers` use `RegisterAgreementOn`; `ExpansionLive` in `JoltConstraints/Soundness/Layer6/PrefixState.lean:82` excludes instruction temporaries initially and admits a temporary after an earlier row writes it.
The existing register and operand proofs use agreement only for the registers they read and for the old values retained after a write.
Each writing step can therefore add its destination without requiring that destination's incoming value, unless it is also a source.
The x0 branch of `RegisterAgreementOn.write` uses `registersVal_x0`, so this remains valid when x0 was initially outside the live set.
Source/destination aliases remain allowed.
The three assertion families have no destination: their live set stays unchanged.

A repository search found no proof caller outside Layer 5 for the eight step lemmas.
Their mentions in `DivisionBlock.lean` are documentation for the staged witness-advice run.
Other Layer 5 families still use full-agreement helpers, so their public statements must continue to work through wrappers.
The old full-agreement `advance_pc` had no proof caller and was removed when its proof was generalized.

For VirtualAdvice, the relevant selected-row facts are `instructionLookupRa_unique` in `Layer1/InstructionReads.lean:80`, `lookupOutput_of_selected_bytecode` in `Layer4/Table.lean:24`, and `rdWriteValue_eq_lookupOutput` in `Layer4/Outputs.lean:13`.
`rangeCheckTableEntry` in `JoltConstraints/lookup_table.lean:156` returns the low 64 bits of the selected 128-bit lookup address, cast into the field.
The proof extracts those bits as a `BitVec 64`; it does not assume that an arbitrary field element, or the entire lookup address, is already a 64-bit word.
`RightLookupEqRightInputOtherwise.lean` disables the ordinary right-input equation on Advice rows, so no equality with honest division advice follows from this row step.

The corresponding Jolt files were read with `git show 5def437f:<path>`:

- `jolt/crates/jolt-riscv/src/instructions/virt/advice.rs`, the `VirtualAdvice` declaration, supplies the `Advice` and `WriteLookupOutputToRD` circuit flags.
- `jolt/crates/jolt-lookup-tables/src/instructions/virt/advice.rs`, `LookupQuery` for `VirtualAdvice`, selects RangeCheck and derives the lookup operand and output from the advice write.
- `jolt/crates/jolt-lookup-tables/src/tables/range_check.rs`, `RangeCheckTable::materialize_entry`, returns the low XLEN bits.
- `jolt/tracer/src/instruction/virtual_advice.rs`, `RISCVInstruction::execute`, writes the supplied advice word to the destination.

The execution lemma cited by the plan, `JoltISA.virtual_advice_run`, is specialized to a writable virtual destination and the default immediate.
The new selected-row step covers any canonical destination and decoded immediate, so it uses the shared destination-write finisher and the definitionally equal VirtualAdvice execution rule.
This requires no new instruction case split or copied register-write proof.

The statement checks from AGENTS.md also pass: the steps construct successful execution from a selected row and agreement, retain register presence, and derive the written word from constrained values.
They introduce no claim about a bare post-state's instruction, no unbounded field-to-word identification, no compression-flag assumption, and no claim about all rows sharing an address.
The existing characteristic bounds are retained; no new PC, uniqueness, restriction, or honest-advice premise is added.

### Statement changes and declarations

All declarations below are in namespace `JoltConstraints.Soundness`, with file names relative to `JoltConstraints/Soundness/Layer5/`.
Every listed declaration is proved.
In the tables, `full` means `RegisterAgreement witness t state`, `on live` means `RegisterAgreementOn live witness t state`, `src s` means `TraceWitness.sourceRegisterAddress s`, and `dst d` means `TraceWitness.destinationRegisterAddress d`.
`live + d` abbreviates the actual predicate `fun register => live register ∨ register = dst d`; no such abbreviation was added to Lean.
The old and new statements have the same field, context, selected-row, canonicality, operand-selection, value, and execution hypotheses unless a change is stated explicitly below.
Times are proof elaboration seconds.

The shared proofs now work over `RegisterAgreementOn`.

| Declaration | Location | Old statement → new statement | Seconds |
| --- | --- | --- | ---: |
| `RegisterAgreementOn.toFull` | `Registers.lean:64` | New: `on live` plus `∀ register, live register` gives `full`; wrappers discharge this for the full live predicate. | 0.001095 |
| `RegisterAgreementOn.advance_pc` | `Registers.lean:82` | Old `RegisterAgreement.advance_pc`: `full` before/after PC preparation → `on live` before/after, with the same live predicate; unused old declaration removed. | 0.002193 |
| `RegisterAgreementOn.read` | `Registers.lean:104` | Old full read → `on live` plus `live (src source)`; the successful read and table-value conclusions are unchanged. | 0.002255 |
| `RegisterAgreementOn.noWrite` | `Registers.lean:213` | Old full no-write transport → `on live` at both cycles; no liveness premise is added. | 0.005325 |
| `RegisterAgreementOn.write` | `Registers.lean:251` | Old full write transport → `on live` before and `on (live + destination)` after; no premise about the old destination is added. | 0.043601 |
| `RegisterAgreementOn.rs1Value` | `RegisterInputs.lean:28` | Old full first-source value → `on live` plus `live (src source)`; same value equation. | 0.003950 |
| `RegisterAgreementOn.rs2Value` | `RegisterInputs.lean:54` | Old full second-source value → `on live` plus `live (src source)`; same value equation. | 0.002985 |
| `RegisterAgreementOn.registerInputs` | `RegisterInputs.lean:80` | Old full register operands → `on live` plus `live (src lhs)` and `live (src rhs)`; same two input equations. | 0.017249 |
| `RegisterAgreementOn.immediateInputs` | `RegisterInputs.lean:130` | Old full register/immediate operands → `on live` plus `live (src source)`; same two input equations. | 0.020472 |
| `registerWriteOn_step` | `LookupWrite.lean:67` | Old full finisher → `on live` input and `on (live + destination)` output; drops `absent` and requires the execution rule for `row.instruction.withRuntimeAdvice advice` instead of the unpatched instruction. | 0.004219 |

The generalized finisher handles both advice and non-advice writes once.
For ordinary rows, the existing no-advice fact rewrites its patched execution-rule obligation.
Its write-value and execution conclusions still cover the last witness cycle; agreement at the next cycle remains conditional on that cycle existing.

The eight public step statements changed as follows.
All previous value, predicate, execution, and final-cycle conclusions remain unchanged.

| Declaration | Location | Old statement → new statement | Seconds |
| --- | --- | --- | ---: |
| `addi_step` | `AddImmediate.lean:80` | `full` input/output → `on live` plus `live (src source)`, returning `on (live + destination)`. | 0.013409 |
| `arithmetic_step` | `Arithmetic.lean:113` | `full` input/output → `on live` plus liveness of `lhs` and `rhs`, returning `on (live + destination)`. | 0.033642 |
| `xor_step` | `Xor.lean:68` | `full` input/output → `on live` plus liveness of `lhs` and `rhs`, returning `on (live + destination)`. | 0.017135 |
| `virtualBinary_step` | `VirtualBinary.lean:121` | `full` input/output → `on live` plus liveness of `lhs` and `rhs`, returning `on (live + destination)`. | 0.070312 |
| `unaryWord_step` | `UnaryWord.lean:228` | `full` input/output → `on live` plus `live (src source)`, returning `on (live + destination)`. | 0.063093 |
| `binaryAssertion_step` | `AssertionsBinary.lean:115` | `full` input/output → `on live` plus liveness of `lhs` and `rhs`, returning `on live`. | 0.037073 |
| `mulAssertion_step` | `AssertionMulOverflow.lean:74` | `full` input/output → `on live` plus liveness of `lhs` and `rhs`, returning `on live`. | 0.012109 |
| `assertLTE_step` | `AssertLessThanEqual.lean:70` | `full` input/output → `on live` plus liveness of `lhs` and `rhs`, returning `on live`. | 0.011143 |

Their private helper statements were generalized in place, keeping their existing conclusions and proofs apart from passing source liveness to the shared helpers.
No family proof was copied.

| Declaration | Location | Old statement → new statement | Seconds |
| --- | --- | --- | ---: |
| `addi_inputs` | `AddImmediate.lean:50` | `full` input → `on live` plus `live (src source)`; conclusion unchanged. | 0.006846 |
| `addi_write_value` | `AddImmediate.lean:61` | `full` input → `on live` plus `live (src source)`; conclusion unchanged. | 0.004391 |
| `arithmetic_write_value` | `Arithmetic.lean:68` | `full` input → `on live` plus `live (src lhs)` and `live (src rhs)`; conclusion unchanged. | 0.604070 |
| `xor_inputs` | `Xor.lean:35` | `full` input → `on live` plus `live (src lhs)` and `live (src rhs)`; conclusion unchanged. | 0.008126 |
| `xor_write_value` | `Xor.lean:47` | `full` input → `on live` plus `live (src lhs)` and `live (src rhs)`; conclusion unchanged. | 0.008501 |
| `virtualBinary_write_value` | `VirtualBinary.lean:75` | `full` input → `on live` plus `live (src lhs)` and `live (src rhs)`; conclusion unchanged. | 0.071633 |
| `unaryWord_inputs` | `UnaryWord.lean:121` | `full` input → `on live` plus `live (src source)`; conclusion unchanged. | 0.208610 |
| `unaryWord_write_value` | `UnaryWord.lean:137` | `full` input → `on live` plus `live (src source)`; conclusion unchanged. | 1.227941 |
| `binaryAssertion_passes` | `AssertionsBinary.lean:58` | `full` input → `on live` plus `live (src lhs)` and `live (src rhs)`; conclusion unchanged. | 0.509034 |
| `mulAssertion_passes` | `AssertionMulOverflow.lean:39` | `full` input → `on live` plus `live (src lhs)` and `live (src rhs)`; conclusion unchanged. | 0.214250 |
| `assertLTE_passes` | `AssertLessThanEqual.lean:39` | `full` input → `on live` plus `live (src lhs)` and `live (src rhs)`; conclusion unchanged. | 0.304706 |

The following full-agreement declarations retain their original statements and now derive their results from the general proofs.
A normalized text comparison against the pre-task snapshot checked each signature.

| Declaration | Location | Statement and implementation | Seconds |
| --- | --- | --- | ---: |
| `RegisterAgreement.read` | `Registers.lean:118` | Old statement = new statement; full agreement is restricted to `fun _ => True` and the general result is converted back where needed. | 0.000893 |
| `RegisterAgreement.noWrite` | `Registers.lean:232` | Old statement = new statement; full agreement is restricted to `fun _ => True` and the general result is converted back where needed. | 0.001736 |
| `RegisterAgreement.write` | `Registers.lean:292` | Old statement = new statement; full agreement is restricted to `fun _ => True` and the general result is converted back where needed. | 0.002153 |
| `RegisterAgreement.rs1Value` | `RegisterInputs.lean:42` | Old statement = new statement; full agreement is restricted to `fun _ => True` and the general result is converted back where needed. | 0.001487 |
| `RegisterAgreement.rs2Value` | `RegisterInputs.lean:68` | Old statement = new statement; full agreement is restricted to `fun _ => True` and the general result is converted back where needed. | 0.001388 |
| `RegisterAgreement.registerInputs` | `RegisterInputs.lean:108` | Old statement = new statement; full agreement is restricted to `fun _ => True` and the general result is converted back where needed. | 0.001802 |
| `RegisterAgreement.immediateInputs` | `RegisterInputs.lean:157` | Old statement = new statement; full agreement is restricted to `fun _ => True` and the general result is converted back where needed. | 0.001712 |
| `registerWrite_step` | `LookupWrite.lean:97` | Old statement = new statement; full agreement is restricted to `fun _ => True` and the general result is converted back where needed. | 0.004376 |

`advice_step` is new at `Advice.lean:26` and elaborated in 0.318807 seconds.
From the usual field bound, constraint context/equations, selected VirtualAdvice row, `on live`, and arbitrary tape answer, it returns a word `value : BitVec 64` and typed runtime advice such that:

- Patching the row produces `.VirtualAdvice destination value imm`.
- `witness.RdWriteValue t = (value.toNat : F)`.
- Executing that patched row retires successfully in `afterWriteDst destination value pre`.
- Whenever the next witness column exists, it agrees on `live + destination`.

There is no source-liveness or honest-advice premise on this source-free row.
The result constrains execution of the witness's word, leaving advice honesty to the later division-block argument.
`JoltConstraints.lean:60` imports the new file so the aggregate build checks it.

### Validation and scope

`lake build JoltConstraints` passed, including a final build after documentation and formatting cleanup.
The final build completed all 8,806 jobs; existing staged gaps remain as warnings.
`git diff --check` passed before this report was written.

The axiom audit checked all 27 generalized helpers, retained wrappers, public ported steps, and the new advice step listed above, traversing their transitive constant dependencies.
None reaches a declaration directly using `sorryAx`; this also covers the private helper proofs reached by the steps.
None has a native bit-vector axiom dependency.
The register helpers depend on `propext`, `Classical.choice`, and `Quot.sound`; the finisher and step proofs additionally retain `sys_enable_experimental_extensions`.
`#print axioms JoltInstance.soundness` retains `propext`, `sorryAx`, `sys_enable_experimental_extensions`, `Classical.choice`, `Quot.sound`, and the existing `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5` axiom.

At the audit snapshot, the soundness theorem's reachable direct `sorryAx` users were:

- `JoltInstance.division_expansion_layout`.
- `JoltInstance.arithmetic_advice_sequence_run`.
- `JoltInstance.division_program_result`.
- `JoltInstance.division_program_honest`.
- `JoltInstance.division_append_honest`.
- `JoltInstance.row_step`.
- `JoltInstance.expansion_finish`.
- `JoltInstance.soundness_prover_accepts` (C).
- `JoltInstance.soundness_spoil_asserts_pass` (D).
- Agent 2's private `BoundaryStart.empty_run_ram_word`.

These are outside Part A; no new `sorry`, axiom, `bv_decide`, `native_decide`, `decide +kernel`, or raised proof limit was introduced.
The existing `RegisterAgreement` and `RegisterAgreementOn` definitions are textually unchanged.
All other Layer 5 step statements are unchanged.
`DivisionBlock.lean` is identical to the pre-task snapshot, so `arithmetic_advice_sequence_run` remains staged for Part B.
No changes were made to `BoundaryStart.lean`, `Layer7/TerminationStore.lean`, the language, core semantics, restrictions, or assumptions.
Concurrent edits to the two named files were left untouched.

Profiling used `lake env lean -j1 -Dtrace.Elab.async=true -Dtrace.profiler=true -Dtrace.profiler.threshold=0` on the twelve changed/new Layer 5 modules.
No profiled proof exceeds ten seconds.
The tables report proof elaboration times rather than whole-module build times.
Build, axiom, and per-module profiling logs are `/private/tmp/layer6-stage4a-final-build.log`, `/private/tmp/layer6-stage4a-axioms.log`, and `/private/tmp/layer6-stage4a-profile-*.log`.
The axiom audit script is `/private/tmp/layer6-stage4a-axioms.lean`.

No commit was made.
Work stops after this Part A report for review.

## Part B: the witness-advice run

### Audit before implementation

The re-audit found no incorrect Part B claim or blocking gap.
The Part A step lemmas now require live source registers and return agreement on the previous live set plus any written destination.
The twelve cases in `DivisionArithmeticRow` match the available steps: VirtualAdvice, VirtualNegateIf, XOR, MUL, SUB, ADDI, VirtualSignExtendWord, VirtualZeroExtendWord, VirtualAssertValidDiv0, VirtualAssertMulUNoOverflow, VirtualAssertLTE, and VirtualAssertValidUnsignedRemainder.

An expansion's temporary certificate supplies the missing source-liveness facts.
The proof extracts the exact indexed source block and derives its certificate using `expand_instruction_property`, `nativeRowOk_tempsReadAfterWrite`, and `sequenceOk_tempsReadAfterWrite`, the same ingredients behind `expand_temps_ok`.
A read of an instruction temporary has a strictly earlier write in that block; the current row's own destination does not count as initialization.
That earlier write puts the register in `ExpansionLive`.
This argument does not identify blocks merely by their source address.

`NextStep` includes honest runtime advice for the whole prefix, so it cannot describe each intermediate run carrying the witness's potentially dishonest advice.
The entry and linkage clause already present in `ExpansionState.next` suffices for those intermediate rows.
The implementation names that clause `RawRowEntry` and reconstructs the original `NextStep` only at the initial honest prefix.
No additional hypothesis is needed on `arithmetic_advice_sequence_run` or `division_block`.

The arithmetic steps preserve full memory and device state, which is sufficient to preserve the cut RAM relation.
A nonterminal row's countdown rules out `StableStall`, and the existing bytecode PC lemmas rule out placing it at the final witness cycle.
Thus the induction cannot silently truncate an expansion.
The single-advice hypothesis selects one witness word for the whole patched program, and the advice step's word encoding plus the existing field-characteristic bound identifies that word with its runtime advice.

The pinned-code checks included Jolt's expansion metadata stamping and VirtualAdvice execution at `5def437f`.
Jolt's expander assigns the countdown and puts the compression flag only on the final row (`jolt/crates/jolt-program/src/expand/metadata.rs:47-52`).
Jolt's tracer writes the supplied advice word to the destination register (`jolt/tracer/src/instruction/virtual_advice.rs:62-64`).
The signed remainder expansion in `jolt/crates/jolt-program/src/expand/division/rem.rs` was also read at that pin to check its arithmetic/advice row sequence.
The remaining arithmetic semantics were checked against the current Lean step APIs and the Part A audit.

The four checks under “Before staging a statement” are satisfied.
The row contract returns an explicit successful execution, rather than inferring execution from a post-state.
Field-to-word equality uses the word bound and field-characteristic bound.
PC preparation uses `source_is_compressed`, rather than treating the final-row flag as a source-wide flag.
Temporary liveness uses the exact indexed expansion slice, so it needs no unproved address-uniqueness assumption.

### Implementation

`PlainRow.lean` defines the reusable row-extension contract for rows other than LD, SD, VirtualHostIO, JAL, and JALR.
`DivisionArithmeticRow` moved there with its definition unchanged.
`PlainRowExtension` records the appended trace row, raw entry, successful execution, witness runtime-advice value, witness tape-read value when applicable, recorded tape answer, run extension, row count, and next `ExpansionState`.
The witness-cycle bound is obtained by its caller from the unfinished expansion state.

`arithmetic_plain_row_step` proves this contract for all twelve division arithmetic kinds using the Part A rules.
Shared helpers handle writes, assertions, observations, RAM preservation, and the appended expansion state.
The arithmetic specialization chooses tape answer zero because these twelve kinds do not consume a tape answer.
`plain_row_step_other` is the single named staged gap for the remaining plain kinds, and `plain_row_step` dispatches between the proved specialization and that gap.
The specialization is separately public so the arithmetic sequence proof has no dependency on the remaining-kind gap.

`arithmetic_advice_sequence_run` is proved with its original statement unchanged.
The proof chooses the witness's word at the unique advice offset, extends the run by induction over the expansion suffix, and composes the actual row executions using `execProgram_instr_run_retire`.
Interior entry states agree with the previous appended post-state, and the final result uses the exact appended trace equality.
The four other DivisionBlock gaps remain staged: `division_expansion_layout`, `division_program_result`, `division_program_honest`, and `division_append_honest`.
`division_block` and its statement are unchanged.

`model_review.md` records the completed arithmetic run, the four remaining division gaps, and `plain_row_step_other`.
No soundness assumption, `NextPCNoWrap` premise, restriction, or language change was added.

### Declarations and elaboration times

The following tables include every explicit new, moved, or newly proved declaration in the two Part B modules, including private helpers.
Locations are relative to `JoltConstraints/Soundness/Layer6/` at the report snapshot.
Theorem times measure proof elaboration; definition and structure times measure command elaboration, including generated declarations.
“Staged” identifies the sole new `sorry`.

#### `PlainRow.lean`

| Declaration | Line | Visibility | Status | Seconds |
| --- | ---: | --- | --- | ---: |
| `DivisionArithmeticRow` | 30 | Public | Moved definition; unchanged | 0.007454 |
| `PlainRow` | 40 | Public | Definition | 0.004050 |
| `DivisionArithmeticRow.plain` | 47 | Public | Proved | 0.041937 |
| `RunExtends.refl` | 53 | Public | Proved | 0.013883 |
| `RunExtends.trans` | 59 | Public | Proved | 0.023495 |
| `rows_block_property` | 79 | Private | Proved | 0.026723 |
| `expand_program_block` | 105 | Private | Proved | 0.018838 |
| `firstAccessIsWrite_read_before` | 134 | Private | Proved | 0.019366 |
| `expansion_sources_live` | 163 | Public | Proved | 0.303940 |
| `expansion_row_countdown` | 219 | Private | Proved | 0.025092 |
| `expansion_row_remaining` | 245 | Private | Proved | 0.005155 |
| `expansion_order_push` | 258 | Private | Proved | 0.040853 |
| `expansionLive_after` | 281 | Private | Proved | 0.010204 |
| `adjacent_push` | 300 | Private | Proved | 0.022977 |
| `appendUntrustedRow` | 333 | Public | Definition | 0.529717 |
| `trace_push_observations` | 389 | Private | Proved | 1.156849 |
| `representsRows_push` | 405 | Private | Proved | 0.026668 |
| `finalTraceState_push` | 445 | Public | Proved | 0.002315 |
| `finalTraceState_back` | 450 | Private | Proved | 0.010144 |
| `representsPrefix_push` | 463 | Private | Proved | 0.020766 |
| `interior_progress` | 495 | Private | Proved | 0.290468 |
| `rowLive` | 540 | Private | Definition | 0.001239 |
| `ArithmeticExecution` | 546 | Private | Structure | 2.972016 |
| `arithmeticExecution_write` | 557 | Private | Proved | 0.008199 |
| `arithmeticExecution_assert` | 582 | Private | Proved | 0.025897 |
| `zeroRuntimeAdvice` | 604 | Private | Definition | 0.007466 |
| `arithmetic_execution` | 610 | Private | Proved | 0.246664 |
| `plain_no_memory` | 709 | Private | Proved | 0.025324 |
| `plain_row_ram` | 728 | Private | Proved | 0.018744 |
| `arithmetic_row_observations` | 757 | Private | Proved | 1.976023 |
| `RawRowEntry` | 800 | Public | Definition | 0.142786 |
| `rawEntry_starts` | 818 | Private | Proved | 0.010108 |
| `rawEntry_linked` | 830 | Private | Proved | 0.060439 |
| `rawEntry_prepared` | 849 | Private | Proved | 0.022240 |
| `append_expansion_row` | 874 | Private | Proved | 0.780063 |
| `ExpansionState.interior_pre` | 996 | Public | Proved | 0.112854 |
| `PlainRowExtension` | 1029 | Public | Definition | 0.104923 |
| `arithmetic_plain_row_step` | 1055 | Public | Proved | 0.472771 |
| `plain_row_step_other` | 1120 | Public | Staged | 0.000540 |
| `plain_row_step` | 1138 | Public | Proved | 0.014468 |

#### `DivisionBlock.lean`

| Declaration | Line | Visibility | Status | Seconds |
| --- | ---: | --- | --- | ---: |
| `witnessWord` | 127 | Private | Definition | 0.008181 |
| `witnessWord_of_encoded` | 135 | Private | Proved | 0.006520 |
| `single_advice_index` | 150 | Private | Proved | 0.066237 |
| `patchAdviceWord_runtime` | 181 | Private | Proved | 0.026331 |
| `runtime_advice_isSome` | 199 | Private | Proved | 0.018041 |
| `arithmetic_exec_eq` | 204 | Private | Proved | 0.007383 |
| `expansionInstructions_at` | 211 | Private | Proved | 0.005663 |
| `arithmetic_advice_row_run` | 223 | Private | Proved | 0.266732 |
| `arithmetic_advice_suffix_run` | 262 | Private | Proved | 0.362395 |
| `arithmetic_advice_sequence_run` | 358 | Public | Proved; statement unchanged | 0.020650 |

The existing helpers `instructionTemporary_index` and `temporary_source` in `Layer7/StallSuffix.lean:253` and `:261`, and `nonterminal_virtual_row_pc_plus_one` and `nonterminal_at_last_cycle_impossible` in `Layer7/LastJump.lean:229` and `:370`, were made public in place.
Their statements and proof bodies are unchanged; the StallSuffix helpers also received docstrings.
These are visibility changes to existing proofs, not newly proved declarations.

No new proof takes ten seconds.
The slowest proof is the shared `arithmetic_row_observations` at 1.976023 seconds; `trace_push_observations` takes 1.156849 seconds.
Both directly establish the common observation equations once, avoiding separate proofs for the instruction cases or additional intermediate observation lemmas solely to reduce elaboration time.
The `ArithmeticExecution` structure takes 2.972016 seconds including generated declarations.
The completed public `arithmetic_advice_sequence_run` proof takes 0.020650 seconds, with its suffix-induction helper taking 0.362395 seconds.
No proof limit was raised.

### Validation and scope

`lake build JoltConstraints.Soundness.Layer6.DivisionBlock` passed with 8,675 jobs.
The final `lake build JoltConstraints` passed with 8,808 jobs.
An earlier aggregate attempt encountered another agent's in-progress `TerminalNextPC.lean`; after that file changed, the aggregate build passed without an edit to it by this task.
`git diff --check` passed before writing this report.
Normalized signature comparisons confirmed the unchanged statements of `arithmetic_advice_sequence_run`, `division_block`, and the four remaining DivisionBlock gaps.
The moved classifier's body is identical to its original definition.

The transitive axiom audit found no reachable direct `sorryAx` user from `RunExtends.refl`, `RunExtends.trans`, `expansion_sources_live`, `appendUntrustedRow`, `ExpansionState.interior_pre`, `arithmetic_plain_row_step`, or `arithmetic_advice_sequence_run`.
These proved roots use only a subset of `propext`, `Classical.choice`, `Quot.sound`, and `sys_enable_experimental_extensions`, with no native bit-vector axiom.
For generic `plain_row_step`, the sole reachable declaration directly using `sorryAx` is exactly `plain_row_step_other`.
The audit checks these conditions rather than merely printing the axiom lists.

At the final aggregate audit snapshot, `JoltInstance.soundness` still reaches these staged gaps:

- `soundness_prover_accepts`.
- `division_append_honest`.
- `division_program_honest`.
- `division_expansion_layout`.
- `division_program_result`.
- `row_step`.
- `terminal_next_unexpanded_pc`.
- `soundness_spoil_asserts_pass`.

Its axiom list also retains the existing `JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5` dependency.
Part B adds no `bv_decide`, `native_decide`, `decide +kernel`, or axiom declaration.
The only new staged gap is the planned `plain_row_step_other`; the former `arithmetic_advice_sequence_run` gap is removed.

Build logs are `/private/tmp/layer6-stage4a-part-b-division-build.log` and `/private/tmp/layer6-stage4a-part-b-final-build.log`.
The core and aggregate audit scripts and logs are `/private/tmp/layer6-stage4a-part-b-core-axioms.{lean,log}` and `/private/tmp/layer6-stage4a-part-b-axioms.{lean,log}`.
Profiling used `lake env lean -j1 -Dtrace.Elab.async=true -Dtrace.Elab.command=true -Dtrace.profiler=true -Dtrace.profiler.threshold=1000` on the two Part B modules.
The profiling logs are `/private/tmp/layer6-stage4a-part-b-profile-PlainRow.log` and `/private/tmp/layer6-stage4a-part-b-profile-DivisionBlock.log`, and the extracted declaration timings are `/private/tmp/layer6-stage4a-part-b-declarations.json`.

I made no edits to `BoundaryStart.lean`, `Layer7/TerminationStore.lean`, or `layout_facts.lean`.
Other agents' edits were preserved, including their concurrent changes in LastJump and StallSuffix.
Concurrent commits advanced HEAD and already included the two StallSuffix visibility changes; I made no commit.
The existing Part A report is preserved above.
Work stops after this Part B report.
