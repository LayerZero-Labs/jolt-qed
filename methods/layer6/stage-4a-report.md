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
