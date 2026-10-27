# Advice fix audit: stopped before implementation

The plan is insufficient as written: step 3 overlooks the actual statement of `JoltInstance.represented_last_control_read`.
Under the proposed weakening of `RepresentsRows`, that statement still requires equality at temporary-register reads, including the plan's REM counterexample.
I stopped under the user's audit instruction and the plan's explicit stop condition at `methods/advice_fix_plan.md:51`.
No Lean declaration, existing documentation, restriction, or hypothesis was changed.
This report is the only file added by this task; the pre-existing working-tree changes were preserved, and nothing was committed.

## Blocking claim and missing fact

Step 3, `methods/advice_fix_plan.md:38`, describes `represented_last_control_read` as applying at the last control row and says its first source cannot be an instruction temporary.
The theorem at `JoltConstraints/Soundness/Layer7/StallSuffix.lean:255` has no hypothesis saying that its instruction is a branch or JALR, that `last` is at the end of the run, or that either source is not a temporary.
Its `reads` hypothesis at line 273 accepts any source register selected by either bytecode operand selector.
Its `observed` hypothesis at line 278 only identifies the trace's operand value with the supplied row's pre-state value; it does not compare that value with the witness.

The conclusion at line 282 is:

```lean
witness.RegistersVal (TraceWitness.sourceRegisterAddress source) before =
  ((JoltISA.sourceValue source last.preState).toNat : F)
```

The proof obtains the required witness-to-trace equality from unconditional `represented.rs1` or `represented.rs2` at lines 296–297.
After step 2, those projections would require a non-temporary operand, which this theorem's hypotheses cannot establish.
A lemma about control operands in expanded bytecode cannot fill this gap because this theorem does not assume a control instruction.
The missing fact is that the represented operand at the selected cycle is not an instruction temporary, with the relevant row correspondence established.

## The plan's REM example also breaks this consumer

Take `rem a0, a1, zero` with `a1 = 7`, witness advice `q = 5`, and honest-run advice `q = 0`.
Choose `before` at the overflow-check row, `last` to be that actual row of the honest run, `second = false`, and `source = .vreg (BitVec.ofNat 7 40)`.
This is allowed by the theorem's statement despite the parameter name `last`.
The selected instruction is `VirtualAssertMulUNoOverflow v40 v42`, so `reads` selects register 40 and `observed` identifies the honest trace's value as zero.
The witness's register-table entry is five at that cycle, so the unchanged conclusion would require `(5 : F) = 0`.
The Jolt field characteristic bound excludes that equality.

The expansion is at `JoltBytecode/JoltISA/ExpansionsAutomated.lean:170`.
The following table checks the proposed representation on its nine rows; operand pairs are the pre-state Rs1Value and Rs2Value, with zero for an absent operand.
Every row has the same PC in the two executions and zero RamAddress because this expansion has no memory access.

| Row | Instruction | Witness operands | Honest operands | Comparisons required by the proposal |
|---|---|---|---|---|
| 1 | Advice into v40 | (0, 0) | (0, 0) | Both absent operands agree |
| 2 | NegateIf v41, a1, a1 | (7, 7) | (7, 7) | Both architectural operands agree |
| 3 | NegateIf v42, zero, zero | (0, 0) | (0, 0) | Both architectural operands agree |
| 4 | AssertMulUNoOverflow v40, v42 | (5, 0) | (0, 0) | Both operands are temporaries and exempt |
| 5 | MUL v43, v40, v42 | (5, 0) | (0, 0) | Both operands are temporaries and exempt |
| 6 | AssertLTE v43, v41 | (0, 7) | (0, 7) | Both operands are temporaries and exempt |
| 7 | SUB v43, v41, v43 | (7, 0) | (7, 0) | Both operands are temporaries and exempt |
| 8 | AssertValidUnsignedRemainder v43, v42 | (7, 0) | (7, 0) | Both operands are temporaries and exempt |
| 9 | NegateIf a0, a1, v43 | (7, 7) | (7, 7) | The architectural first operand agrees; the second is exempt |

Thus the proposed relation removes precisely the equality that this existing generic consumer still asserts.
This is a source-level counterexample analysis, not a newly formalized complete constraint witness.

## Pinned Jolt checks supporting the finding

I read these sources with `git show 8bbb2357:<path>`, not from the checked-out Jolt HEAD.

- Jolt's expander emits this nine-row sequence: `jolt/crates/jolt-program/src/expand/division/rem.rs:15-24`.
- Jolt's allocator assigns instruction temporaries from registers 40–47: `jolt/crates/jolt-program/src/expand/allocator.rs:133-143`.
- Jolt's tracer supplies quotient magnitude zero for a zero divisor: `jolt/tracer/src/instruction/rem.rs:44-55`.
- The overflow assertion accepts multiplication by zero: `jolt/tracer/src/instruction/virtual_assert_mulu_no_overflow.rs:22-24`.
- The remainder assertion accepts any remainder when the divisor is zero: `jolt/tracer/src/instruction/virtual_assert_valid_unsigned_remainder.rs:23-25`.
- The verifier's right-lookup/input equality is gated off by the Advice flag: `jolt/crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs:282-293`, matching `JoltConstraints/Constraints/RightLookupEqRightInputOtherwise.lean:12`.

The Lean `rem_advice_value` definition at `JoltBytecode/InstructionEquivalence/Instructions/ALUAdviceFamily/Div_math.lean:55` agrees with the tracer's zero-divisor choice.
I also checked that the five final-state theorems and three advice-uniqueness theorems listed in the plan have the stated kinds of conclusions.
These checks support the original diagnosis but do not repair the consumer's missing hypothesis.
The audit stopped at this blocker; this report does not certify every remaining claim in the plan.

## Consumer search and necessary plan revision

Repository-wide searches of Lean files for `.rs1`, `.rs2`, `RepresentsRows`, its explicit projections and constructor, and `toRepresentsRows` found only these two direct operand-projection uses:

| Use | Location | Disposition |
|---|---|---|
| `represented.rs1 before inRun` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:296` | Cannot repair under the unchanged generic statement |
| `represented.rs2 before inRun` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:297` | Has the same missing non-temporary hypothesis |

The generic helper has three call sites, all in that file: the two branch operands in `stall_suffix_initial_branch` at lines 2629 and 2641, and the JALR base in `represented_last_jalr_base` at line 2693.
Those callers have instruction-shape and row-correspondence facts that the generic helper lacks.
The plan should explicitly authorize narrowing or replacing the generic helper, or moving the operand bridge into these callers, where the proposed expanded-bytecode fact can be applied.
The current instruction at `methods/advice_fix_plan.md:50` forbids adding a premise, and line 51 specifically requires stopping on a consumer that needs temporary reads, so no such revision was implemented.

## Changes, timings, build, and axiom audit

- Changed or new Lean declarations: none; there are no old/new statement changes or elaboration timings to report.
- Added hypotheses, restrictions, `sorry`, or `bv_decide` uses: none.
- Build: not run, because the audit failed before implementation.
- Axiom audit: not run; no new claim is made about the existing dependency graph.
- A and the prefix theorem were left untouched, as were all pre-existing changes under `methods/`.

Work stopped after writing this report.

## Implementation after Ari amended step 3

The findings above describe the initial plan and are retained unchanged.
Ari subsequently authorized exactly one additional hypothesis on `represented_last_control_read`, discharged by its three callers.
The amended fix is now implemented in this checkout on `feat/soundness`, without a commit.
The full build and axiom audit passed.
A and `soundness_execution_prefix_agreement` were not proved or edited.

### Remaining source checks

All Jolt source checks used public pin `8bbb2357` through `git show`, without modifying Jolt's checkout.
The remaining checks found no further obstruction to the row-observation fix:

- The REMU and REMW recipes keep quotient advice in instruction temporaries, with architectural writeback at the end: `jolt/crates/jolt-program/src/expand/division/remu.rs:14-59` and `jolt/crates/jolt-program/src/expand/division/remw.rs:8-27`.
- The shared unsigned-word recipe zero-extends the divisor, permits arbitrary quotient advice when it is zero, and checks only the sign-extended low word for DIVUW's divide-by-zero result: `jolt/crates/jolt-program/src/expand/division/shared.rs:8-38`.
  This confirms the claimed free upper 32 advice bits for DIVUW; REMUW's remainder also remains independent of the quotient when the divisor is zero.
- The corresponding Lean expansions are `JoltBytecode/JoltISA/ExpansionsAutomated.lean:187`, `:371`, `:412`, and `:429`.
  The eight `*Program_sound` conclusions match the distinction recorded in the initial audit: three establish advice uniqueness, while five establish the final Sail state.
- `SourceInstruction.expand` at `JoltConstraints/expansions.lean:22` emits architectural branch operands and an architectural base for a source JALR.
  Jolt's x0 rewrite changes the destination, preserving the sources: `jolt/crates/jolt-program/src/expand/mod.rs:126-170`.
  The system expansions read persistent virtual bases 34 and 36: `jolt/crates/jolt-program/src/expand/control_flow/ecall.rs:15-19,47-50` and `jolt/crates/jolt-program/src/expand/control_flow/mret.rs:11-16`, matching `JoltBytecode/JoltISA/Expansions/System.lean:79,93`.
- `joltRegisterSlot` at `JoltBytecode/JoltISA/VirtualRegisters.lean:215` classifies exactly 40–47 as instruction temporaries; `System.systemProject` at `JoltBytecode/JoltISA/SystemProjection.lean:25` ignores them while retaining the persistent CSR values.
  `ExpansionFacts.expand_temps_ok` at `JoltConstraints/expansion_facts.lean:913` supplies the per-expansion first-write-before-read property.
- The honest-advice hypothesis remains necessary for `soundness_stopping` and the execution-prefix restrictions using `UntrustedAnswerRun.NextStep`.
  Source-only restrictions, such as `HostCallRdZero`, are separate from those run restrictions and are unchanged.
- The repository-wide consumer search still finds only the two operand projections in `represented_last_control_read`.
  The final observation consumers retain the same PC, RAM-address, and RAM comparisons.

The plan's wording about differences being “inside one division expansion” needs the observation-level interpretation.
An old temporary value can remain stored after that expansion; liveness guarantees that a later expansion writes the temporary before reading it, rather than resetting the temporary at the boundary.
The existing HostIO x0 case also leaves its dead temporary outside register agreement (`Soundness/Layer5/HostCallRegisterFrame.lean:72`); the proposed exclusion already covers that temporary.
Neither qualification requires a further change to `RepresentsRows`.
The documentation now states the write-before-read fact explicitly.

### Declarations and statement changes

All names below are in `JoltInstance`; the five auxiliary theorems are private.
Times are seconds from Lean's profiler, excluding startup and imports.
For the predicate and structure, the reported time is command elaboration; for theorems, it is proof elaboration.
The final theorem profiling used `lake env lean -j1 -Dtrace.Elab.async=true -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 JoltConstraints/Soundness/Layer7/StallSuffix.lean`.
The predicate and structure were measured with the same options and threshold 1 on `ExecutionPrefix.lean`.
No measured proof in these files exceeded ten seconds.

| Declaration | File and line | Old → new statement or proof change | Elaboration |
|---|---|---|---:|
| `IsInstructionTemporary` | `JoltConstraints/Soundness/Layer6/ExecutionPrefix.lean:17` | New predicate on `Fin 128`, true exactly when `joltRegisterSlot` returns `instructionTmp` | 0.004 |
| `RepresentsRows` | `JoltConstraints/Soundness/Layer6/ExecutionPrefix.lean:29` | Unconditional in-range Rs1/Rs2 equality → equality when every register in the corresponding optional operand is not an instruction temporary; other fields unchanged | 0.133 |
| `instructionTemporary_index` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:251` | New: a classified temporary has address `40 + index.val` for some `index : Fin 8` | 0.132 |
| `temporary_source` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:257` | New: a source encoded at `40 + index.val` is the virtual source with that address | 0.023 |
| `branch_operand_forms` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:273` | New: any of the six branch forms has read sources `[lhs, rhs]` and the corresponding two bytecode selectors; the immediate is `BitVec 128` | 0.011 |
| `control_operand_source` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:283` | New: a selected branch/JALR operand is the encoding of a source in `readSources` | 0.183 |
| `unwritten_no_read` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:302` | New: first-write-before-read plus no writes anywhere in an instruction list implies no member reads that register | 0.003 |
| `expanded_control_read_not_temporary` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:322` | New: a selected operand of a branch or JALR row in expanded bytecode is not an instruction temporary | 0.186 |
| `represented_last_control_read` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:395` | Same conclusion and previous hypotheses, plus the authorized `nonTemporary` hypothesis below | 0.409 |
| `stall_suffix_initial_branch` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:2761` | Statement unchanged; both operand calls discharge `nonTemporary` using the shared expanded-bytecode lemma | 4.996 |
| `represented_last_jalr_base` | `JoltConstraints/Soundness/Layer7/StallSuffix.lean:2833` | Statement unchanged; its base-operand call discharges `nonTemporary` using the same lemma | 0.589 |

The only added hypothesis on an existing theorem is:

```lean
(nonTemporary :
  ¬ IsInstructionTemporary (TraceWitness.sourceRegisterAddress source))
```

In `RepresentsRows.rs1`, the new guard is:

```lean
∀ register ∈ JoltConstraints.bytecodeRs1Register
  trace.bytecode[trace.rows[t.val].rowIndex].instruction,
  ¬ IsInstructionTemporary register
```

The Rs2 guard substitutes `bytecodeRs2Register`.
For `none`, the guard is vacuous, so an absent operand still has to agree.
`RepresentsPrefix`, `Represents`, A, and the prefix theorem retain their existing declaration text and inherit the changed row relation.
No restriction or premise on the soundness theorem was added.

The expanded-bytecode proof uses the existing source-layout and expansion checks rather than splitting over the source instruction set.
A native row cannot read an uninitialized temporary; sequences have no branches, and their JALR base is unwritten throughout the sequence, so temporary liveness rules it out as a temporary.
`unwritten_no_read` proves that list argument once, and `branch_operand_forms` shares the branch-selector argument between its consumers.
`instructionTemporary_index` uses ordinary kernel-checked `decide` to evaluate the finite register classifier.
No new `bv_decide`, `native_decide`, `decide +kernel`, raised limit, or remaining `sorry` was introduced.

### REM and repaired uses

The nine-row REM table in the initial audit applies unchanged to the implemented relation.
Rows 4 and 5 are the only differing operand observations: their first operand reads temporary 40, containing 5 in the witness and 0 in the honest run.
Those comparisons are exempt, while rows 1–3 and 9 satisfy every required absent or architectural operand comparison.
Rows 6–8 have equal temporary operands anyway, every row has matching PC and zero RAM address, and both executions write 7 to a0.
This remains a source-level calculation, not a newly formalized complete constraint witness.

The final whole-repository search covered `.rs1`, `.rs2`, explicit `RepresentsRows.rs1`/`.rs2`, `RepresentsRows.mk`, `RepresentsRows`, and `toRepresentsRows`.
The only direct projections are now at `StallSuffix.lean:453` and `:455`.
Before using them, `represented_last_control_read` derives equality of the represented and selected bytecode rows from PC agreement and uniqueness of the bytecode selector, then transports the authorized non-temporary fact to the represented row.
Its three callers are the two branch operands in `stall_suffix_initial_branch` and the JALR base in `represented_last_jalr_base`, repaired as listed above.

The four requested passages in `methods/soundness.md` and the prefix-theorem row under “Proofs owed” in `JoltConstraints/model_review.md` were updated.
The “Running the Layer 6 agents” section and the pre-existing plan changes were not edited by this task.
Concurrent changes to `AGENTS.md` and the pin-update documents were also left alone.

### Build and axiom audit

`lake build JoltConstraints` completed successfully with 8800 jobs.
The build retains existing warnings; the changed files have no new unproved declaration beyond the existing prefix theorem.
`git diff --check` passed.
An initial build caught a 64-bit annotation in the new branch-selector helper; it was corrected to the model's 128-bit branch immediate before the successful build and final profiling.

`#print axioms JoltInstance.soundness` reports:

```text
propext
sorryAx
sys_enable_experimental_extensions
Classical.choice
Quot.sound
JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5
```

A traversal of the compiled theorem's declaration dependencies found exactly these reachable declarations directly using `sorryAx`:

```text
JoltInstance.soundness_execution_prefix_agreement
JoltInstance.soundness_prover_accepts
JoltInstance.soundness_spoil_asserts_pass
```

The new `expanded_control_read_not_temporary` depends only on `propext`, `Classical.choice`, and `Quot.sound`.
The repaired consumers and `soundness_stopping` have no `sorryAx`; the existing branch-target `bv_decide` axiom remains unchanged.
The same audit file type-checked examples that register 40 is temporary, register 36 is not, and the absent-operand guard is vacuous.
No claim is made that the remaining prefix theorem, helper C, or helper D has been proved.

No commit was made.
Work stopped after appending this implementation report.
