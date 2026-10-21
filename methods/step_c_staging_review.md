# Step (c): checker staging review, 2026-10-21

Historical staging record: Ari approved this proposal, and the checker is now integrated.
See [the integration report](step_c_closing_report.md) for the current state.
The remainder of this document records Part 1 of `step_c_closing_plan.md` at the original review boundary.
The starting revision was `7e46ef8` on `feat/soundness`, with no modified Lean files.
The current `sequenceOk`, `nativeRowOk`, proof macros and existing proved declarations are intact.
Integration and proofs await Ari's review.

## Staged declarations

`expansion_facts.lean` now defines the four separate Boolean checks `jumpEndNoStore`, `sequenceJalrsVirtual`, `virtualJalrBaseUnwritten` and `advicePairsOk`, plus `nativeJalrBaseOk`.
`virtualJalrBaseUnwritten` uses the existing `ExpansionTempLiveness.writes` check for virtual destinations.
The existing canonical-operand check is still needed to exclude an architectural destination aliasing a virtual base's witness address.
`advicePairsOk` accepts precisely a nonzero architectural destination or the x0 rewrite's virtual register 40, followed by the multiply with matching destination, source and multiplier.
The operand patterns encode the existing `sideEffectingRdZeroDst` and `adviceReadSource` forms without importing a Layer 5 proof module into the checker.
Checking `advicePairsOk [instruction]` excludes a native narrow advice load because it has no following multiply.

Two new named obligations use `sorry`:

- `ExpansionFacts.expand_additional_checks`: every source expansion satisfies the four sequence checks, or the native JALR and singleton advice checks.
- `ExpansionFacts.expand_instruction_checks`: materialization preserves the ordered instruction list and provides the existing and proposed checks for its sequence or native case.

`expanded_virtual_jalr_source` retains its hypotheses and its no-write conclusion for every bytecode row at the same address.
Its unused conjunct identifying the source as ECALL or MRET was removed as directed in Part 2.
The other four existing gaps retain their statements and `sorry` proofs.
No completeness theorem statement changed.
The move of `expanded_same_source_rows`, deletion of `Emission.lean`, replay proofs and cleanup remain after review.

## Proposed checker integration

After approval, replace `sequenceOk` with:

```lean
def sequenceOk (instructions : List JoltISA.Instr) : Bool :=
  rowsOk instructions && shiftsOk instructions &&
    ExpansionTempLiveness.tempsReadAfterWrite instructions &&
    jumpEndNoStore instructions &&
    sequenceJalrsVirtual instructions &&
    virtualJalrBaseUnwritten instructions &&
    advicePairsOk instructions
```

Replace `nativeRowOk` with:

```lean
def nativeRowOk (instruction : JoltISA.Instr) : Bool :=
  x0Ok instruction && JoltRegisterEncoding.instructionIsCanonical instruction &&
    immShiftOk instruction && !isRegisterShift instruction &&
    ExpansionTempLiveness.tempsReadAfterWrite [instruction] &&
    nativeJalrBaseOk instruction && advicePairsOk [instruction]
```

Both native additions are necessary.
Evaluation of the current `nativeRowOk` returned `true` for `JALR (.vreg 40) (.vreg 34) 0` and `VirtualAdviceLoad (.xreg (.Regidx 1)) 1`.
These are examples of syntax the current check accepts, not claims that native source instructions emit those rows.

Add the new check definitions to the existing `rows_ok`, `pure_rows_ok` and `native_ok` simplification lists, using the existing expansion table.
Prove the staged source-check obligation through the strengthened `expand_ok`, and then prove the materialization lift.

## Five positional sequence consumers

The following line numbers identify the sites before this staging change.
The new projection lemmas will each take `instructions` and `ok : sequenceOk instructions = true` and return the named check's equality to `true`.

1. `expansion_facts.lean:753`, the sequence case of `expand_temps_ok`:

   ```lean
   | sequence rows =>
       exact sequenceOk_tempsReadAfterWrite rows ok
   ```

2. `trace_interface.lean:480`, `stamp_sequence_rowOk`:

   ```lean
   have rowChecks := sequenceOk_rowsOk instructions ok
   have shiftChecks := sequenceOk_shiftsOk instructions ok
   obtain ⟨rowOk, notLast⟩ := rowsOk_rows instructions rowChecks k inInstructions
   ```

   Its later `shiftsOk_rows` call will use `shiftChecks` in place of `ok.1.2`.

3. `trace_interface.lean:572`, the sequence case of `expand_instruction_shiftPairs`:

   ```lean
   exact stamp_sequence_shiftPairs _ _ instructions
     (sequenceOk_shiftsOk instructions ok)
   ```

4. `Soundness/Layer5/HostCallExpansion.lean:80`, `host_not_in_sequence`:

   ```lean
   exact rowsOk_no_host instructions
     (ExpansionFacts.sequenceOk_rowsOk instructions good)
   ```

5. `Soundness/Layer7/Emission.lean:403`, `sequence_jalr_terminal`:

   ```lean
   have rowsOk := ExpansionFacts.sequenceOk_rowsOk instructions good
   ```

Each replacement removes the corresponding `simp only [sequenceOk, Bool.and_eq_true]` destructuring.
The fifth site disappears when Part 2 deletes `Emission.lean`.

There are also three positional native consumers affected by the proposed native additions:

- `expansion_facts.lean:750`, the native case of `expand_temps_ok`, needs `nativeRowOk_tempsReadAfterWrite` applied to `ok.1`.
- `trace_interface.lean:502`, `expand_instruction_rowOk`, needs projections for `x0Ok`, canonical operands and `immShiftOk`.
- `trace_interface.lean:562`, `expand_instruction_shiftPairs`, needs a projection giving `isRegisterShift instruction = false`.

These native projections are proposed for the same integration pass.

## Initial audit

`lake build JoltBytecode JoltConstraints` passed with 8801 jobs and no errors before edits.
The direct `sorry` users reachable from `JoltInstance.soundness_stopping` are exactly:

- `stall_suffix_initial`;
- `stall_system_jalr_step`;
- `expanded_jalr_operand_forms`;
- `stable_stall_source_no_store`.

The fifth listed gap, `expanded_virtual_jalr_source`, is currently unused.
`soundness_reconstruct_trace` reaches those same four gaps plus `soundness_execution_prefix_agreement`.
No other `sorry` reaches either audited theorem.

Both axiom sets are:

```text
propext
sorryAx
sys_enable_experimental_extensions
Classical.choice
Quot.sound
JoltConstraints.branch_target_toNat._native.bv_decide.ax_1_5
```

The final entry is an existing dependency; this staging change introduces no use of `bv_decide`.
Removing `sorryAx` from stopping is the later closing target, not a result of this staging pass.

The initial source scan found these existing gaps outside the five stopping gaps:

| Declaration | Existing gaps |
|---|---|
| `JoltInstance.soundness_execution_prefix_agreement` | One staged proof. |
| `JoltInstance.soundness_prover_accepts` | Helper C, with its existing approved known-false status. |
| `JoltInstance.soundness_spoil_asserts_pass` | Helper D. |
| `JoltConstraints.Soundness.untrustedAnswerLanguage_implies_inLanguage` | The main worktree's tape-rebuild obligation. |
| `JoltConstraints.honestWitness_ramAddrEqRs1PlusImmIfLoadStore` | Completeness constraint 1. |
| `JoltConstraints.honestWitness_ramValEqInitialPlusPrefixRamInc` | Completeness constraint 37. |
| `JoltConstraints.honestWitness_ramValFinalEqInitialPlusRamInc` | Completeness constraint 38. |
| `JoltConstraints.HonestTrace.corrected_witness_params_ram_bounds` | Completeness RAM-size bounds. |
| `System.mretProgram_eq_sail_projected` | One existing `sorry` inside its proof. |
| `RiscvInstruction.equivalenceStatement_holds` | Six existing branch-local gaps: ECALL, EBREAK, LR.W, SC.W, LR.D and SC.D. |

The two new checker obligations are the only additional `sorry` declarations in this pass.

## Validation and timing

The final `lake build JoltBytecode JoltConstraints` passed with 8801 jobs and no errors.
`git diff --check` passed.
The final axiom sets and direct `sorry` dependencies exactly match the initial audit above.
The two new staged obligations are not yet used by stopping or completeness.

Timings use Lean's `#time` around each declaration, with `Elab.async=false` and one worker, on temporary copies of the source.
The module totals sum the timed definitions, theorems and macros, excluding imports and process startup.
These are individual measurements, not performance bounds.

| New or changed declaration | Elaboration |
|---|---:|
| `ExpansionFacts.jumpEndNoStore` | 12 ms |
| `ExpansionFacts.sequenceJalrsVirtual` | 12 ms |
| `ExpansionFacts.virtualJalrBaseUnwritten` | 3 ms |
| `ExpansionFacts.advicePairsOk` | 32 ms |
| `ExpansionFacts.nativeJalrBaseOk` | 2 ms |
| `ExpansionFacts.expand_additional_checks` | 2 ms |
| `ExpansionFacts.expand_instruction_checks` | 3 ms |
| `JoltInstance.expanded_virtual_jalr_source` | 2 ms |

The restated gap was timed separately under a temporary namespace with the same statement and `sorry` body.
The timings of the staged theorems measure their statements and placeholders, not future proofs.

| `expansion_facts.lean` | Before staging | After staging |
|---|---:|---:|
| Total declaration elaboration | 11.375 s | 11.732 s |
| Whole Lean process, including imports and startup | 16.73 s | 17.53 s |

These after-times measure the separate definitions and staged statements only.
The stronger checker has not been integrated, so its performance remains to be measured after approval.
The status documents now remove the already-proved stopping obligations and record the five remaining gaps plus the two new staging obligations.
