# Witness columns and verifier inputs: Lean types against what Jolt's verifier knows

Date: 2026-11-12.
Jolt commit: a16z/jolt `a6b6dc717` (contains a16z/jolt#2190, `4e55c9a5f`).
Lean commit: `86e3c7a` (the Lean implementation) on the pushed branch `t5/advice-field`, based on `inline/t1-driver` at `b648846`.
The local worktree branch is `track/t5-advice-field`; `t5/advice-field` is the name to cite.
Line numbers in the statement inventory refer to `6a44511` and are unchanged at the branch head; the commits after `86e3c7a` change only docstrings and Markdown.
Scope: every column of `WitnessType` (`JoltConstraints/witness.lean`) and every other input of the relation `AllConstraints` (`JoltConstraints/Constraints/All.lean`).
For each one, this note compares the value Jolt's verifier has with the Lean type, and lists the mismatches.
Only the untrusted-advice mismatch is fixed on this branch; the other fixes below are proposals.

## Summary

Every witness column is a field element in Lean, and Jolt's verifier knows nothing more about any of them than that it is a field element, so the witness columns have no typing gap.
The gaps are in the other inputs of the relation, which Lean modelled as bytes or 64-bit words while Jolt's verifier holds only a commitment:

| Input | Jolt's verifier has | Lean type before | Status |
| --- | --- | --- | --- |
| Untrusted advice | A commitment to field elements, one per word of the untrusted-advice block | Bytes in `JoltPrivateInputs.untrusted_advice` | Fixed on this branch: `AllConstraints` takes `untrustedAdvice : Nat → F` |
| Size of the untrusted-advice block | `layout.max_untrusted_advice_size / 8` words, with the size rounded up to a multiple of 8 | Tracer accepts only `config.max_untrusted_advice_size` bytes | New temporary premise `UntrustedAdviceBlockFits`; Jolt fix proposed below |
| Trusted advice | A commitment, made by a trusted party | Bytes in `JoltInstance.trusted_advice` | Unchanged; holds if the trusted party commits to packed bytes |
| Program image and bytecode in committed-program mode | Commitments `ProgramImageInit` and `ProgramBytecode` | Public `JoltInstance.program` | Out of scope of the current model |
| Execution tape (`advice_tape`) | Nothing: it is not an input of the verifier | Bytes in `JoltPrivateInputs.advice_tape` | No gap: the relation ignores it (`AllConstraintsOnBytes.advice_tape_irrelevant`) |
| Inline advice (`inline_advice`, added by I1b) | Nothing directly: the words appear only as values of `VirtualAdvice` rows, which are witness columns | 64-bit words in `JoltPrivateInputs.inline_advice` | No gap: the relation ignores it (`ConstraintContext.withInlineAdvice`, on the merged branch `inline/i1b-t5`) |

## Witness columns

Jolt commits to these polynomials (`crates/jolt-claims/src/protocols/jolt/ids.rs:348`): `RdInc`, `RamInc`, `InstructionRa(i)`, `BytecodeRa(i)`, `RamRa(i)`, `TrustedAdvice`, `UntrustedAdvice`, `ProgramImageInit` and `ProgramBytecode`.
Every other polynomial is virtual: the verifier learns only evaluation claims about it, which sumchecks reduce to openings of committed polynomials and to public data.
In both cases the verifier knows a field element and nothing about its range.

Every column of `WitnessType F params` has values in `F` (`witness.lean:239`):

* The committed columns `RdInc`, `RamInc`, `InstructionRaChunk`, `BytecodeRaChunk` and `RamRaChunk` are committed field elements in Jolt and `F` in Lean.
* The virtual columns (`PC`, `UnexpandedPC`, `Imm`, the register and RAM values, the instruction inputs, lookup operands and outputs, `Product`, the branch and jump flags, the next-row columns, `OpFlags`, `InstructionFlags`, `LookupTableFlag`, `InstructionRafFlag`, `RamHammingWeight`, `Rs1Ra`, `Rs2Ra`, `RdWa`, `RegistersVal`, `RamRa`, `RamVal`, `RamValFinal` and `InstructionRa`) are field elements in both.

The soundness proof derives every range fact it uses from the constraints, not from the types.
For example, it shows that every row with the Load flag reads a 64-bit word (`load_ramReadValue_word` in `Soundness/UntrustedAdvice/LoadWords.lean`) from the lookups of the load row or of the two rows after it.
So the witness columns need no change.

## Untrusted advice (fixed)

Jolt's verifier receives only a commitment to the untrusted advice.
Since a16z/jolt#2190 it adds the committed block to the initial RAM in the RAM value check (`ram_val_check_advice_block`, `crates/jolt-verifier/src/stages/stage4/ram_val_check.rs:482`).
The block starts at the remapped word of `untrusted_advice_start` and holds `max_untrusted_advice_size / 8` words, and each word is an arbitrary field element.

Before this branch, the relation took the advice as bytes, so each initial word of the block was the cast of a 64-bit word.
That relation admitted fewer witnesses than Jolt's verifier accepts, and soundness for it did not cover a prover that commits to a word outside the 64-bit range.

On this branch, `AllConstraints joltInstance untrustedAdvice witness` takes the advice words as `untrustedAdvice : Nat → F`.
The initial value of a RAM word is `committedInitialValue`: the committed word inside the block and the cast of the fixed 64-bit word elsewhere.
`JoltInstance.soundness` proves soundness for this relation by reducing it to the byte relation (`onBytes_of_allConstraints`).
It covers every committed advice word, under one extra premise, `UntrustedAdviceBlockFits` (next section).
The old theorem stays unchanged as `JoltInstance.soundness_onBytes`, which keeps byte advice and does not need that premise.
Every byte input that satisfies the old relation gives advice words that satisfy the new one with the same witness (`allConstraints_of_onBytes`).
A word outside the 64-bit range cannot be loaded before it is overwritten, because every load reads a 64-bit word, so it can be replaced by zero together with a shift of the RAM value columns.

## Size of the untrusted-advice block (new restriction)

The tracer accepts at most `config.max_untrusted_advice_size` bytes of untrusted advice (`tracer/src/lib.rs:374`).
`MemoryLayout::new` rounds that size up to a multiple of 8 (`common/src/jolt_device.rs:397-410`), and the verifier's block spans the rounded size.
If the configured size is not a multiple of 8, the prover can commit to block bytes that no tracer run can hold.
For example, with a configured size of 12 the block has 2 words, and the prover may set the top 4 bytes of the second word.
This gap exists even when every committed word is a 64-bit word.

The branch adds the temporary restriction `JoltInstance.UntrustedAdviceBlockFits`: the rounded size is at most the configured size, which holds exactly when the configured size is a multiple of 8.
It is a separate premise `adviceBlockFits` of `JoltInstance.soundness` and `JoltInstance.sail_soundness`, not a field of `JoltInstance.TemporaryRestrictions`, so `JoltInstance.soundness_onBytes` keeps its old statement.
Proposed Jolt fix: the tracer checks the advice length against the rounded size, or `MemoryLayout::new` rejects a configured size that is not a multiple of 8.

## Trusted advice (not changed)

The instance holds the trusted advice as bytes (`JoltInstance.trusted_advice`), while Jolt's verifier holds only a commitment (NOTE in `JoltConstraints/program.lean` above `JoltInstance`).
The verifier adds the trusted block to the initial RAM in the same way as the untrusted block (`ram_val_check.rs:351-366`).
The model is right only when the trusted party commits to the packed words of some byte string that fits the configured size.
If the trusted party may commit to arbitrary field elements, the same reduction as for untrusted advice applies, and the same block-size gap appears.
Proposed fix, not implemented: either state the honest-commitment premise next to `trusted_advice`, or take trusted advice as field words like the untrusted advice.

## Committed-program mode (out of scope)

When the program is committed, Jolt's verifier holds commitments `ProgramImageInit` and `ProgramBytecode` instead of the program.
The Lean instance always holds the program image (`JoltInstance.program`), so the model covers only the mode where the verifier preprocesses the program itself.
Proposed fix, not implemented: model committed-program mode as a separate instance type once it is in scope.

## Planned inline advice

`docs/inline-precompiles.md` (phase I1b) plans a lemma `allConstraints_inline_advice` that states `AllConstraints joltInstance { privateInputs with inline_advice := words } witness`.
After this branch `AllConstraints` takes untrusted-advice words instead of private inputs, so it cannot read `inline_advice` at all.
On `t5/advice-field` alone, `docs/inline-precompiles.md` stated the planned lemma on the byte relation, as `allConstraintsOnBytes_inline_advice`.
On the merged branch `inline/i1b-t5`, the fact is I1b's `ConstraintContext.withInlineAdvice` (`advice_inputs.lean`): a context for some private inputs is one for the same inputs with other inline advice words, with the same equations.
The soundness proof reaches the byte relation through `onBytes_of_allConstraints`, and `JoltInstance.soundness_onBytes` moves the reconstructed run to the inline advice words with `ConstraintContext.withInlineAdvice`; the spec names that definition.

## Scope of the load argument

The reduction uses that every row with the Load flag reads a 64-bit word.
`expansion_checks.lean` checks the load window (`loadWindowsOk`, part of `sequenceOk`) for the expansion of every `SourceInstruction`.
Jolt's inline builder can emit narrow loads (`InlineExpansionBuilder::emit_ld`, `crates/jolt-program/src/expand/inline.rs:223`), and nothing in Jolt makes an inline recipe range-check the loaded value.
For example, a recipe that loads a byte and then overwrites the destination register supplies no lookup that bounds the loaded word.
On the merged branch `inline/i1b-t5`, the supported inlines are `SourceInstruction`s, and their rows are checked one at a time by `inlineRowOk`.
`inlineRowOk` now also requires `loadRowChecked`: a row with the Load flag must range-check its own value (`loadSelfChecked`, as LD does).
`sequenceOk_of_inlineRowsOk` derives `loadWindowsOk` from it, so the reduction covers the twelve supported inline keys.
Their only loads are LD rows; a future inline with a narrow load would fail `inlineRowOk` until the window check is extended to it.

## Statement changes

Summary:

* `AllConstraints` takes `untrustedAdvice : Nat → F` instead of `privateInputs`; the old relation is `AllConstraintsOnBytes`, and the old soundness theorem is `JoltInstance.soundness_onBytes`.
* Added hypotheses: only `adviceBlockFits` on `JoltInstance.soundness` and `JoltInstance.sail_soundness`.
* The soundness lemmas of layers 1 to 4 and 6 take `FieldConstraintEquations` at an arbitrary `initialValue : Nat → F`; none gains a hypothesis.
* Removed: `materialized_pairs` and the private `pairs_append` and `pairs_flatten` (`Layer7/AdjacentRows.lean`), replaced by their window versions.
* Unchanged: `InLanguage`, the execution semantics, `Pairs`, and the six fields of `TemporaryRestrictions`.

Every changed or new declaration, with its line at `6a44511` (paths relative to `JoltConstraints/`).
"New" means the declaration did not exist at `b648846`.

`Completeness/All.lean`:

* `HonestTrace.allConstraintsOnBytes_prover_sizes` (line 188): renamed from `HonestTrace.allConstraints_prover_sizes`, statement unchanged.

`Completeness/RamValEqInitialPlusPrefixRamInc.lean`:

* `honestWitness_ramValEqInitialPlusPrefixRamInc` (line 20): passes `ramInitialValue` to the field-valued predicate.

`Completeness/RamValFinalEqInitialPlusRamInc.lean`:

* `honestWitness_ramValFinalEqInitialPlusRamInc` (line 23): passes `ramInitialValue` to the field-valued predicate.

`Completeness/completeness.lean`:

* `JoltInstance.completeness` (line 85): concludes `AllConstraints` at `adviceBlockWords` of the run's initial RAM.
* `JoltInstance.completeness_someWitness` (line 120): quantifies over advice words instead of private inputs.

`Constraints/All.lean`:

* `FieldConstraintEquations` (line 78): new.
* `ConstraintEquations` (line 157): now an abbreviation for `FieldConstraintEquations` at `ramInitialValue initialRam`.
* `_root_.JoltPrivateInputs.noUntrustedAdvice` (line 170): new.
* `untrustedAdviceWordIndex?` (line 181): new.
* `committedInitialValue` (line 199): new.
* `AllConstraintsOnBytes` (line 216): the old `AllConstraints`, statement unchanged.
* `AllConstraints` (line 233): takes `untrustedAdvice : Nat → F` instead of `privateInputs`.

`Constraints/RamValEqInitialPlusPrefixRamInc.lean`:

* `ramValEqInitialPlusPrefixRamInc` (line 16): takes a field-valued initial value.

`Constraints/RamValFinalEqInitialPlusRamInc.lean`:

* `ramValFinalEqInitialPlusRamInc` (line 16): takes a field-valued initial value.

`Soundness/Assumptions.lean`:

* `JoltInstance.UntrustedAdviceBlockFits` (line 67): new.

`Soundness/Layer1/Addresses.lean`:

* `bytecodeRa_zero_or_one` (line 41): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `bytecodeRa_at_most_one` (line 53): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `bytecodeRa_zero_or_unique` (line 72): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `ramRa_zero_or_one` (line 89): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `ramRa_at_most_one` (line 102): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `ramRa_zero_or_unique` (line 126): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.

`Soundness/Layer1/Bytecode.lean`:

* `bytecode_read_of_selected` (line 50): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `unexpandedPC_ne_four` (line 69): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `nextUnexpandedPC_eq_four_of_bytecodeRa_zero` (line 83): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `bytecodeRa_unique` (line 112): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.

`Soundness/Layer1/BytecodeReads.lean`:

* `pc_of_selected_bytecode` (line 19): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `unexpandedPC_of_selected_bytecode` (line 31): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `imm_of_selected_bytecode` (line 43): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `opFlag_of_selected_bytecode` (line 55): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `instructionFlag_of_selected_bytecode` (line 67): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `rs1Ra_of_selected_bytecode` (line 79): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `rs2Ra_of_selected_bytecode` (line 91): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `rdWa_of_selected_bytecode` (line 103): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `lookupTableFlag_of_selected_bytecode` (line 115): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `instructionRafFlag_of_selected_bytecode` (line 129): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.

`Soundness/Layer1/Chunks.lean`:

* `bytecode_chunk_unique` (line 20): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `instruction_chunk_unique` (line 33): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `ram_weight_zero_or_one` (line 46): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `ram_chunk_all_zero` (line 56): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `ram_chunk_unique` (line 70): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.

`Soundness/Layer1/Instruction.lean`:

* `instructionRa_zero_or_one` (line 42): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `instructionRa_at_most_one` (line 56): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `instructionRa_unique` (line 81): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.

`Soundness/Layer1/InstructionReads.lean`:

* `instructionRa_boolean` (line 45): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `instructionLookupRa_zero_or_one` (line 58): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `instructionLookupRa_at_most_one` (line 69): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `instructionLookupRa_unique` (line 88): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `instruction_read_of_selected` (line 110): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `lookupOutput_of_selected` (line 131): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `leftLookupOperand_of_selected` (line 145): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `rightLookupOperand_of_selected` (line 164): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.

`Soundness/Layer1/Ram.lean`:

* `ram_read_of_selected` (line 57): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `ramRa_zero_iff_address_zero` (line 77): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `ram_zero_effects` (line 99): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `ramRa_unique_of_address_ne_zero` (line 117): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.

`Soundness/Layer2/Registers.lean`:

* `rs1Value_of_selected_bytecode` (line 60): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `rs2Value_of_selected_bytecode` (line 78): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `rdWriteValue_of_selected_bytecode` (line 96): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `registersVal_succ_of_selected_bytecode` (line 115): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.

`Soundness/Layer3/History.lean`:

* `ramVal_zero` (line 21): takes the history predicates at an arbitrary `initialValue : Nat → F`, no new hypothesis.
* `ramVal_succ` (line 28): takes the history predicates at an arbitrary `initialValue : Nat → F`, no new hypothesis.
* `ramValFinal_eq_last_update` (line 39): takes the history predicates at an arbitrary `initialValue : Nat → F`, no new hypothesis.
* `ramVal_eq_final_of_suffix_zero` (line 56): takes the history predicates at an arbitrary `initialValue : Nat → F`, no new hypothesis.

`Soundness/Layer3/State.lean`:

* `ramVal_initial_state` (line 39): takes the history predicate at `ramInitialValue context.initialRam`, the same byte claim as before.
* `ramVal_initial_advance_pc` (line 56): takes the history predicate at `ramInitialValue context.initialRam`, the same byte claim as before.

`Soundness/Layer4/Inputs.lean`:

* `instructionInputs_of_selected_bytecode` (line 41): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `arithmeticAdviceFlags_zero_of_raf_zero` (line 62): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `lookupOperands_eq_inputs_of_raf_zero` (line 81): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.

`Soundness/Layer4/Interleaved.lean`:

* `uninterleave_of_lookup_operands` (line 28): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `instructionLookupRa_of_interleaved` (line 49): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `lookupOutput_of_interleaved` (line 64): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.

`Soundness/Layer4/Table.lean`:

* `lookupOutput_of_selected_bytecode` (line 28): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `instructionRafFlag_one_of_arithmetic` (line 48): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.

`Soundness/Layer5/RamAgreement.lean`:

* `OrdinaryRamAgreement.initial` (line 49): states the initial value through `ramInitialValue`.

`Soundness/Layer6/BytecodePC.lean`:

* `selected_entry` (line 26): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `selected_next_of_nonlast_virtual` (line 35): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `nonlastVirtual_of_remaining` (line 71): new.
* `selected_next_of_remaining` (line 100): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `next_of_remaining` (line 118): new.
* `selected_interior_current_remaining` (line 148): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `selected_interior_predecessor` (line 196): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `selected_registerShift_fed` (line 217): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `padding_persists` (line 263): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.
* `padding_from` (line 338): generalized to `FieldConstraintEquations` at an arbitrary `initialValue`, no new hypothesis.

`Soundness/Layer7/AdjacentRows.lean`:

* `window_bound` (line 19): new.
* `Windows` (line 27): new.
* `windows_append` (line 43): new.
* `windows_flatten` (line 75): new.
* `WithinSource` (line 93): new.
* `materialized_windows` (line 106): new.
* `expand_program_windows` (line 139): new.
* `expand_program_pairs` (line 171): statement unchanged, now the width-two case of `expand_program_windows`.

`Soundness/UntrustedAdvice/Bytes.lean`:

* `adviceWord` (line 28): new.
* `wordBytes` (line 35): new.
* `byteInitialRam` (line 44): new.
* `wordBytes_size` (line 52): new.
* `ramImageWord_wordBytes` (line 58): new.
* `byteInitialRam_good` (line 75): new.
* `publicIoMask_of_untrustedAdvice` (line 94): new.
* `byteInitialRam_masked` (line 121): new.
* `initialRamWordFromState_untrustedAdvice` (line 140): new.
* `onBytes_of_allConstraints` (line 214): new.

`Soundness/UntrustedAdvice/LoadWords.lean`:

* `NarrowLoad` (line 31): new.
* `LoadWindow` (line 40): new.
* `loadWindowsOk_windows` (line 49): new.
* `expand_program_loadWindows` (line 93): new.
* `narrowLoad_window` (line 108): new.
* `selfChecked_rdWriteValue_word` (line 163): new.
* `narrowLoad_rdWriteValue_word` (line 189): new.
* `load_rdWriteValue_word` (line 247): new.
* `load_ramReadValue_word` (line 270): new.

`Soundness/UntrustedAdvice/ShiftWitness.lean`:

* `Untouched` (line 29): new; unrelated to `WholeRun.Untouched`.
* `correction` (line 39): new.
* `accessCorrection` (line 46): new.
* `shiftWitness` (line 54): new.
* `opFlag_zero_or_one` (line 76): new.
* `prefix_correction` (line 88): new.
* `ramRa_mul_accessCorrection` (line 135): new.
* `load_mul_accessCorrection` (line 156): new.
* `shifted_history` (line 191): new.
* `shiftWitness_equations` (line 225): new.

`Soundness/soundness.lean`:

* `JoltInstance.soundness_onBytes` (line 34): renamed from `JoltInstance.soundness`, statement unchanged.
* `JoltInstance.soundness` (line 71): new statement: committed advice words and the added premise `adviceBlockFits`.

`WholeRun/Top.lean`:

* `JoltInstance.sail_soundness` (line 373): committed advice words and the added premise `adviceBlockFits`.

`advice_inputs.lean`:

* `JoltInstance.initial_state_with_untrusted_advice` (line 53): new.
* `AllConstraintsOnBytes.advice_tape_irrelevant` (line 104): renamed from `AllConstraints.advice_tape_irrelevant`, statement unchanged.
* `adviceBlockWords` (line 120): new.
* `overlay_untrusted_outside` (line 131): new.
* `initialRamWordFromState_outside_untrustedAdvice` (line 154): new.
* `Soundness.initial_state_memory_layout` (line 177): moved from `Soundness/Layer3/State.lean`, statement unchanged.
* `allConstraints_of_onBytes` (line 197): new.

`expansion_facts.lean`:

* `loadSelfChecked` (line 201): new.
* `leftOperandIsRegister` (line 210): new.
* `loadWindowsOk` (line 223): new.
* `sequenceOk` (line 239): adds the conjunct `loadWindowsOk`.
* `sequenceOk_loadWindowsOk` (line 297): new.
* `nativeRowOk` (line 902): adds the conjunct `loadWindowsOk`.
* `nativeRowOk_loadWindowsOk` (line 952): new.

`witness_helpers/ram_state.lean`:

* `ramImageWord_of_bytes` (line 38): new.

## Checks

* No new `bv_decide`, `native_decide`, `decide +kernel`, `sorry`, `maxHeartbeats` or `maxRecDepth`.
* Build at `5354ac5`: `lake build JoltConstraints.advice_inputs JoltConstraints.Soundness.UntrustedAdvice.Bytes JoltConstraints.Soundness.UntrustedAdvice.LoadWords JoltConstraints.Soundness.UntrustedAdvice.ShiftWitness JoltConstraints.witness_helpers.ram_state JoltConstraints.Soundness.soundness JoltConstraints.Completeness.completeness JoltConstraints.WholeRun.Top` completed successfully (9774 jobs) with no errors.
  The same command without the four `UntrustedAdvice` and `ram_state` targets also succeeded at `86e3c7a`.
  The Lean commits after `5354ac5` change only docstrings; `lake env lean` elaborated each changed file at `6a44511` without errors, and the PR's CI builds the whole project at the head.
  The remaining warnings in changed files are the existing `sorry` in completeness, deprecated names, and an unused-tactic lint in `ramImageWord_getLsbD`, all present at `b648846`.
* `#print axioms` at `86e3c7a`, and again at `5354ac5`: `JoltInstance.soundness`, `JoltInstance.soundness_onBytes`, `JoltInstance.sail_soundness`, `allConstraints_of_onBytes` and `onBytes_of_allConstraints` use only `propext`, `Classical.choice` and `Quot.sound`; completeness keeps the `sorryAx` it had at `b648846`.
* Proof times: `lean -Dprofiler=true -Dprofiler.threshold=10000` on `LoadWords`, `ShiftWitness`, `Bytes`, `advice_inputs`, `BytecodePC`, `AdjacentRows` and `expansion_facts` reports no declaration over ten seconds.
  `expansion_facts.lean` takes about 82 seconds in all, most of it in `simp` for the per-expansion checks.
