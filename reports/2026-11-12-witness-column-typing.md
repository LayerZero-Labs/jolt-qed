# Witness columns and verifier inputs: Lean types against what Jolt's verifier knows

Date: 2026-11-12.
Jolt commit: a16z/jolt `a6b6dc717` (contains a16z/jolt#2190, `4e55c9a5f`).
Lean commit: `86e3c7a` on branch `t5/advice-field`, based on `inline/t1-driver` at `b648846`.
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

## Planned inline advice (conflict to resolve)

`docs/inline-precompiles.md` (phase I1b) plans a lemma `allConstraints_inline_advice` that states `AllConstraints joltInstance { privateInputs with inline_advice := words } witness`.
After this branch `AllConstraints` takes untrusted-advice words instead of private inputs, so that plan needs the byte relation `AllConstraintsOnBytes`, or inline advice words alongside `untrustedAdvice`.

## Scope of the load argument

The reduction uses that every row with the Load flag reads a 64-bit word.
`expansion_facts.lean` checks the load window for the expansion of every `SourceInstruction`, which excludes inline opcodes (`JoltConstraints/expansion_helpers.lean:16`).
Jolt's inline builder can emit narrow loads (`InlineExpansionBuilder::emit_ld`, `crates/jolt-program/src/expand/inline.rs:223`), and nothing in Jolt makes an inline recipe range-check the loaded value.
For example, a recipe that loads a byte and then overwrites the destination register supplies no lookup that bounds the loaded word.
So when the inline phases (I1a, I1b of `docs/inline-precompiles.md`) add inline rows, they must extend the load-window check to those rows, or prove a range check for each recipe in another way, before this reduction applies to them.

## Statement changes

Changed statements of existing theorems and definitions:

* `AllConstraints` (`Constraints/All.lean`) takes `untrustedAdvice : Nat → F` instead of `privateInputs`; the old relation is `AllConstraintsOnBytes`.
* `ConstraintEquations` is an abbreviation for the new `FieldConstraintEquations` at `ramInitialValue initialRam`.
* `JoltInstance.soundness` and `JoltInstance.sail_soundness` take `adviceBlockFits : joltInstance.UntrustedAdviceBlockFits` and `untrustedAdvice : Nat → F`, and assume `AllConstraints joltInstance untrustedAdvice witness`.
* `JoltInstance.completeness` concludes `AllConstraints` at the words `adviceBlockWords` of the run's initial RAM, and `completeness_someWitness` quantifies over advice words instead of private inputs.
* The raw RAM-history predicates `ramValEqInitialPlusPrefixRamInc` and `ramValFinalEqInitialPlusRamInc` (`Constraints/`) take a field-valued initial value; their byte users pass `ramInitialValue`.
* The soundness lemmas of layers 1 to 4, `Layer3/History.lean`, `Layer3/State.lean` (`ramVal_initial_state`, `ramVal_initial_advance_pc`), `OrdinaryRamAgreement.initial` and `Layer6/BytecodePC.lean` take `FieldConstraintEquations` at an arbitrary `initialValue : Nat → F`, or at `ramInitialValue` where they use the bytes; none gains a hypothesis.
* `sequenceOk` and `nativeRowOk` (`expansion_facts.lean`) include the load-window check `loadWindowsOk`.
* `materialized_pairs` (`Layer7/AdjacentRows.lean`) is replaced by `materialized_windows`; `expand_program_pairs` keeps its statement.
* `Soundness.initial_state_memory_layout` moves from `Soundness/Layer3/State.lean` to `advice_inputs.lean` with the same name and statement.

Renamed, with unchanged statements: `JoltInstance.soundness_onBytes` (was `JoltInstance.soundness`), `AllConstraintsOnBytes.advice_tape_irrelevant` and `HonestTrace.allConstraintsOnBytes_prover_sizes`.

Added hypotheses: only `adviceBlockFits` on `JoltInstance.soundness` and `JoltInstance.sail_soundness`.

New declarations:

* `Constraints/All.lean`: `FieldConstraintEquations`, `JoltPrivateInputs.noUntrustedAdvice`, `untrustedAdviceWordIndex?`, `committedInitialValue`, `AllConstraintsOnBytes`.
* `Soundness/Assumptions.lean`: `JoltInstance.UntrustedAdviceBlockFits`.
* `Soundness/UntrustedAdvice/LoadWords.lean`: the load-window argument, ending in `load_ramReadValue_word`.
* `Soundness/UntrustedAdvice/ShiftWitness.lean`: `shiftWitness` and `shiftWitness_equations`.
* `Soundness/UntrustedAdvice/Bytes.lean`: `adviceWord`, `wordBytes`, `byteInitialRam` and `onBytes_of_allConstraints`.
* `advice_inputs.lean`: `initial_state_with_untrusted_advice`, `adviceBlockWords` and `allConstraints_of_onBytes`.
* `expansion_facts.lean`: `loadSelfChecked`, `leftOperandIsRegister`, `loadWindowsOk` and its proofs for every expansion.
* `Layer7/AdjacentRows.lean`: `Windows` and `expand_program_windows`; `Layer6/BytecodePC.lean`: `next_of_remaining`; `witness_helpers/ram_state.lean`: `ramImageWord_of_bytes`.

## Checks

* No new `bv_decide`, `native_decide`, `decide +kernel`, `sorry`, `maxHeartbeats` or `maxRecDepth`.
* `#print axioms` at `86e3c7a`: `JoltInstance.soundness`, `JoltInstance.soundness_onBytes`, `JoltInstance.sail_soundness`, `allConstraints_of_onBytes` and `onBytes_of_allConstraints` use only `propext`, `Classical.choice` and `Quot.sound`; completeness keeps the `sorryAx` it had at `b648846`.
* Proof times: `lean -Dprofiler=true -Dprofiler.threshold=10000` on `LoadWords`, `ShiftWitness`, `Bytes`, `advice_inputs`, `BytecodePC`, `AdjacentRows` and `expansion_facts` reports no declaration over ten seconds.
  `expansion_facts.lean` takes about 82 seconds in all, most of it in `simp` for the per-expansion checks.
