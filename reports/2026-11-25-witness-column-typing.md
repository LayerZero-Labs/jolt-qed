# Witness columns and verifier inputs: Lean types against what Jolt's verifier knows

Date: 2026-11-25.
Jolt commit: a16z/jolt `ff6fc656813d950565c9f6e1258b78bdaf0e60e8` (the re-pin).
Lean branch: `t5/advice-field-ff6fc`, stacked on `drift-guards` (`20b949b`).
This note ports `reports/2026-11-12-witness-column-typing.md` from the branch `t5/advice-field` (Jolt `a6b6dc717`) and re-checks every row at the pin.
Scope: every column of `WitnessType` (`JoltConstraints/translation/witness.lean`) and every other input of the relation `AllConstraints` (`JoltConstraints/translation/Constraints/All.lean`).
For each one, the note compares the value Jolt's verifier has with the Lean type and lists the mismatches.
Jolt paths below are relative to the Jolt repository at the pin.

## Summary

Every witness column is a field element in Lean, and Jolt's verifier knows nothing more about any of them than that it is a field element, so the witness columns have no typing gap.
The gaps are in the other inputs of the relation, which Lean modelled as bytes while Jolt's verifier holds only a commitment:

| Input | Jolt's verifier has | Lean type | Status |
| --- | --- | --- | --- |
| Untrusted advice | A commitment to field elements, one per word of the untrusted-advice block | `untrustedAdvice : Nat → F`, an argument of `AllConstraints` | Fixed on this branch |
| Size of the untrusted-advice block | `max_untrusted_advice_size / 8` words of the checked layout | The same layout size; the tracer accepts that many bytes | No gap at the pin; derived, no premise |
| Trusted advice | A commitment, made by a trusted party | Bytes in `JoltInstance.trusted_advice` | Unchanged; recorded as the assumption `TrustedAdviceAsBytes` |
| Program image and bytecode in committed-program mode | Commitments `ProgramImageInit` and `ProgramBytecode` | Public `JoltInstance.program` | Out of scope of the current model |
| Execution tape (`advice_tape`) | Nothing: it is not an input of the verifier | Bytes in `JoltPrivateInputs.advice_tape` | No gap: the relation ignores it (`AllConstraintsOnBytes.advice_tape_irrelevant`) |

## Witness columns

Jolt commits to these polynomials (`JoltCommittedPolynomial`, `crates/jolt-claims/src/protocols/jolt/ids.rs:348-365`): `RdInc`, `RamInc`, `InstructionRa(i)`, `BytecodeRa(i)`, `RamRa(i)`, `TrustedAdvice`, `UntrustedAdvice`, `ProgramImageInit` and `ProgramBytecode`.
The enum also has retired codec slots (`Reserved4`, `Reserved9`, `Reserved10`), which are uninhabited.
Every other polynomial is virtual: the verifier learns only evaluation claims about it, which sumchecks reduce to openings of committed polynomials and to public data.
In both cases the verifier knows a field element and nothing about its range.

Every column of `WitnessType F params` has values in `F` (`witness.lean:238`):

* The committed columns `RdInc`, `RamInc`, `InstructionRaChunk`, `BytecodeRaChunk` and `RamRaChunk` are committed field elements in Jolt and `F` in Lean.
* The virtual columns (`PC`, `UnexpandedPC`, `Imm`, the register and RAM values, the instruction inputs, lookup operands and outputs, `Product`, the branch and jump flags, the next-row columns, `OpFlags`, `InstructionFlags`, `LookupTableFlag`, `InstructionRafFlag`, `RamHammingWeight`, `Rs1Ra`, `Rs2Ra`, `RdWa`, `RegistersVal`, `RamRa`, `RamVal`, `RamValFinal` and `InstructionRa`) are field elements in both.

The soundness proof derives every range fact it uses from the constraints, not from the types.
For example, `load_ramReadValue_word` (`theorems/Soundness/UntrustedAdvice/LoadWords.lean`) shows that every row with the Load flag reads a 64-bit word, from the lookups of the load row or of the rows after it.
The witness columns need no change.

## Untrusted advice (fixed)

Jolt's verifier receives only a commitment to the untrusted advice (`proof.untrusted_advice_commitment`, `crates/jolt-verifier/src/verifier.rs:480`).
When the commitment is present, the RAM value check adds the committed block to the initial RAM (`ram_val_check_init_structure` and `ram_val_check_advice_block`, `crates/jolt-verifier/src/stages/stage4/ram_val_check.rs:340` and `:482`).
The block starts at the remapped word of `untrusted_advice_start` and holds `max_untrusted_advice_size / 8` words, and each word is an arbitrary field element.

Before this branch, the relation took the advice as bytes, so each initial word of the block was the cast of a 64-bit word.
That relation admitted fewer witnesses than Jolt's verifier accepts, and soundness for it did not cover a prover that commits to a word outside the 64-bit range.

On this branch, `AllConstraints joltInstance untrustedAdvice witness` takes the advice words as `untrustedAdvice : Nat → F`.
The initial value of a RAM word is `committedInitialValue`: the committed word inside the block and the cast of the fixed 64-bit word elsewhere.
When Jolt's prover sends no commitment, the verifier adds nothing, which equals the all-zero block; the relation quantifies over every advice word sequence, so it covers that case too.
`JoltInstance.soundness` proves soundness for this relation with no new premise, by reducing it to the byte relation (`allConstraintsOnBytes_of_allConstraints`).
The byte relation is still available as `AllConstraintsOnBytes`, with its soundness theorem `JoltInstance.soundness_onBytes`; neither is a headline statement.

The reduction rests on three facts, all proved from the constraints:

* `RamWriteProtected` makes every store to a protected word keep its value (`ramInc_zero_of_selected_protected`), and every word of the untrusted-advice block is protected (`writeProtectedMask_of_untrustedAdvice`). Jolt: the protected-increment claim in `crates/jolt-claims/src/protocols/jolt/relations/ram/read_write_checking.rs`.
* At the first row that selects a protected word, a load reads a range-checked word, and a store writes a register value, which is a 64-bit word (`initialValue_word_of_selected`). A committed word outside the 64-bit range is therefore never selected.
* The public I/O mask is zero on the block (`publicIoMask_of_untrustedAdvice`), so the final-RAM output check does not see the block.

So each committed word outside the 64-bit range can be replaced by zero, together with the same shift of `RamVal` and `RamValFinal` at that word (`shiftRam_equations`).
The other columns do not change.

## Size of the untrusted-advice block (no gap at the pin)

At `a6b6dc717` the tracer checked the advice length against the configured size, while the verifier's block spanned the size rounded up to a multiple of 8, so the old branch needed the premise `UntrustedAdviceBlockFits`.
At the pin this gap is closed in Jolt:

* `MemoryLayout::new` rounds each advice size up to a multiple of 8 and requires it to be zero or a power of two (`common/src/jolt_device.rs:503-511` and `validate_advice_sizes`, `:744-752`).
* `JoltDevice::try_with_io` checks the advice length against the rounded `memory_layout.max_untrusted_advice_size` (`common/src/jolt_device.rs:214-232`), so a run can hold exactly as many bytes as the verifier's block has.
* Because the rounded size is a power of two, `(max_size / 8).next_power_of_two()` in `ram_val_check_advice_block` equals `max_size / 8`.

The Lean model has these checks (`MemoryLayout.new`, `initialMem`), and `untrustedBlock_geometry` (`theorems/untrusted_advice_block.lean`) derives the block facts from them.
`JoltInstance.soundness` has no block-size premise.

One part of the verifier geometry is not modelled: `block_selector_mle_msb` (`crates/jolt-poly/src/mle.rs:95`) rejects a block whose start is not aligned to its size or whose end leaves the RAM domain.
The model reads `committedInitialValue` from the layout directly and does not reproduce the selector polynomial.
The layout checks make the start a multiple of 8 and keep the block inside the I/O region, so the selector rejection only shrinks the set of accepted proofs, and the soundness theorem covers the larger set.

## Trusted advice (not changed)

The instance holds the trusted advice as bytes (`JoltInstance.trusted_advice`), while Jolt's verifier holds only a commitment (the NOTE above `JoltInstance` in `JoltConstraints/translation/program.lean`).
The verifier adds the trusted block to the initial RAM in the same way as the untrusted block, when `trusted_advice_commitment_present` holds (`ram_val_check.rs:351-361`).
The model is right only when the trusted party commits to the packed words of some byte string that fits the configured size.
This branch records that as the assumption `TrustedAdviceAsBytes` in `assumptions.toml`, anchored at `ram_val_check_advice_block` and `ram_val_check_init_structure`.
If the trusted party may commit to arbitrary field elements, the reduction above would apply with the trusted block in place of the untrusted one.

## Committed-program mode (out of scope)

When the program is committed, Jolt's verifier holds commitments `ProgramImageInit` and `ProgramBytecode` instead of the program (`ids.rs:360` and `:364`; `program_image_point` in `ram_val_check_init_structure`).
The Lean instance always holds the program image (`JoltInstance.program`), so the model covers only the mode where the verifier preprocesses the program itself.
`model_review.md` lists program commitments under "Not modeled".

## Scope of the load argument

The reduction uses that every row with the Load flag reads a 64-bit word.
`expansion_facts.lean` checks the load window (`loadWindowsOk`) for the expansion of every `SourceInstruction`, which excludes inline opcodes (`JoltConstraints/translation/expansion_helpers.lean:16`).
Jolt's inline builder can emit narrow loads (`InlineExpansionBuilder::emit_ld`, `crates/jolt-program/src/expand/inline.rs:223`), and nothing in Jolt makes an inline recipe range-check the loaded value.
For example, a recipe that loads a byte and then overwrites the destination register supplies no lookup that bounds the loaded word.
When the inline tracks add inline rows, they must extend the load-window check to those rows, or prove a range check for each recipe in another way, before this reduction applies to them.
An inline-advice lemma should be stated on `AllConstraintsOnBytes`, which still takes the private inputs, and reach `AllConstraints` through `allConstraints_of_onBytes`.

## Statement changes

* `AllConstraints` takes `untrustedAdvice : Nat → F` instead of `privateInputs`. The old relation is `AllConstraintsOnBytes`.
* `JoltInstance.soundness` and `JoltInstance.sail_soundness` take `untrustedAdvice` in place of `privateInputs`. Neither gains a hypothesis.
* `JoltInstance.completeness` concludes `AllConstraints` at `adviceBlockWords` of the run's initial RAM, and `JoltInstance.completeness_someWitness` quantifies over advice words.
* The soundness lemmas of layers 1 to 7 take `FieldConstraintEquations` at an arbitrary `initialValue : Nat → F`. None gains a hypothesis.
* `InLanguage`, the execution semantics and `TemporaryRestrictions` do not change.
