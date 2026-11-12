# Witness columns and verifier inputs: Lean types against what Jolt's verifier knows

Date: 2026-11-12.
Jolt commit: a16z/jolt `a6b6dc717` (contains a16z/jolt#2190, `4e55c9a5f`).
Lean commit: branch `t5/advice-field`, based on `inline/t1-driver` at `b648846`.
Scope: every column of `WitnessType` (`JoltConstraints/witness.lean`) and every other input of the relation `AllConstraints` (`JoltConstraints/Constraints/All.lean`).
For each one, this note compares the value Jolt's verifier has with the Lean type, and lists the mismatches.
Only the untrusted-advice mismatch is fixed on this branch; the other fixes below are proposals.

## Summary

Every witness column is a field element in Lean, and Jolt's verifier knows nothing more about any of them than that it is a field element, so the witness columns have no typing gap.
The gaps are in the other inputs of the relation, which Lean modelled as bytes or 64-bit words while Jolt's verifier holds only a commitment:

| Input | Jolt's verifier has | Lean type before | Status |
| --- | --- | --- | --- |
| Untrusted advice | A commitment to field elements, one per word of the untrusted-advice block | Bytes in `JoltPrivateInputs.untrusted_advice` | Fixed on this branch: `AllConstraints` takes `untrustedAdvice : Nat → F` |
| Size of the untrusted-advice block | `layout.max_untrusted_advice_size / 8` words, with the size rounded up to a multiple of 8 | Tracer accepts only `config.max_untrusted_advice_size` bytes | New temporary restriction `untrustedAdviceBlockFits`; Jolt fix proposed below |
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
`JoltInstance.soundness` proves the stronger statement by reducing it to the byte relation (`onBytes_of_allConstraints`).
A word outside the 64-bit range cannot be loaded before it is overwritten, because every load reads a 64-bit word, so it can be replaced by zero together with a shift of the RAM value columns.

## Size of the untrusted-advice block (new restriction)

The tracer accepts at most `config.max_untrusted_advice_size` bytes of untrusted advice (`tracer/src/lib.rs:374`).
`MemoryLayout::new` rounds that size up to a multiple of 8 (`common/src/jolt_device.rs:397-410`), and the verifier's block spans the rounded size.
If the configured size is not a multiple of 8, the prover can commit to block bytes that no tracer run can hold.
For example, with a configured size of 12 the block has 2 words, and the prover may set the top 4 bytes of the second word.
This gap exists even when every committed word is a 64-bit word.

The branch adds the temporary restriction `untrustedAdviceBlockFits` to `JoltInstance.TemporaryRestrictions`: the rounded size is at most the configured size, which holds exactly when the configured size is a multiple of 8.
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
