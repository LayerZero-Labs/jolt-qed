# Represent decoded Rust operands at their actual widths

## Problem

The old final `Instr` constructors used RISC-V source encoding widths, including 12-bit arithmetic and memory immediates, 13-bit branch offsets, and a 21-bit JAL offset.
Rust's final expanded instructions carry decoded operands, and expansion can produce values outside those source encoding ranges.
Using a narrow field loses information before execution begins.

For example, Rust's inline emitter accepts an ADDI immediate of `4096`.
With a source register containing ten, that final instruction must produce `4106`.
Storing `4096` in a 12-bit field produces zero, so the old representation would instead compute ten.

## Change

Use 64-bit decoded immediates for the affected arithmetic, jump, memory, and address-helper instructions.
Use 128-bit bit patterns for Rust's signed `i128` branch and assertion immediates.
Allow alignment assertions to read either architectural or virtual source registers.
Add `Encoded` constructors that decode narrow source operands once before constructing a final instruction.
For example, `Encoded.ADDI` sign-extends its 12-bit argument, while `Encoded.AUIPC` shifts and sign-extends its 20-bit argument.
Final AUIPC execution consumes the already shifted offset without shifting it again.

Retain separate representability predicates for Nat-valued helper immediates and the signed magnitudes accepted by compact trace conversion.
Those predicates describe input boundaries; defining them does not make every raw `Instr` value satisfy them.
Update generated expansions, handwritten expansions, value helpers, and all affected equivalence proofs to use the appropriate source or final constructor.

## Evidence

See Rust's [inline emitter](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/expand/inline.rs#L204-L245), [FormatI](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/tracer/src/instruction/format/format_i.rs#L9-L14), and [FormatB](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/tracer/src/instruction/format/format_b.rs#L9-L14).
The AUIPC decoding boundary is visible in [Rust's decoder](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/image/decode.rs#L471-L485).
The original mixed commit is [dfd9e93](https://github.com/LayerZero-Labs/jolt-qed/commit/dfd9e932b25d29ebb9ff306db11f301abcedcc2b), corresponding to model-review item #18.
This port extracts its JoltBytecode changes, with the independent LD destination repair recorded separately.

The implementation is in [Instruction.lean](../JoltBytecode/JoltISA/Instruction.lean), [Semantics.lean](../JoltBytecode/JoltISA/Semantics.lean), and [ExpansionsAutomated.lean](../JoltBytecode/JoltISA/ExpansionsAutomated.lean).

## Acceptance criteria

- A final ADDI with source ten and immediate `4096` produces `4106`.
- Encoded negative immediates are sign-extended once.
- A final AUIPC offset of `4096` remains `4096` during execution.
- Branch/assertion operands preserve the signed `i128` representation.
- Alignment helpers accept virtual sources.
- The migrated instruction and expansion proofs build without witness dependencies.
