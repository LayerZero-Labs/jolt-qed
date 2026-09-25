# Preserve Rust instruction operands even when execution ignores them

## Problem

Several Lean virtual-instruction constructors omitted immediate fields present in Rust's instruction formats.
`VirtualAdviceLen` also omitted its source operand, and `VirtualHostIO` had no operands at all.
Although an instruction body may ignore a field, the decoded instruction and its trace capture still contain it.
Dropping the field prevents the Lean instruction from representing that Rust row faithfully.

For example, Rust's `VirtualAdviceLen` uses `FormatI`, containing a destination, source, and immediate, although the result is calculated from the tape.
Two rows with different immediates must remain distinguishable even if they compute the same result.

## Change

Retain the missing operands in [Instruction.lean](../JoltBytecode/JoltISA/Instruction.lean).
Supply zero defaults for omitted immediates in existing expansions, while allowing an imported row to supply its actual immediate.
Update instruction pattern matches, generated expansions, and their proofs to accept the additional fields.

## Evidence and scope

See Rust's [FormatI and its capture operations](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/tracer/src/instruction/format/format_i.rs), [VirtualAdviceLen](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/tracer/src/instruction/virtual_advice_len.rs), and [VirtualHostIO](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/tracer/src/instruction/virtual_host_io.rs).
The original Lean change is [907d734](https://github.com/LayerZero-Labs/jolt-qed/commit/907d7346352ec800578e4ed6fd52cabca64155d5).
Preserving HostIO operands does not implement its live execution effects.
The separate [decoded operand issue](isa-decoded-operands.md) covers the later width corrections.

## Acceptance criteria

- The affected constructors retain the actual Rust operands.
- Existing expansions explicitly or by default supply their zero immediates.
- Execution continues to ignore only the fields ignored by the corresponding Rust body.
- Updated proofs build.
