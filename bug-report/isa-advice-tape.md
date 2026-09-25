# Read advice instructions from the runtime tape

## Problem

The old `VirtualAdviceLoad dst value` wrote a supplied value directly, and `VirtualAdviceLen dst remaining` wrote a supplied length.
Rust obtains both results from a mutable advice tape.
The same instruction can therefore produce different results on successive executions.

For a tape containing bytes `[0x12, 0x34, 0x56]` at cursor zero, a two-byte advice load returns `0x3412` and advances the cursor to two.
A subsequent advice-length instruction returns one.
These effects cannot be represented by a fixed result stored in the instruction.

## Change

Add tape bytes and a read cursor to [Core.lean](../JoltBytecode/JoltISA/Core.lean).
Implement little-endian tape reads in [AdviceTape.lean](../JoltBytecode/JoltISA/AdviceTape.lean).
Make `VirtualAdviceLoad` take a byte count and consume the tape, and make `VirtualAdviceLen` compute the remaining length.
Update the source advice-load expansions so they supply the width rather than a preselected result.
Port the affected expansion proofs and state-preservation lemmas.

## Evidence and scope

See Rust's [AdviceTape](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/tracer/src/emulator/cpu.rs#L25-L82), [VirtualAdviceLoad](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/tracer/src/instruction/virtual_advice_load.rs), and [VirtualAdviceLen](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/tracer/src/instruction/virtual_advice_len.rs).
The original Lean change is [907d734](https://github.com/LayerZero-Labs/jolt-qed/commit/907d7346352ec800578e4ed6fd52cabca64155d5).
Lean accepts widths one, two, four, and eight; Rust checks this set with `debug_assert!`, so arbitrary invalid widths in release builds are outside the correspondence established here.
Lean reports exhausted reads as an assertion error, while Rust's instruction uses `expect`.
Live `VirtualHostIO` tape production remains unimplemented, as recorded in model-review item #5.

## Acceptance criteria

- Successful reads consume the requested bytes in little-endian order.
- Length queries use the current cursor.
- Exhausted reads fail without advancing the cursor.
- The affected ISA proofs build.
