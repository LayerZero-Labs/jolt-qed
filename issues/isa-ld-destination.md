# Execute LD using the destination in the final instruction

## Problem

The old Lean LD body called `writeDst (sideEffectingDst dst) dword`.
For destination `x0`, this silently redirected the write to a temporary virtual register during execution.
Rust's raw LD body writes the destination supplied in its operands.
Any source-instruction destination rewrite must already be reflected in those operands before the final instruction executes.

For a raw final `LD x0` loading nine, the architectural write is discarded and the temporary virtual register must remain unchanged.
The old Lean body could instead write nine into that temporary register.
If source expansion produces an LD targeting a temporary register, that emitted LD must write the temporary register explicitly.

## Change

Use `writeDst dst dword` in [Semantics.lean](../JoltBytecode/JoltISA/Semantics.lean).
Retain the source expansion's destination handling at the expansion boundary.
Simplify the [native LD proof](../JoltBytecode/InstructionEquivalence/Instructions/Natives/Ld.lean) to use the actual destination, including Sail's discard behavior for `x0`.

## Evidence and scope

See [Rust's LD execution](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/tracer/src/instruction/ld.rs) and the [source expansion rewrite](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/crates/jolt-program/src/expand/mod.rs#L134-L149).
The original change is part of [dfd9e93](https://github.com/LayerZero-Labs/jolt-qed/commit/dfd9e932b25d29ebb9ff306db11f301abcedcc2b), corresponding to model-review item #8.
Rust's [compact trace conversion](https://github.com/abiswas3/jolt/blob/e012da54c3bb26a6436b5ca74e86c19bb39695ad/tracer/src/trace_row.rs#L53-L118) separately requires a load's captured RAM value to equal its captured destination value.
Thus a raw LD into `x0` can execute while a nonzero loaded value causes proof-trace conversion to reject it.
This issue fixes execution semantics; the witness branch's load-capture condition is outside this port.

## Acceptance criteria

- Final LD execution writes exactly its supplied destination.
- Loading into `x0` does not write a hidden temporary register.
- Source expansion can still emit an explicit temporary destination.
- The native and expanded load proofs build.
