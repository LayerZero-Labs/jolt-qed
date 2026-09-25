# Share the ISA operand and branch calculations

## Why this change is needed

The instruction executor and consumers of execution state need the same operand values and branch decisions.
Duplicating those calculations makes it possible to describe an execution using a different calculation from the one that actually ran.
This is a refactoring requirement, with no claimed change to successful branch execution.

## Change

Extract `branchDecisionPure` and use it in the six branch instruction bodies.
Add `sourceValue` for reading an operand from an existing state without executing a monadic instruction.
The branch equivalence proofs are updated to unfold the shared helper.

`sourceValue` returns zero for a missing architectural register, while `readSrc` can fail on that register.
Consequently, using `sourceValue` to describe an executed read requires that the execution read succeeded.
Architectural `x0` always reads as zero.

## Evidence and port scope

The original change is [2a46c17](https://github.com/LayerZero-Labs/jolt-qed/commit/2a46c177519d1a7238e1d30e3fb85cdb553f94cf).
The implementation is in [RegisterAccess.lean](../JoltBytecode/JoltISA/RegisterAccess.lean), [semantic_helpers.lean](../JoltBytecode/JoltISA/semantic_helpers.lean), and [Semantics.lean](../JoltBytecode/JoltISA/Semantics.lean).
This port includes the six affected native branch proofs.
It introduces no witness or constraint modules.

## Acceptance criteria

- All six branch bodies use the shared decision helper.
- The native branch equivalence proofs build.
- The missing-register distinction between `sourceValue` and `readSrc` remains explicit.
