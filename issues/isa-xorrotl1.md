# Add the missing VirtualXORROTL1 instruction

## Problem

Rust supports `VirtualXORROTL1`, but the Lean ISA on `main` has no constructor or execution rule for it.
The existing XOR-rotate instructions cannot substitute for it because the placement of the rotation differs.

Rust computes `rs1 XOR rotate_left(rs2, 1)`.
With operands one and two, the result is `1 XOR 4 = 5`.
Rotating the XOR of those operands would instead produce six.
With operands zero and `2^63`, the result is one because the top bit wraps to bit zero.

## Change

Add the constructor in [Instruction.lean](../JoltBytecode/JoltISA/Instruction.lean), the value helper in [Values.lean](../JoltBytecode/JoltISA/Values.lean), and the execution rule in [Semantics.lean](../JoltBytecode/JoltISA/Semantics.lean).
Read both operands before writing the destination, preserving behavior when the destination aliases a source.
Extend the generic proof-support case splits and protected-register-write predicate.

## Evidence and scope

See [Rust's execution rule](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/tracer/src/instruction/virtual_xor_rotl1.rs#L17-L23).
The original Lean change is [f42ae4f](https://github.com/LayerZero-Labs/jolt-qed/commit/f42ae4f16f203681246619bb6b23302f2ed543b5).
This is model-review item #19.
Witness selectors and lookup tables from the witness branch are outside this ISA port.

## Acceptance criteria

- The ISA represents and executes `VirtualXORROTL1` with the stated operand order.
- The examples above produce five and one respectively.
- The ISA and existing equivalence proofs build with the new constructor.
