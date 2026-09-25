# ISA migration from the witness branch

Branch: `fix/isa-rust-correspondence`.
Base: local `main` at `0efd66819feebf4704a330a2aad02fe0f1b52d70`.
Source: `feat/npWitness` at `132435a`, plus the reviewed, previously untracked JAL issue report.
The issue documents below are local GitHub issue drafts and have not been published.

## Ports and issue drafts

| Port commit | Original commit(s) | Change | Issue draft(s) |
| --- | --- | --- | --- |
| `cb8a6c7` | `2a46c17` | Shared operand and branch calculations | [Shared helpers](isa-shared-helpers.md) |
| `7b4bc98` | `907d734` | Device memory, runtime advice, preserved operands, and shared arithmetic | [Device memory](isa-device-memory.md), [advice tape](isa-advice-tape.md), [preserved operands](isa-preserve-operands.md), [shared helpers](isa-shared-helpers.md) |
| `fba913a` | `f42ae4f` | Missing VirtualXORROTL1 instruction | [VirtualXORROTL1](isa-xorrotl1.md) |
| `c43d3ce` | JoltBytecode portion of `dfd9e93` | Decoded operand widths and source constructors | [Decoded operands](isa-decoded-operands.md) |
| `47a1f49` | LD portion of `dfd9e93` | Execute the destination supplied by the final LD row | [LD destination](isa-ld-destination.md) |
| `c1adbf5` | JoltBytecode portions of `feae045`, `3bf46b5`, and `78bbca7` | JAL semantics, assumptions bundle, and projection proof | [PC and nextPC](pc_nextPc.md) |

Proof adaptations accompany the corresponding ISA port and do not have separate issues.
The three JAL commits are combined because the new semantics, bundle, theorem, and helper lemmas must be available together.
The mixed final-operand commit is restricted to JoltBytecode, and its independent LD destination change is split into a separate port.

## Scope verification

All 114 changed JoltBytecode files match the source branch exactly after the ports.
No `JoltConstraints` source files, witness definitions, constraint proofs, or witness build targets are included.
The trusted Sail sources, toolchain, dependency manifest, and Lake configuration remain those of `main`.
The witness branch and its working files are preserved in the original checkout.

## Validation

`lake build` passed on 25 September 2026 with 8,449 jobs in the ISA worktree.
The build includes the public `JoltBytecode` root, instruction dispatcher, and migrated instruction and expansion proofs.
Existing `sorry` and linter warnings remain; a successful build does not assert that all project theorems are proved.

## Limits retained from the source branch

The issue drafts distinguish the implemented changes from unfinished model work.
Live HostIO effects, complete device-layout validation, and the deferred shift-mask behavior are not repaired by this migration.
The JAL theorem requires the readable-register and target-alignment bundle described in its issue.
Review also identified the existing LD offset-cast discrepancy for arbitrary final operands, documented in the decoded-operand issue.
No additional ISA behavior was changed to address these follow-ups during the port.
