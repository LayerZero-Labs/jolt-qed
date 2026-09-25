# Model Jolt device memory in LD and SD execution

## Problem

The old Lean LD and SD bodies sent every access through Sail's memory operations.
Rust routes addresses below `0x80000000` through its device, where input, advice, output, panic, and termination have their own behavior.
The old `SailJoltState` could not record changes to these device buffers or the panic flag.

For example, writing the first panic byte sets the panic flag even when the stored byte is zero.
A subsequent device read returns the flag, so treating that location as ordinary stored RAM gives the wrong result.
Rust's termination region ignores writes and reads as zero.

## Change

Add `JoltIOLayout` and `JoltIOState` to [Core.lean](../JoltBytecode/JoltISA/Core.lean).
Implement device byte reads, byte writes, and little-endian word operations in [DeviceMemory.lean](../JoltBytecode/JoltISA/DeviceMemory.lean).
Route LD and SD through these operations, retaining Sail's access checks on the ordinary RAM path.
Update the memory proofs and state-preservation lemmas for the extended state.

The ordinary-RAM proof assumptions now require the address to be at least `0x80000000`, as well as excluding Sail MMIO.
Excluding Sail MMIO alone does not exclude Jolt's device region.

## Evidence and scope

See Rust's [device load and store operations](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/common/src/jolt_device.rs#L121-L182) and [MMU](https://github.com/abiswas3/jolt/blob/7dfe8a0f829a4ab3e9126eb5ac5b5b15208cf5fc/tracer/src/emulator/mmu.rs).
The original Lean change is [907d734](https://github.com/LayerZero-Labs/jolt-qed/commit/907d7346352ec800578e4ed6fd52cabca64155d5).
The model-review notes identify layout validation and buffer bounds as unfinished work.
This port adds device execution but does not establish validity of every constructible layout, Rust heap/stack bounds, or device equivalence with Sail.

## Acceptance criteria

- LD and SD distinguish device memory from ordinary RAM.
- Device output and panic effects are represented in the execution state.
- Ordinary-RAM equivalence proofs build with the explicit device exclusion.
