+++
title = "Tracer And Constraints Disagree On Panic Definition"
date = 2026-09-29
draft = false

[extra]
hidden = true
+++

Everything in this post is with respect to commit [`8bbb2357`](https://github.com/a16z/jolt/tree/8bbb2357890928d8f83b00ca542879077c4d3d28).


**Reported:** filed as [#2065](https://github.com/a16z/jolt/issues/2065) on 2026-10-15 and marked closed the same day, to prevent it from being publicly open.
The bug has not been fixed.

## Background

Jolt's memory layout reserves an 8-byte word in its I/O region, the panic word.
A guest program signals that it has panicked by storing to it.
RISC-V has no such word; only Jolt gives this address a meaning.

> The core issue is that Jolt's tracer and the constraints disagree.

**Jolt's tracer.**
Any store to the panic address sets the panic flag, whatever value is stored ([`common/src/jolt_device.rs:175-178`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/common/src/jolt_device.rs#L175-L178)):

```rust
pub fn store(&mut self, address: u64, value: u8) {
    if address == self.memory_layout.panic {
        self.panic = true;
        return;
```

**The constraints.**
The RAM table keeps the value actually stored.
At the end, the verifier requires the panic word to equal the claimed panic flag: 1 for "panicked", 0 for "no panic".
For a "no panic" claim it also requires the termination word to be 1 ([`crates/jolt-program/src/preprocess/public_io.rs:42-52`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-program/src/preprocess/public_io.rs#L42-L52)):

```rust
segments.push(PublicMemorySegment {
    start_index: layout.remapped_word_address(layout.panic)? as u128,
    words: vec![public_io.panic as u64],
});

if !public_io.panic {
    segments.push(PublicMemorySegment {
        start_index: layout.remapped_word_address(layout.termination)? as u128,
        words: vec![1],
    });
}
```

## Example

Consider this program:

```text
sb  x0, 0(panic)          ; store 0 to the panic word
                          ;   Jolt's tracer: panic flag set
                          ;   RAM table: panic word holds 0
write output 5
sb  1, 0(termination)     ; store 1 to the termination word
j   .                     ; stall
```

Jolt's tracer ends this run with output 5 and `panic = true`, so the true claim is "output 5, panicked".

- **Completeness.**
  Jolt's prover claims "output 5, panicked", and the verifier rejects it at the Stage 4 RAM value check ([`RamValCheck`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-verifier/src/stages/stage4/ram_val_check.rs)).
  At every RAM word, that check requires the final value to equal the initial value plus the changes made by the recorded stores.
  - The constraints do not treat the panic word specially.
    Jolt's tracer records every store, including stores to the I/O region, as an ordinary RAM write before the device sees it ([`tracer/src/emulator/mmu.rs:429-435`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/emulator/mmu.rs#L429-L435), [`548-561`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/emulator/mmu.rs#L548-L561)).
    So the RAM history gives the panic word the stored value, 0.
  - Jolt's prover builds the final RAM from the tracer's flag instead, and sets the final panic word to 1 ([`crates/jolt-witness/src/backend/trace/ram.rs:180-187`](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/backend/trace/ram.rs#L180-L187)).
  - A final value of 1 is not the initial 0 plus a store of 0, so the check fails.
    The final panic word does match the claim, so the public I/O check alone would pass.
    The true claim has no proof.

- **Soundness.**
  A prover can follow the program's rows exactly, and build its final RAM from the recorded stores, so the panic word stays 0.
  The RAM value check passes.
  It claims "output 5, no panic": the panic word is 0, the termination word is 1 and the output is 5, so the public I/O check passes too, and the verifier accepts.
  Jolt's tracer never ends this run without a panic, so a false claim is accepted.
