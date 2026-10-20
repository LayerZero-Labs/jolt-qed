+++
title = "Tracer And Constraints Disagree On The Termination Word"
date = 2026-10-20
draft = false

[extra]
hidden = false
+++

Everything in this post is with respect to commit [`8bbb2357`](https://github.com/a16z/jolt/tree/8bbb2357890928d8f83b00ca542879077c4d3d28).


## Background

A guest built with Jolt's SDK ends by storing 1 to the termination word and then stalling with `j .`:

```rust
unsafe {
    ::core::ptr::write_volatile(#termination_bit as *mut u8, 1);
}
// Never return - loop forever for clean termination
// The emulator detects termination via PC stall (prev_pc == pc)
loop {
    unsafe { ::core::arch::asm!("j .", options(noreturn)); }
}
```
[Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/jolt-sdk/macros/src/lib.rs#L880-L887)

Jolt's tracer ignores every store to the termination word, and loads it as 0:

```rust
pub fn load(&self, address: u64) -> u8 {
    if self.is_panic(address) {
        self.panic as u8
    } else if self.is_termination(address) {
        0
    } // ...
}

pub fn store(&mut self, address: u64, value: u8) {
    if address == self.memory_layout.panic {
        self.panic = true;
        return;
    } else if self.is_panic(address) || self.is_termination(address) {
        return;
    }
    // ...
}
```
[Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/common/src/jolt_device.rs#L146-L181)

### Constraints

The constraints treat the termination word as ordinary memory: a store sets it to the stored value, and a load reads that value back.
At the end, a "no panic" claim requires the final termination word to be 1:

```text
RamValFinal(termination) = 1
```

The PC constraints let the last cycle before the padding be any JAL or JALR; see [A Proof Can Stop At Any Jump](@/blog/proof-stops-at-any-jump/index.md).

### Example

Consider this program, shown with made-up addresses, where `s1` holds the first address of the output region and `s2` the termination address:

```text
        0x1000  addi t0, x0, 5
        0x1004  sb   t0, 0(s1)     # output 5
        0x1008  addi t1, x0, 1
        0x100c  sb   t1, 0(s2)     # store 1 to the termination word
        0x1010  jal  x0, next      # a jump, but not a PC stall
next:   0x1014  addi t0, x0, 6
        0x1018  sb   t0, 0(s1)     # output 6
        0x101c  jal  x0, 0         # jump to itself: the PC stall, where Jolt's tracer stops
```

Jolt's tracer executes it to the end and stops at `jal x0, 0`, with output 6 and no panic.

A cheating prover generates a witness that makes it look like the execution stops at `jal x0, next`, and pads the rest with no-ops.
The PC constraints accept it exactly as in [A Proof Can Stop At Any Jump](@/blog/proof-stops-at-any-jump/index.md).

It also has to pass the final check against the false claim "output 5, no panic":

- At the output word, `RamValFinal(a) = PublicIo(a)` is `5 = 5`: the store at 0x1004 wrote 5.
- At the panic word, it is `0 = 0`: the program never stores there.
- At the termination word, it is `1 = 1`: the RAM table keeps the 1 stored at 0x100c, although Jolt's tracer ignored that store.
- At every other word of the I/O region, it is `0 = 0`.

This lets the cheating prover make the claim "output 5, no panic".
If the prover were honest, the claim would be "output 6, no panic".
Hence this is a soundness issue.

### Core Issue

Jolt's tracer ignores stores to the termination word and loads it as 0, while the constraints treat it as ordinary memory.
For a "no panic" claim, the final check only asks that the termination word hold 1, which one store of 1 achieves.
After that store, a witness can make the execution look as if it stops at any later JAL or JALR.

The same disagreement affects loads.
After a store of 1, Jolt's tracer loads the termination word as 0, while every witness reads 1.
A program that branches on that load then follows one path under Jolt's tracer and the other in every witness.
