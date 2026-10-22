+++
title = "Host Calls That Crash Jolt's Tracer Pass The Constraints"
date = 2026-10-20
draft = false

[extra]
hidden = false
+++

Everything in this post is with respect to commit [`8bbb2357`](https://github.com/a16z/jolt/tree/8bbb2357890928d8f83b00ca542879077c4d3d28).


## Background

A host call is how a guest asks Jolt's tracer to do something outside the program: write advice, record a cycle count, or print.
In the program it is one instruction, `VirtualHostIO`, a custom instruction with opcode 0x5B, and the call's arguments are in registers `a0` to `a3`.
For a cycle-count call, `a3` says whether a count starts (1) or ends (2).
On any other value, Jolt's tracer stops with a Rust panic:

```rust
pub fn handle_jolt_cycle_marker(&mut self, ptr: u32, len: u32, event: u32) -> Result<(), Trap> {
    // ...
    match event {
        JOLT_CYCLE_MARKER_START => { /* ... */ }
        JOLT_CYCLE_MARKER_END => { /* ... */ }
        _ => {
            panic!("Unexpected event: event must match either start or end marker.")
        }
    }
    Ok(())
}
```
[Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/emulator/cpu.rs#L1056-L1090)

A print call does the same on an unknown print type ([Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/emulator/cpu.rs#L1092-L1105)).
After such a panic there is no trace, so Jolt's prover produces no proof.

In the constraints, `VirtualHostIO` is declared with no flags at all:

```rust
jolt_instruction!(
    /// Virtual HOST_IO: host I/O side-effect instruction.
    VirtualHostIO
);
```
[Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-riscv/src/instructions/virt/host_io.rs#L3-L6)

### Constraints

With no flags, the only constraint that does anything on a host call's cycle is the rule for the next PC.
It is neither a jump nor a branch, so the unexpanded next PC must be the address of the following instruction:

```text
(1 − ShouldBranch(t) − Jump(t)) · (NextUnexpandedPC(t) − (UnexpandedPC(t) + 4 − 4·DoNotUpdateUnexpandedPC(t) − 2·IsCompressed(t))) = 0
```

No constraint looks at the call's arguments in `a0` to `a3`.

### Example

Consider this program, shown with made-up addresses, where `s1` holds the first address of the output region and `s2` the termination address:

```text
        0x1000  lui  a0, 0xc8
        0x1004  addi a0, a0, -0x3e2         # a0 = 0xc7c1e, the cycle-count call
        0x1008  addi a3, x0, 3              # event 3: neither start (1) nor end (2)
        0x100c  .insn i 0x5B, 2, x0, x0, 0  # VirtualHostIO: Jolt's tracer panics here
        0x1010  addi t0, x0, 5
        0x1014  sb   t0, 0(s1)              # output 5
        0x1018  addi t1, x0, 1
        0x101c  sb   t1, 0(s2)              # store 1 to the termination word
        0x1020  jal  x0, 0                  # PC stall
```

Jolt's tracer panics at the host call at 0x100c, so it never finishes this program and there is no true claim about its output.

A cheating prover generates a witness for the execution in which the host call does nothing: every instruction as written, then output 5, the termination store and the stall.

Before the host call, the witness is honest, so the verifier should accept those cycles.
From the host call on, we show that the verifier still accepts:

- At cycle $t$, the host call, `ShouldBranch(t)`, `Jump(t)`, `DoNotUpdateUnexpandedPC(t)` and `IsCompressed(t)` are 0, so the next-PC rule is `NextUnexpandedPC(t) = 0x100c + 4 = 0x1010`, the address of the next instruction.
- No other constraint looks at the host call.
- Every later cycle is the honest execution of the remaining instructions.

It also has to pass the final check against the false claim "output 5, no panic":

- At the output word, `RamValFinal(a) = PublicIo(a)` is `5 = 5`: the store at 0x1014 wrote 5.
- At the panic word, it is `0 = 0`: the program never stores there.
- At the termination word, it is `1 = 1`: the store at 0x101c wrote 1.
- At every other word of the I/O region, it is `0 = 0`.

This lets the cheating prover make the claim "output 5, no panic".
If the prover were honest, there would be no claim: Jolt's tracer stops with a panic at the host call.
Hence this is a soundness issue.

### Core Issue

Jolt's tracer can fail a host call, for example on an unknown cycle-count event or print type.
The constraints see a host call as an instruction that does nothing, so a witness can step over a host call that Jolt's tracer fails on.
The verifier then accepts claims about an execution that Jolt's tracer cannot complete.
