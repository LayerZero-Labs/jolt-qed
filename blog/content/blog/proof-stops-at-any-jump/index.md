+++
title = "A Proof Can Stop At Any Jump"
date = 2026-10-20
draft = false

[extra]
hidden = true
+++

Everything in this post is with respect to commit [`8bbb2357`](https://github.com/a16z/jolt/tree/8bbb2357890928d8f83b00ca542879077c4d3d28).


## Background

Jolt's tracer stops an execution only at a step that leaves the PC where it was, such as `j .`.
That is the `PC` before and after execution of this instruction is the same. 
This signals to Jolt's tracer that the program has finished executing.

```rust
fn step_emulator(emulator: &mut Emulator, prev_pc: &mut u64, trace: Option<&mut Vec<Cycle>>) {
    let pc = emulator.get_cpu().read_pc();
    // ...
    if *prev_pc == pc {
        return;
    }
    emulator.tick(trace);
    *prev_pc = pc;
}
```
[Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/lib.rs#L328-L338)

### Constraints

Jolt has two PCs, an unexpanded and an expanded one, to account for bytecode expansion.
The first constraint checks that the unexpanded next PC at cycle $t$ equals the unexpanded PC at cycle $t + 1$.

```text
NextUnexpandedPC(t) = UnexpandedPC(t + 1)
```

The next two constraints handle jumps.
The `ShouldJump` flag is set at cycle $t$ if cycle $t$ is a JAL or JALR and cycle $t + 1$ is not padding:

```text
ShouldJump(t) = Jump(t) · (1 − NextIsNoop(t))
```

If it is set, the unexpanded next PC must be `LookupOutput`, which holds the target of the jump:

```text
ShouldJump(t) · (NextUnexpandedPC(t) − LookupOutput(t)) = 0
```

The next two handle branches, in the same pattern as jumps.
The `ShouldBranch` flag is set at cycle $t$ if cycle $t$ is a branch (BEQ, BNE, BLT, BGE, BLTU or BGEU) and its condition holds, in which case `LookupOutput` is 1:

```text
ShouldBranch(t) = LookupOutput(t) · Branch(t)
```

If it is set, the unexpanded next PC must be the branch target, the current address plus the immediate:

```text
ShouldBranch(t) · (NextUnexpandedPC(t) − (UnexpandedPC(t) + Imm(t))) = 0
```

Unlike `ShouldJump`, `ShouldBranch` does not depend on whether the next cycle is padding.

The next one covers every other instruction.
If cycle $t$ is neither a jump nor a branch whose condition holds, the unexpanded next PC must be the address of the following instruction: the current address plus 4, or plus 2 for a compressed instruction.
While the rows of one expanded instruction are still running, `DoNotUpdateUnexpandedPC` is 1 and the address stays the same.

```text
(1 − ShouldBranch(t) − Jump(t)) · (NextUnexpandedPC(t) − (UnexpandedPC(t) + 4 − 4·DoNotUpdateUnexpandedPC(t) − 2·IsCompressed(t))) = 0
```

It is switched off by `Jump`, not by `ShouldJump`, so on a JAL or JALR it never applies, even when `ShouldJump` is 0.

`Jump(t)` is 1 whenever cycle $t$ is a JAL or JALR.
`ShouldJump(t)` is 1 only when cycle $t$ is a JAL or JALR and cycle $t + 1$ is not padding.
So on a JAL or JALR followed by padding, `Jump` is 1 but `ShouldJump` is 0.

One more constraint compares the final memory with the claim.
For every memory word $a$ in the I/O region, the witness's final value `RamValFinal(a)` must equal the word the claim gives there, `PublicIo(a)`:

```text
RamValFinal(a) = PublicIo(a)
```

`PublicIo(a)` holds the claimed inputs and outputs, 1 or 0 at the panic word for "panicked" or "no panic", 1 at the termination word for a "no panic" claim, and 0 at every other word.

### Example

Consider this program, shown with made-up addresses, where `s0` holds the panic address and `s1` the first address of the output region:

```text
        0x1000  addi t0, x0, 1
        0x1004  sb   t0, 0(s0)     # the guest panics
        0x1008  addi t1, x0, 5
        0x100c  sb   t1, 0(s1)     # output 5
        0x1010  jal  x0, next      # a jump, but not a PC stall
next:   0x1014  addi t1, x0, 6
        0x1018  sb   t1, 0(s1)     # output 6
        0x101c  jal  x0, 0         # jump to itself: the PC stall, where Jolt's tracer stops
```

Jolt's tracer executes it to the end and stops at `jal x0, 0`, with output 6 and the panic flag set.

A cheating prove generates a witness that makes it look like the execution stops at `jal x0, next` and pads the rest with no-ops. 
If Jolt was sound the verifier should reject such a witness.

```text
        0x1000  addi t0, x0, 1
        0x1004  sb   t0, 0(s0)     # the guest panics
        0x1008  addi t1, x0, 5
        0x100c  sb   t1, 0(s1)     # output 5
        0x1010  jal  x0, next      # next PC recorded as 0, not 0x1014
        0x0000  no-op              # padding
        0x0000  no-op              # padding
        ...
```

But we show that the verifier accepts this witness from the cheating prover.

- At cycle $t$, the `jal x0, next`, cycle $t + 1$ is padding:
  - `NextUnexpandedPC(t) = UnexpandedPC(t + 1)` is `0 = 0`.
  - `ShouldJump(t) = Jump(t) · (1 − NextIsNoop(t))` gives `ShouldJump(t) = 1 · (1 − 1) = 0`.
  - `ShouldJump(t) · (NextUnexpandedPC(t) − LookupOutput(t)) = 0` is `0 · (0 − 0x1014) = 0`.
  - `ShouldBranch(t) = LookupOutput(t) · Branch(t)` gives `ShouldBranch(t) = 0x1014 · 0 = 0`, so the branch-target constraint is `0 · (…) = 0`.
  - `(1 − ShouldBranch(t) − Jump(t)) · (…) = 0` is `(1 − 0 − 1) · (…) = 0`.
- Every cycle after $t$ is padding, which satisfies the constraints as in any witness.

So the witness passes the PC checks.
It also has to pass the final check against the false claim "output 5, panicked":

- At the output word, `RamValFinal(a) = PublicIo(a)` is `5 = 5`: the store at 0x100c wrote 5, and no later store follows.
- At the panic word, it is `1 = 1`: the store at 0x1004 wrote 1, and the claim "panicked" gives 1.
- At the input words, it holds because the program never stores there.
- At the termination word, it is `0 = 0`: the program never stores there, and for a panicked claim the claim gives 0.
- At every other word of the I/O region, it is `0 = 0`, since the program stores nowhere else.

This lets the cheating prover make the claim "output 5, panicked".
If the prover were honest, the claim would be "output 6, panicked".
Hence this is a soundness issue.

### Core Issue

Jolt's tracer considers an execution finished only at a PC stall.
The constraints never check that the last cycle before the padding is a PC stall.
At that cycle, the first constraint requires the unexpanded next PC to equal the padding's unexpanded PC, which is 0.
After any instruction other than a JAL or JALR, the next-PC rules force a nonzero unexpanded next PC, so the padding cannot start there.
After a JAL or JALR, `ShouldJump` is 0 when the next cycle is padding, and the next-instruction rule is off, so nothing stops the unexpanded next PC from being 0.
So a witness can make the execution look as if it stops after any JAL or JALR.
The verifier then accepts a false claim whenever the program changes its output after that jump.
For a panicked claim nothing else is needed; for a "no panic" claim, the program must also have stored 1 to the termination word before the jump.
