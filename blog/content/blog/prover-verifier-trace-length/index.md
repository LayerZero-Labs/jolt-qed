+++
title = "The Verifier Accepts Witnesses Jolt's Prover Never Builds"
date = 2026-10-20
draft = false

[extra]
hidden = false
+++

Everything in this post is with respect to commit [`8bbb2357`](https://github.com/a16z/jolt/tree/8bbb2357890928d8f83b00ca542879077c4d3d28).


## Jolt's prover

Jolt's prover chooses the witness's length from the number of rows in the trace.
It adds one row, rounds up to a power of two, and uses at least 256:

```rust
let trace_length = dimensions
    .trace_length
    .checked_add(1)
    .and_then(usize::checked_next_power_of_two)
    // ...
    .max(MIN_PADDED_TRACE_LENGTH);
```
[Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-prover/src/config.rs#L73-L80)

If that length is more than the instance's maximum, Jolt's prover stops with an error and proves nothing ([Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-prover/src/config.rs#L126)).

The added row means the last cycle of every witness Jolt's prover builds is a no-op.
Jolt's witness code relies on this:

```rust
/// At `T - 1` constraint 21
/// (`ShouldJump = Jump · (1 − NextIsNoop)`) forces `ShouldJump = 0`, which
/// holds under either convention only because the padded trace ends in a
/// NoOp row (`Jump = 0` there) — the padding every prover config guarantees.
```
[Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/witnesses/flags.rs#L29-L35)

## The verifier

The verifier's check on the witness's length is:

```rust
if !trace_length.is_power_of_two() || trace_length > program.max_padded_trace_length() {
    return Err(VerifierError::InvalidTraceLength { /* ... */ });
}
```
[Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-verifier/src/verifier.rs#L378-L383)

We found no constraint that requires the last cycle to be a no-op.
The only constraints that mention no-ops read each cycle's no-op flag from its bytecode row, define `ShouldJump`, and set `NextIsNoop`, which is 1 at the last cycle whatever that cycle is.
We found no check that the length is at least 256, and Jolt's preprocessing accepts any maximum ([Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-program/src/preprocess/program.rs#L21-L35)).

## Example

Take a program whose execution takes exactly 256 cycles, ending at the PC stall `jal x0, 0`, and an instance whose maximum is 256.

Jolt's prover adds one row to the 256, rounds up to 512, and stops with an error, because 512 is more than 256.

A 256-cycle witness, with the stall on its last cycle and no padding, still satisfies the constraints.
To see this, start from the 512-cycle witness Jolt's prover would build if the maximum were 512, and cut off its 256 padding cycles:

- Padding cycles change no register and no memory word, so the register history, the memory history and the final memory stay the same.
- At the new last cycle, the end of the witness forces the "next" columns to the values a padding row gave them: next PC 0, next is a no-op 1, next is virtual 0.
- Every other cycle is unchanged.

Its length, 256, is a power of two and within the maximum, so the verifier accepts it.

The same happens below the minimum.
With a maximum of 128, Jolt's prover refuses every program, because it never uses fewer than 256 cycles, while the verifier's length check accepts a witness of 128 cycles.

## A third party can make this proof

Jolt's prover will not make the 256-cycle proof from the example.
Anyone else can, by taking Jolt's prover and changing two things:

- Choose the witness's length as the number of rows rounded up to a power of two, without adding one.
- At the last cycle, set `ShouldJump` to 0, as constraint 21 requires; on a final jump, Jolt's witness code would set it to 1, because it does not count a missing next row as a no-op ([Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-witness/src/witnesses/flags.rs#L116-L126)).

As far as we can tell, nothing else in Jolt's prover needs to change, and the verifier accepts the proof it produces.
We have not built such a proof.

## Why it matters

The claim proved in the example is true: the execution does end at that stall with those outputs.
So no false claim is accepted.
But the verifier accepts proofs that Jolt's prover never makes, so the two disagree on which executions can be proved.

At the last cycle the constraints also never check a jump's target, because `ShouldJump` is forced to 0 there.
The same holds at a jump followed by padding, where `ShouldJump` is also 0, so a witness can stop its execution after any JAL or JALR; we describe this in a separate note.

## Question

Is "the last cycle is a no-op" meant to be enforced by the verifier, or only guaranteed by Jolt's prover?
If only by Jolt's prover, which rule should decide what can be proved: Jolt's prover's, at least one padding row and at least 256 cycles, or the verifier's, any power of two up to the maximum?
