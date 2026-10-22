+++
title = "Jolt's Tracer Rejects Memory Accesses The Constraints Accept"
date = 2026-10-20
draft = false

[extra]
hidden = false
+++

Everything in this post is with respect to commit [`8bbb2357`](https://github.com/a16z/jolt/tree/8bbb2357890928d8f83b00ca542879077c4d3d28).


## Background

Jolt's tracer checks the address of every load and store against the memory layout, and stops with a Rust panic when the access is not allowed.
Below RAM, a store is allowed only to the output region, the panic word and the termination word:

```rust
let ok = if is_write {
    jolt_device.is_output(ea)
        || jolt_device.is_panic(ea)
        || jolt_device.is_termination(ea)
} else {
    // ...
};
assert!(
    ok,
    "Illegal device {}: Unknown memory mapping: 0x{ea:X}\n{layout:#?}",
    action.to_lowercase(),
);
```
[Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/emulator/mmu.rs#L112-L173)

So a store to the inputs, or to the trusted or untrusted advice, stops Jolt's tracer.

### Constraints

Each cycle that accesses memory selects one word `a` of the witness's memory.
A store writes the value of its source register:

```text
Store(t) · (RamWriteValue(t) − Rs2Value(t)) = 0
```

The memory history then gives the selected word that value at the next cycle:

```text
RamVal(a, t + 1) = RamWriteValue(t)
```

A load reads the selected word's current value, and writes it to its destination register:

```text
RamReadValue(t) = RamVal(a, t)
Load(t) · (RamReadValue(t) − RdWriteValue(t)) = 0
```

None of these constraints looks at which region the word `a` is in.
At the end, the final check compares the I/O region with the claim, so the input words must again hold the claimed inputs.

### Example

Consider this program with input 2, shown with made-up addresses, where `s3` holds the input address, `s1` the first address of the output region and `s2` the termination address:

```text
        0x1000  addi t0, x0, 7
        0x1004  sb   t0, 0(s3)     # store 7 over the input: Jolt's tracer panics here
        0x1008  lbu  t1, 0(s3)     # read it back
        0x100c  sb   t1, 0(s1)     # output it
        0x1010  addi t2, x0, 2
        0x1014  sb   t2, 0(s3)     # put the input back
        0x1018  addi t3, x0, 1
        0x101c  sb   t3, 0(s2)     # store 1 to the termination word
        0x1020  jal  x0, 0         # PC stall
```

Jolt's tracer panics at the store at 0x1004, so it never finishes this program and there is no true claim about its output.

A cheating prover generates a witness for the execution in which the input word is ordinary memory: the store writes 7, the load reads 7 back, the output is 7, and the input is put back to 2.

Before the store at 0x1004, the witness is honest, so the verifier should accept those cycles.
From that store on, we show that the verifier still accepts:

- At the store at 0x1004, `Store(t) · (RamWriteValue(t) − Rs2Value(t)) = 0` is `1 · (7 − 7) = 0`, and `RamVal(input, t + 1) = RamWriteValue(t)` is `7 = 7`.
- At the load at 0x1008, `RamReadValue(t) = RamVal(input, t)` is `7 = 7`, and the load writes 7 to `t1`.
- At the store at 0x1014, the input word goes back to 2.
- Every other cycle is the honest execution of its instruction.

It also has to pass the final check against the false claim "input 2, output 7, no panic":

- At the input word, `RamValFinal(a) = PublicIo(a)` is `2 = 2`: the store at 0x1014 put the input back.
- At the output word, it is `7 = 7`: the store at 0x100c wrote 7.
- At the panic word, it is `0 = 0`: the program never stores there.
- At the termination word, it is `1 = 1`: the store at 0x101c wrote 1.
- At every other word of the I/O region, it is `0 = 0`.

This lets the cheating prover make the claim "input 2, output 7, no panic".
If the prover were honest, there would be no claim: Jolt's tracer stops with a panic at the store at 0x1004.
Hence this is a soundness issue.

### Core Issue

Jolt's tracer allows a load or store only at certain addresses, and stops with a panic at any other.
The constraints treat every word of the witness's memory as ordinary memory, wherever it is.
So a witness can carry out a load or store that Jolt's tracer rejects.

The same mismatch covers these other accesses, which Jolt's tracer also rejects:

- A store to the trusted or untrusted advice.
  The final check does not cover the advice, so the program does not even need to put it back.
- A store at address 0.
  In the witness, address 0 selects no word and forces the stored value to be 0, so a store of 0 there passes as an instruction that does nothing.
- A load or store between the end of the I/O region and the start of RAM, when rounding the I/O region up to a power of two puts that gap inside the witness's memory.
- A store to the stack canary, the guard region between the program and the stack.
- A load or store at or above the end of the heap, when rounding the memory size up to a power of two puts those words inside the witness's memory.
