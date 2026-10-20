+++
title = "A Host Call Can Write Any Value To Its Destination Register"
date = 2026-10-20
draft = false

[extra]
hidden = false
+++

Everything in this post is with respect to commit [`8bbb2357`](https://github.com/a16z/jolt/tree/8bbb2357890928d8f83b00ca542879077c4d3d28).


## Background

A host call is how a guest asks Jolt's tracer to do something outside the program: write advice, record a cycle count, or print.
In the program it is one instruction, `VirtualHostIO`, a custom instruction with opcode 0x5B.
Jolt's tracer reads the call's arguments from registers `a0` to `a3`, and never writes the instruction's destination register:

```rust
impl VirtualHostIO {
    fn exec(&self, cpu: &mut Cpu, _: &mut <VirtualHostIO as RISCVInstruction>::RamAccess) {
        let call_id = cpu.x[10] as u32;

        if call_id == JOLT_ADVICE_WRITE_CALL_ID {
            // ...
        } else {
            // ...
            if call_id == JOLT_CYCLE_TRACK_CALL_ID {
                let _ = cpu.handle_jolt_cycle_marker(ptr, len, event);
            } else if call_id == JOLT_PRINT_CALL_ID {
                let _ = cpu.handle_jolt_print(ptr, len, event);
            }
        }
    }
}
```
[Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/tracer/src/instruction/virtual_host_io.rs#L19-L39)

The SDK always names `x0` as the destination, but Jolt's decoder accepts a host call with any destination register:

```rust
(0b010, _) => Ok(SourceInstructionKind::VirtualHostIO(
    jolt_riscv::instructions::VirtualHostIO(()),
)),
```
[Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-program/src/image/decode.rs#L192-L209)

In the constraints, `VirtualHostIO` is declared with no flags at all:

```rust
jolt_instruction!(
    /// Virtual HOST_IO: host I/O side-effect instruction.
    VirtualHostIO
);
```
[Reference](https://github.com/a16z/jolt/blob/8bbb2357890928d8f83b00ca542879077c4d3d28/crates/jolt-riscv/src/instructions/virt/host_io.rs#L3-L6)

### Constraints

Each cycle records the value its instruction writes to its destination register, `RdWriteValue`.
Three constraints fix that value, each switched on by a flag.

An instruction that writes its lookup output, such as an ADD, writes `LookupOutput`:

```text
WriteLookupOutputToRD(t) · (RdWriteValue(t) − LookupOutput(t)) = 0
```

A jump writes the address of the instruction after it:

```text
Jump(t) · (RdWriteValue(t) − (UnexpandedPC(t) + 4 − 2·IsCompressed(t))) = 0
```

A load writes the value it read:

```text
Load(t) · (RamReadValue(t) − RdWriteValue(t)) = 0
```

The register history then gives the destination register `rd` the value `RdWriteValue` at the next cycle:

```text
RegistersVal(rd, t + 1) = RdWriteValue(t)
```

`VirtualHostIO` sets none of the three flags, so nothing fixes its `RdWriteValue`.

### Example

Consider this program, shown with made-up addresses, where `s1` holds the first address of the output region and `s2` the termination address:

```text
        0x1000  addi a0, x0, 0              # call number 0: no host call matches
        0x1004  addi t0, x0, 5
        0x1008  .insn i 0x5B, 2, t0, x0, 0  # VirtualHostIO with destination t0
        0x100c  sb   t0, 0(s1)              # output t0
        0x1010  addi t1, x0, 1
        0x1014  sb   t1, 0(s2)              # store 1 to the termination word
        0x1018  jal  x0, 0                  # PC stall: Jolt's tracer stops here
```

Jolt's tracer does nothing at the host call, because no host call has number 0, and leaves `t0` at 5.
It ends with output 5 and no panic.

A cheating prover generates a witness for the same execution, except that at the host call it records `RdWriteValue` as 9.
From the next cycle on, its register table holds 9 in `t0`, so the store at 0x100c writes 9 to the output region.

Before the host call, the witness is honest, so the verifier should accept those cycles.
From the host call on, we show that the verifier still accepts:

- At cycle $t$, the host call, all three flags are 0:
  - `WriteLookupOutputToRD(t) · (RdWriteValue(t) − LookupOutput(t)) = 0` is `0 · (9 − …) = 0`.
  - `Jump(t) · (RdWriteValue(t) − …) = 0` is `0 · (9 − …) = 0`.
  - `Load(t) · (RamReadValue(t) − RdWriteValue(t)) = 0` is `0 · (… − 9) = 0`.
  - `RegistersVal(t0, t + 1) = RdWriteValue(t)` is `9 = 9`.
- Every later cycle is the honest execution of the remaining instructions with 9 in `t0`.

It also has to pass the final check against the false claim "output 9, no panic":

- At the output word, `RamValFinal(a) = PublicIo(a)` is `9 = 9`: the store at 0x100c wrote 9.
- At the panic word, it is `0 = 0`: the program never stores there.
- At the termination word, it is `1 = 1`: the store at 0x1014 wrote 1.
- At every other word of the I/O region, it is `0 = 0`.

This lets the cheating prover make the claim "output 9, no panic".
If the prover were honest, the claim would be "output 5, no panic".
Hence this is a soundness issue.

### Core Issue

Jolt's tracer never writes a host call's destination register.
The constraints fix `RdWriteValue` only for instructions that write a lookup output, jumps and loads, and a host call is none of these.
So when a host call names a register other than `x0`, a witness can give that register any value.
When the destination is `x0`, Jolt rewrites it to a temporary register, which later instructions always write before they read it, so that case is harmless.
