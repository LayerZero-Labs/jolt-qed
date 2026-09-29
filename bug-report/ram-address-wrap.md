# Wrapping LD address: the honest witness fails the RAM-address constraint

> [!NOTE]
> The following issue text is _mostly_ AI generated. The issue surfaced while trying to formally verify that an honest jolt witness satisfies the RAM-address constraint.
> On being unable to close the proof, we first checked if we translated Rust logic correctly in Lean, both manually, and with AI audit.
> Following, this we asked AI to find the counter example that prevents the theorem from closing.
> It found the edge case, ran tests on Jolt and generated this report.
> The report was then proof read and posted here.

Reproduced against the local Rust Jolt checkout at `922af71c7d7f646a336ff69dc386439b12ee0d0f`. This concerns constraint (01) in [our checklist](../JoltConstraints/constraints.md), row index 0 of Rust's stage-1 R1CS matrix. GitHub links below identify the reviewed files; the result comes from running the local checkout.



## Counterexample

Assemble these instructions into an RV64 ELF whose entry point is `0x80000000`:

```asm
addi x1, x0, -8    # 0xff800093; x1 = 0xfffffffffffffff8
ld   x2, 8(x1)     # 0x0080b103; effective address wraps to 0
jal  x0, 0         # 0x0000006f; self-jump at 0x80000008 ends the trace
```

[Rust's `LD::exec`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/tracer/src/instruction/ld.rs#L16-L30) uses `wrapping_add`, so the load address is `0`. [The MMU](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/tracer/src/emulator/mmu.rs#L144-L190) permits a load from this zero-padding address. [`load_doubleword` calls `trace_load`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/tracer/src/emulator/mmu.rs#L368-L375), which [records](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/tracer/src/emulator/mmu.rs#L525-L537) `RAMRead { address: 0, value: 0 }`; the [device returns zero](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/common/src/jolt_device.rs#L121-L147). After the load, `x1 = 0xfffffffffffffff8` and `x2 = 0`.

Jolt's [`build_jolt_program`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-program/src/execution/mod.rs#L27-L39) accepts this ELF and expands it to three bytecode rows. The normal `tracer::trace` executes three cycles without a device panic. [`JoltProgramPreprocessing::new`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-program/src/preprocess/program.rs#L20-L39) succeeds, and [`TracerBackend::trace_compact`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/tracer/src/execution_backend.rs#L61-L85) accepts the execution and produces three proof-facing rows. The `LD` row passes the load capture checks because its RAM read and destination value are both zero. The final `JAL` returns to its own address, the [PC-stall termination condition](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/tracer/src/lib.rs#L329-L339).

## Honest witness

The actual Rust witness extractors return these values on the `LD` row:

| Witness value | Value | Source |
| --- | --- | --- |
| `OpFlags.Load` | `1` | [`OpFlag::extract_indexed`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-witness/src/witnesses/flags.rs#L155-L164) reads the row's load flag. |
| `OpFlags.Store` | `0` | The row is an `LD`. |
| `RamAddress` | `0` | [`RamAddress::extract`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-witness/src/witnesses/ram.rs#L41-L48) reads the captured address. |
| `Rs1Value` | `0xfffffffffffffff8` | [`Rs1Value::extract`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-witness/src/witnesses/registers.rs#L25-L32) reads the captured base register. |
| `Imm` | `8` | [`Imm::extract`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-witness/src/witnesses/operands.rs#L141-L151) reads the decoded signed offset. |

The extractors also return `RamReadValue = 0`, `RamHammingWeight = false`, and `RemappedRamAddress = None`. Address zero is explicitly [treated as no remapped RAM word](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/common/src/jolt_device.rs#L505-L521); it does not cause trace conversion or witness extraction to fail.

## Failed constraint

[Rust's constraint row 0](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-r1cs/src/constraints/rv64.rs#L199-L209) requires, over the proof field `Fr`:

```text
(Load + Store) × (RamAddress − Rs1Value − Imm) = 0
```

Substituting the extracted values gives:

```text
(1 + 0) × (0 − (2^64 − 8) − 8) = −2^64 ≠ 0
```

The CPU's address addition wraps modulo `2^64`; the R1CS subtraction is field arithmetic and does not wrap there. Evaluating the actual `rv64_spartan_outer_constraints::<Fr>()` matrix with these extracted cells returns `Err(0)`, identifying this same first constraint row. This is the local residual of one R1CS row, not a claimed value for the full challenge-weighted sumcheck.

## Why this is a completeness bug

Rust executes the load, accepts the converted proof trace, and derives the witness values above. That honest witness cannot satisfy a required stage-1 constraint. Changing `RamAddress` to `2^64` would misstate the address actually read; changing `Rs1Value` would misstate the source register. The matching [Lean constraint](../JoltConstraints/Constraints/RamAddrEqRs1PlusImmIfLoadStore.lean) and [Lean witness address](../JoltConstraints/witness_helpers/ram_address.lean) preserve the same behavior, so the missing Lean proof exposes this Rust inconsistency.

A standalone Rust check ran the decoded instructions on `Cpu`, converted their cycles through [`build_trace_rows`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/tracer/src/trace_row.rs#L151-L160), called the witness extractors on the load row, and evaluated the stage-1 matrix. It separately passed the assembled ELF through the normal program builder, tracer, preprocessing, and compact trace backend, confirming the same load-row values. It printed:

```text
cycles=3 rows=3
cpu_pc=0x80000008 cpu_x1=0xfffffffffffffff8 cpu_x2=0x0
load=true store=false ram_address=0x0 rs1_value=0xfffffffffffffff8 imm=8
ram_read_value=0 ram_hamming_weight=false remapped_ram_address=None
residual_nonzero=true first_failing_row=Err(0)
elf_cycles=3 elf_device_panic=false
program_bytecode=3 elf_rows=3 compact_rows=3
```

An end-to-end prover/verifier run was not performed. The confirmed issue is that a valid ELF accepted by Jolt's program builder and proof-trace backend has an honest witness that violates the R1CS relation; it is not evidence that an invalid proof can be accepted.
