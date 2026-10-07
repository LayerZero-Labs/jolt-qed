# Final RAM misplaces bytes more than 2 GiB above RAM_START

> [!NOTE]
> This issue surfaced while formally verifying, in Lean, that the honest Jolt
> witness satisfies the final-RAM check. Our Lean model of the final RAM put every
> byte at its own address, and an audit against Rust found that Rust does not for
> bytes more than 2 GiB above `RAM_START`. We then built the counterexample below
> and ran it against Jolt. The text was drafted with AI assistance and proofread.

## Summary

For a guest whose RAM extends more than 2 GiB above `RAM_START`, the witness
builds the final RAM (`RamValFinal`) with some bytes in the wrong slot. The
final-RAM check (`RamValFinal(k) = RamValInit(k) + Σ_j RamInc(j)·ra(k, j)`) then
fails, so a valid execution that the tracer and `ProverConfig::derive_compact`
accept cannot be proven. This is a completeness issue; it does not let an invalid
proof be accepted.

Nothing in Jolt rules such a guest out: `MemoryLayout::try_new` only rejects
sizes that overflow 64 bits, and `compute_max_ram_k` grows with the heap.

## Counterexample

A 2 GiB heap, and a program that stores one byte at `0x1_0000_0000`:

```asm
addi x6, x0, 1
slli x6, x6, 32     # x6 = 0x1_0000_0000 (RAM_START + 2 GiB)
addi x5, x0, 7
sd   x5, 0(x6)      # store 7 there
jal  x0, 0          # self-jump ends the trace
```

`MemoryConfig`: no inputs or advice, `max_output_size = 8`, `stack_size = 4096`,
`heap_size = 0x8000_0000`. This puts `heap_end` at `0x1_0000_2340`, so the store
is a legal heap write.

## How to reproduce

The three files next to this README build the ELF and run it through the same
steps as `jolt-sdk/src/host_utils.rs`:
1. `build_jolt_program` and `JoltProgramPreprocessing::new`;
2. `TracerBackend::trace_compact`;
3. `ProverConfig::derive_compact`;
4. the witness's `RamInc` and `RamValFinal` tables.

The program then evaluates both sides of the final-RAM check at the two slots
involved:
- `RamValInit` from preprocessing: the program's first word at `RAM_START`, and 0
  at `0x1_0000_0000`;
- the store's `RamInc` at its remapped slot.

```sh
sh run.sh /absolute/path/to/jolt     # needs about 17 GiB of free RAM
```

Output (Jolt `8e536f19`; every file involved is unchanged at `629ed77b`):

```text
lowest=0x7fffffe0 stack_end=0x800012c0 heap_end=0x100002340
tracer: rows=5 panic=false
row=3 store=true ram_address=0x100000000 slot=Some(268435460) read=0x0 write=0x7
prover config: trace_length=256 ram_K=536870912
building RamValFinal (536870912 slots)...
slot 4 at RAM_START (0x80000000): RamValFinal=144980585332343559 | RamValInit + sum(RamInc*ra)=144980585332343571 | check holds=false
slot 268435460 at 0x1_0000_0000: RamValFinal=0 | RamValInit + sum(RamInc*ra)=7 | check holds=false
```

The check fails in two slots:
- **Slot 268435460 (`0x1_0000_0000`):** the store wrote 7 there, but `RamValFinal` is 0.
- **Slot 4 (`RAM_START`):** the 7 was filed here instead. It overwrote the low byte
  of the program's first word, so `0x0203131300100313` became `0x0203131300100307`
  (`…571` vs `…559`).

## Cause

Both tracers hand the witness the final memory as RAM-relative addresses, where
address 0 is `RAM_START_ADDRESS`:
- The emulator's memory is indexed from `DRAM_BASE`
  ([`mmu.rs#L964-L971`](https://github.com/a16z/jolt/blob/629ed77b5c999fb2f52e5781b2b98a04ed6cf5ed/tracer/src/emulator/mmu.rs#L964-L971)).
- That inner memory is what `finish_emulator` takes
  ([`lib.rs#L158`](https://github.com/a16z/jolt/blob/629ed77b5c999fb2f52e5781b2b98a04ed6cf5ed/tracer/src/lib.rs#L158)).
- It is what `materialized_nonzero_bytes` lists
  ([`memory.rs#L341-L369`](https://github.com/a16z/jolt/blob/629ed77b5c999fb2f52e5781b2b98a04ed6cf5ed/tracer/src/emulator/memory.rs#L341-L369)),
  into `TraceOutput::final_memory`
  ([`execution_backend.rs#L291-L293`](https://github.com/a16z/jolt/blob/629ed77b5c999fb2f52e5781b2b98a04ed6cf5ed/tracer/src/execution_backend.rs#L291-L293)).
- The x86 tracer states the convention
  ([`native/memory.rs#L81-L84`](https://github.com/a16z/jolt/blob/629ed77b5c999fb2f52e5781b2b98a04ed6cf5ed/crates/jolt-tracer-x86/src/native/memory.rs#L81-L84)):
  "RAM-relative (address 0 = `RAM_START_ADDRESS`) — the convention the reference
  backend's `Memory::materialized_nonzero_bytes` uses for `TraceOutput::final_memory`".

`populate_final_memory_image`
([`ram.rs#L198-L232`](https://github.com/a16z/jolt/blob/629ed77b5c999fb2f52e5781b2b98a04ed6cf5ed/crates/jolt-witness/src/backend/trace/ram.rs#L198-L232))
converts each address differently depending on its size:

```rust
let absolute_address = if address >= dram_start {
    address
} else {
    dram_start.checked_add(address)...
};
```

- A RAM-relative address of `0x8000_0000` or more is taken as already absolute.
  Such an address only exists when the guest writes more than 2 GiB above
  `RAM_START`.
- In the counterexample, the byte at `0x1_0000_0000` has RAM-relative address
  `0x8000_0000`, so it is filed at absolute `0x8000_0000`, which is slot 4.
- Its own slot is left at 0.

`RamValFinal` comes only from this path:
`TraceBackend::oracle_table` →
[`materialize_ram_val_final`](https://github.com/a16z/jolt/blob/629ed77b5c999fb2f52e5781b2b98a04ed6cf5ed/crates/jolt-witness/src/backend/trace/ram.rs#L70-L78)
→ [`final_ram_state`](https://github.com/a16z/jolt/blob/629ed77b5c999fb2f52e5781b2b98a04ed6cf5ed/crates/jolt-witness/src/backend/trace/ram.rs#L132-L196).

## Scope of what was checked

We ran the tracer, `derive_compact` and the witness, and evaluated the final-RAM
identity directly. We did not run `dory::prove` or `verify`. The identity that
fails is the one Stage 4's `RamValCheck` reduces, so we expect the prover to fail
there.
