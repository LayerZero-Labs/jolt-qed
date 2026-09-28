# A store that the device ignores breaks the RAM history constraint

## Summary

1. Rust's [`JoltDevice`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/common/src/jolt_device.rs#L57-L68) has a [`MemoryLayout`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/common/src/jolt_device.rs#L277-L301) with a termination address:

   ```rust
   pub struct MemoryLayout {
       /// The total size of the elf's sections, including the .text, .data, .rodata, and .bss sections.
       pub program_size: u64,
       // other fields...
       pub termination: u64,
       /// End of the memory region containing inputs, outputs, the panic bit,
       /// and the termination bit.
       pub io_end: u64,
   }
   ```

   The jolt device says any `address` in the following range of values is marked with `is_termination=true`:

   ```rust
   pub fn is_termination(&self, address: u64) -> bool {
       address >= self.memory_layout.termination && address < self.memory_layout.io_end
   }
   ```

   Its [`load`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/common/src/jolt_device.rs#L121-L125) returns `0` there, and its [`store`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/common/src/jolt_device.rs#L150-L155) returns without writing:

   ```rust
   pub fn load(&self, address: u64) -> u8 {
       if self.is_panic(address) {
           self.panic as u8
       } else if self.is_termination(address) {
           0 // Termination bit should never be loaded after it is set
       }
   ```

   ```rust
   pub fn store(&mut self, address: u64, value: u8) {
       if address == self.memory_layout.panic {
           self.panic = true;
           return;
       } else if self.is_panic(address) || self.is_termination(address) {
           return;
       }
   ```

2. We will write small program writes that `1` there, then reads it. The read returns `0`,
   as expected for that address.
3. Rust's tracer records the attempted write in a `RAMWrite` with
   `pre_value = 0` and `post_value = 1`. This will later affect how witness polynomials are built, and give us an completeness bug.

## Counterexample

Put these six RV64 instructions at entry address `0x80000000`:

```asm
auipc x1, 0          # x1 = 0x80000000
addi  x1, x1, -16    # x1 = 0x7ffffff0
addi  x2, x0, 1      # x2 = 1
sd    x2, 0(x1)      # try to write 1
ld    x3, 0(x1)      # read back 0
jal   x0, 0          # end by repeating the PC
```

Instructions on how to run the Jolt tracer with the following program are given below.

## Honest witness

When the tracer traces through the program,
Rust maps the termination word's byte address `0x7ffffff0` to index `2` in
its RAM tables. The reproducer supplies this `MemoryConfig`:

```rust
let memory_config = MemoryConfig {
    max_input_size: 0,
    max_trusted_advice_size: 0,
    max_untrusted_advice_size: 0,
    max_output_size: 8,
    // other fields...
};
```

In [`MemoryLayout::new`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/common/src/jolt_device.rs#L387-L449), Jolt adds 16 bytes for the panic and termination words. The
I/O region therefore needs `8 + 16 = 24` bytes, rounded up to four 8-byte
words (`32` bytes):

```rust
let io_region_bytes = max_input_size
    .checked_add(max_trusted_advice_size)
    .and_then(|s| s.checked_add(max_untrusted_advice_size))
    .and_then(|s| s.checked_add(max_output_size))
    .and_then(|s| s.checked_add(16))
    .expect("I/O region size overflow");
let io_region_words = (io_region_bytes / 8).next_power_of_two();
let io_bytes = io_region_words
    .checked_mul(8)
    .expect("I/O region byte count overflow");
// other layout calculations...
let trusted_start = RAM_START_ADDRESS
    .checked_sub(io_bytes)
    .expect("I/O region exceeds RAM_START_ADDRESS");
```

Since [`RAM_START_ADDRESS` is `0x80000000`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/common/src/constants.rs#L21), the lowest device address is
`0x7fffffe0`. The input and advice sizes are zero, so output begins there.
Rust places termination one 8-byte word after the output and another after
the panic word:

```rust
let output_start = input_end;
let output_end = output_start
    .checked_add(max_output_size)
    .expect("output_end overflow");
let panic = output_end;
let termination = panic.checked_add(8).expect("termination overflow");
```

Thus `termination = 0x7fffffe0 + 8 + 8 = 0x7ffffff0`.
The [RAM witness calls `remap_word_address`](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/crates/jolt-witness/src/backend/trace/ram.rs#L262-L274) on the accessed address. That
[function](https://github.com/abiswas3/jolt/blob/922af71c7d7f646a336ff69dc386439b12ee0d0f/common/src/jolt_device.rs#L491-L510) uses:

```rust
let lowest_address = self.get_lowest_address();
if address >= lowest_address {
    Ok(Some((address - lowest_address) / 8))
}
```

Thus the termination word's index is
`(0x7ffffff0 - 0x7fffffe0) / 8 = 2`. At cycle `t = 4`, the constraint uses
these values:

| Quantity | Value |
| --- | ---: |
| `Init(2)` | 0 |
| `RamRa(2,3)` | 1 |
| `RamInc(3)` | 1 |
| `RamVal(2,4)` | 0 |

The attempted store contributes `RamInc(3) = 1`, but the device ignores it.
The following load returns `0`, giving `RamVal(2,4) = 0`.

## Failed constraint

The RAM value-history condition sums over all `T` padded cycles, keeping only
terms strictly before `t`. For `a = 2` and `t = 4`, its full equation is:

```text
RamVal(2,4) = Init(2) + Σ_{j=0}^{T-1} (if j < 4 then RamRa(2,j) × RamInc(j) else 0)
            = Init(2) + RamRa(2,0) × RamInc(0)
                      + RamRa(2,1) × RamInc(1)
                      + RamRa(2,2) × RamInc(2)
                      + RamRa(2,3) × RamInc(3)
```

Cycles `0`, `1`, and `2` run `AUIPC`, `ADDI`, and `ADDI`, so none accesses RAM:
`RamRa(2,0) = RamRa(2,1) = RamRa(2,2) = 0`. The store at cycle `3` has
`RamRa(2,3) = 1` and `RamInc(3) = 1`. Substitution requires:

```text
RamVal(2,4) = Init(2) + 0 + 0 + 0 + 1 × 1
          0 =       0 + 0 + 0 + 0 + 1
          0 = 1
```

## Where the inconsistency starts

In the local Rust checkout, `common/src/jolt_device.rs` ignores writes to
the termination region and returns zero on reads. But
`tracer/src/emulator/mmu.rs::trace_store` records the **requested** store value
as `post_value` before the device handles the write.

`crates/jolt-witness/src/witnesses/increments.rs` turns that recorded
`0 → 1` into `RamInc = 1`. In
`crates/jolt-witness/src/backend/trace/ram.rs`, the RAM witness advances its
accumulated value to `1` from the store record, then sets the current
`RamVal` cell to the captured load value `0`. The history relation in
`crates/jolt-claims/src/protocols/jolt/relations/ram/val_check.rs` expects
those values to describe one consistent word history.

## Reproduce and scope

Download the attached `ram-val-termination-repro.zip`. It contains this
report, `run.sh`, `make_ram37_elf.py`, and `ram37_repro.rs`. From the directory
containing the downloaded ZIP, run the following commands. Replace the path
in the second command with the absolute path to your Jolt checkout (the
directory containing its `Cargo.toml`):

```sh
unzip ram-val-termination-repro.zip -d ram-val-termination-repro
sh ram-val-termination-repro/run.sh /absolute/path/to/your/jolt
```

The script generates the ELF, builds the Rust `tracer` and `jolt-witness`
crates, then checks the trace and witness values. It needs Python 3 and Rust
toolchain `1.95`. A successful run prints
`word_index=2 init=0 prefix=1 ram_val_t4=0 eq=false`. If the Rust crates are
already built in that checkout, set `SKIP_BUILD=1` before `sh` to reuse them.

The checker records the exact `MemoryConfig` that places the termination word
at `0x7ffffff0`. The `SD` and `LD` are native final rows; the native `JAL x0`
is rewritten to destination register 40 before its repeated PC ends the
trace. Neither trace reports a device panic.

Reproduced on 28 September 2026 against local Rust commit
`3cb4e24361ae2006e9713ae65d58a3fa51fd0518`. Its tracked worktree was
clean, with an unrelated untracked `nvim.log`. The confirmed path reaches
the trace and witness oracle; it does not run the full prover/verifier.
