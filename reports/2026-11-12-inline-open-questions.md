# Inline open questions 1, 3 and 7, and the SDK call-site check (I0(c), I0(f))

This report answers questions 1, 3 and 7 of section 10 of `docs/inline-precompiles.md` and checks every SDK call site of the twelve in-scope inlines against `Pre c` (section 5.4), as phase I0 asks.
Questions 1 and 3 and the aliasing and value-range parts of I0(f) are settled by running Jolt's production code; the rest is settled by reading source.

- jolt-qed: worktree `~/claude-work/jq-inline-research`, branch `inline/i0cf-research`, based on `309ba77`.
- Jolt: `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5`, checkout `~/claude-work/jolt-inline-pin-a6b6`. Every Jolt citation below is a path in that checkout at that commit.
- Probe: `scripts/inline-open-questions/` (source identical to the binaries that produced the outputs below; see "How the runs were made").

## Summary

| Question | Answer | How settled |
|---|---|---|
| Q1. Which registration set the verifier's preprocessing uses | The set linked into the binary that runs preprocessing (`preprocess_shared_*`, `preprocess_*`, `program_preprocessing`). Registration happens at link time through `inventory`, and only crates that the binary names (or that a named crate pulls in) register. The verifier itself consults no registry: it receives the expanded program inside its preprocessing and binds it through `preprocessing_digest` | Source (verifier side), run (registration and expansion) |
| Q1. How a guest that calls an unlinked inline fails | Decoding succeeds; expansion returns `ExpansionError::UnsupportedInstruction`; `JoltProgramSource::decode`, which the SDK's preprocessing calls, panics at `crates/jolt-host/src/lib.rs:100`; `tracer::trace` panics at `tracer/src/instruction/inline.rs:310`. No preprocessing and no proof is produced. A crate that is a dependency but is never named registers nothing and fails the same way | Run (three builds) |
| Q3. Misaligned `LD`/`SD` inside an inline | Tracer: panic (`mmu.rs:321` load, `mmu.rs:429` store). Constraints: unsatisfiable (RAF admits only multiples of 8 since `629b7d959` added the alignment check on `lowest_address`). jolt-qed: `Memory_Exception`, and the rows stop there | Run (tracer), source (constraints, Lean) |
| Q3. Range that wraps past 2^64 | Tracer: panic on the first access, which is already at or above `heap_end` (`memory.rs:36`). Constraints: unsatisfiable (`RamAddress` is the unwrapped `rs1 + imm`). jolt-qed: assertion error on the first access. For the twelve inlines a wrap needs a base above `2^64 − 200`, and the first access then already fails | Run, source |
| Q3. Base above `heap_end` | Tracer: loads panic at `memory.rs:36` (before the "Illegal Memory Access" assert is reached), stores panic at `mmu.rs:166`. Constraints: unsatisfiable when the remapped index reaches `ram_k`. jolt-qed: assertion error | Run, source |
| Q3. Base below the lowest address | Tracer: loads succeed and read 0; stores panic (`mmu.rs:148`). Constraints: unsatisfiable, except an access at exactly address 0, which RAF reads as "no access". jolt-qed: loads succeed and read 0, stores fail; `NoLowLoad` and `TracerAddressChecks` already exclude the load case at the whole-run level | Run, source |
| Q3. Address 0 | Not special for any of the twelve: every buffer has at least four words, and a base of 0 therefore also accesses address 8, which the prover and RAF reject (loads) or the tracer rejects (stores) | Run, source |
| Q3. What 629b7d959 and 4e55c9a5f changed for `LD`/`SD` | `629b7d959` kept `RamAddress = rs1 + imm` for `LD`/`SD`, added the verifier check that `lowest_address` is a multiple of 8 (which makes misaligned `LD`/`SD` unsatisfiable), and added the expansion check that inline load and store offsets lie in [−2048, 2047]. `4e55c9a5f` range-checks the value an `LD` loads; it changes no address | Source |
| Q7. Whether `trace_file` affects proving | No. Only `store_inlines` reads it, and nothing calls `store_inlines` | Source (`git grep`) |
| I0(f). SDK call sites | All 20 call sites (6 hash, 14 secp256k1) satisfy `Pre c` for every caller of the safe API: buffers are 8-aligned Rust objects in RAM, output buffers are fresh locals or `&mut self` fields, BLAKE2's flag comes from a `bool`, and secp256k1 inputs are canonical through checked constructors. Public bypasses exist: `ECField::from_u64_arr_unchecked`, `ECField::div_assume_nonzero`, `AffinePoint::new_unchecked`, `AffinePoint::from_u64_arr_unchecked` and `keccak256_absorb_permute` | Source |
| I0(f). Overlap | No overlap condition is needed for any of the twelve: every load comes before every store, and the advice reads its operands before any row runs. Every aliasing shape tried gave the same output as disjoint buffers, and `GLVR_ADV` with `rs3 = rs1` returns the correct decomposition while overwriting `k` | Run |
| I0(f). Value ranges | BLAKE2 accepts any `is_final` but means BLAKE2 only for 0 and 1. Jolt's secp256k1 advice needs the quotient `⌊a·b/q⌋` to fit in 256 bits (canonical inputs suffice; `a = p, b = 1` works, `a = b = 2^256 − 1` panics) and a divisor that is nonzero modulo `q` (`b = p` panics). `GLVR_ADV` reduces `k` modulo `n` and needs no range | Run |

## How the runs were made

The probe builds small RISC-V ELF images in memory (`src/elf.rs`): one `AUIPC` and one `LD` per operand register load the operand values from a data section, one inline instruction follows, and the image ends with `j .`.
Operands go in `x10` (`rs1`), `x11` (`rs2`) and `x12` (the `rd` field, which the secp256k1 inlines read as `rs3`); the hash inlines get `rd = x0`.
Every row count below therefore includes the setup rows and the final jump.
It then calls Jolt's production entry points directly: `jolt_program::image::decode_elf`, `jolt_program::build_jolt_program_with_inline_provider` (with `TracerInlineExpansionProvider`), `jolt_program::build_jolt_program`, `jolt_host::JoltProgramSource::decode` through a small `ElfSource` implementation, and `tracer::trace`.
For every successful trace it also passes each recorded RAM address to `MemoryLayout::remap_word_address`, which is the check Jolt's prover applies when it builds the RAM witness (`crates/jolt-witness/src/backend/trace/ram.rs:260-283`).
Panics are caught with `catch_unwind`, and the probe prints the panic location and the first line of the message.

The inline crates are optional dependencies behind two cargo features (`scripts/inline-open-questions/Cargo.toml.in`):

- `dep-sha2` makes `jolt-inlines-sha2` (with feature `host`) a dependency, and no code names it.
- `inlines` makes all four in-scope inline crates dependencies and names each with `use jolt_inlines_X as _;` (`src/main.rs:9-16`).

I built the three binaries in `~/claude-work/i0cf-scratch/inline-probe`, one after another, with

```
JOLT_DIR=~/claude-work/jolt-inline-pin-a6b6 CARGO_TARGET_DIR=~/claude-work/.cargo-target-i0cf ./build.sh            # then copied to inline-probe-nofeat
JOLT_DIR=~/claude-work/jolt-inline-pin-a6b6 CARGO_TARGET_DIR=~/claude-work/.cargo-target-i0cf ./build.sh dep-sha2   # inline-probe-depsha2
JOLT_DIR=~/claude-work/jolt-inline-pin-a6b6 CARGO_TARGET_DIR=~/claude-work/.cargo-target-i0cf ./build.sh inlines    # inline-probe-inlines
```

and ran each subcommand as `./inline-probe-<variant> <q1|q3|alias|glv|edge>`.
The outputs are kept in `~/claude-work/i0cf-scratch/out/` and are quoted below.
`scripts/inline-open-questions/build.sh WORK_DIR` builds the same three binaries from the committed copy into `WORK_DIR/bin/`.
The committed `src/` is byte-identical to the source of the binaries above, and the `Cargo.toml` that `build.sh` generates is identical to the one they were built with (checked without compiling).
I have not yet run the committed `build.sh` end to end, because the machine's single build slot was taken while I wrote this report.

All runs use `MemoryConfig::default()` with the program size of the probe image.
The resulting layout is:

```
layout: lowest=0x7fff8000 input=0x7fffa000..0x7fffb000 output=0x7fffb000..0x7fffc000 panic=0x7fffc000 termination=0x7fffc008 io_end=0x7fffc010
        program=0x80000000..0x80001500 stack_end(canary start)=0x80001500 heap_end=0x82002580
```

## Q1. Registration set and the unlinked-inline failure

### Where the registration set comes from

- `register_inlines!` (`jolt-inlines/sdk/src/host.rs:585`) generates, for each inline, a call to `__submit_inline_op!`, which uses `inventory::submit!` (around lines 610-625).
  `inventory` collects these at link time: a registration exists only in a binary whose linker keeps the crate.
  Each inline crate puts its `register_inlines!` call in its `host` module, and a crate linked without feature `host` therefore registers nothing either (source reading; not run).
- The raw decoder accepts opcodes `0x0B` and `0x2B` as inline instructions without consulting the registry (`crates/jolt-program/src/decode.rs:85`).
- The registry is consulted at expansion: `lookup_inline` (`tracer/src/instruction/inline.rs:113-121`) returns `ExpansionError::UnsupportedInstruction` for an unregistered key, and `find_inline` (`inline.rs:102-111`) panics with "No inline registered ...".
  Neither checks for a duplicate key; both take the first match.
- `jolt-host` builds the program with the full inline profile: `JoltProgramSource::instruction_profile` defaults to `RV64IMAC_JOLT_ALL_INLINES` (`crates/jolt-host/src/lib.rs:75-77`), `build_jolt_program` uses `TracerInlineExpansionProvider` (`lib.rs:83-91`), and `decode` calls `.expect("failed to build Jolt program")` (`lib.rs:100`, in `decode` at 97-107).
- The SDK's preprocessing functions all go through `program_preprocessing`, which calls `source.decode()` (`jolt-sdk/src/host_utils.rs:116`, in `program_preprocessing` at 110-126; `preprocess_shared_program` 128-140; `preprocess_program` 150-163; `verifier_preprocessing_from_prover` 166-170).
  The macro-generated functions call these (`jolt-sdk/macros/src/lib.rs:517-537` for `preprocess_shared_*`, `from_shared_parts` at 597, `verifier_preprocessing_from_prover` around 607-620).
- The verifier crate has `tracer` only as a dev-dependency (`crates/jolt-verifier/Cargo.toml:73`, under `[dev-dependencies]` at line 62); `jolt-program` is a normal dependency (line 52).
  `JoltVerifierPreprocessing` carries the expanded program and `preprocessing_digest` (`crates/jolt-verifier/src/preprocessing.rs:208`, computed from `program.digest()` at 225), and the verifier absorbs the digest into the transcript (`crates/jolt-verifier/src/verifier.rs:385`).

The registration set is therefore the one linked into whichever binary runs preprocessing.
The verifier needs no registration: it checks proofs against the expanded rows it was handed.
If prover and verifier preprocessing come from binaries with different registrations, either preprocessing fails (as below) or the two programs differ, the digests differ, and the proof does not verify (source reading; not run).

Jolt's examples get the registration in two ways: the host crate writes `use jolt_inlines_X as _;`, or the guest crate calls the inline crate and cargo feature unification turns on `host` for the host build.
For example, `examples/sha2-ex/guest/src/lib.rs:5` calls `jolt_inlines_sha2::Sha256::digest`, and `examples/sha2-ex/Cargo.toml` lists `jolt-inlines-sha2` with `features = ["host"]`.

### Runs

The image contains the word `0x00b5000b`: `SHA256` with `rd = x0`, `rs1 = x10`, `rs2 = x11`.

```
== inline-probe-nofeat q1
linked inline registrations: 0
inline word: 0x00b5000b
(a) jolt_program::image::decode_elf(RV64IMAC_JOLT_ALL_INLINES): Ok(Ok(5))
(b) jolt_program::build_jolt_program_with_inline_provider: Ok(Err(Expansion(UnsupportedInstruction)))
(c) jolt_program::build_jolt_program (RV64IMAC_JOLT, no provider): Ok(Err(Expansion(InlineProviderRequired)))
(d) jolt_host::JoltProgramSource::decode (called by jolt-sdk program_preprocessing): Err("panic at crates/jolt-host/src/lib.rs:100: failed to build Jolt program: Expansion(UnsupportedInstruction)")
(e) tracer::trace: panic at tracer/src/instruction/inline.rs:310: jolt-program inline expansion failed: UnsupportedInstruction
```

`inline-probe-depsha2 q1` prints exactly the same lines: a dependency that no code names is dropped by the linker and registers nothing.

```
== inline-probe-inlines q1
linked inline registrations: 12
  0x0b f3=0 f7=2 BLAKE2_INLINE
  0x0b f3=0 f7=1 KECCAK256_INLINE
  0x0b f3=1 f7=1 KECCAK256_ABSORB_PERMUTE_INLINE
  0x0b f3=7 f7=5 SECP256K1_GLVR_ADV
  0x0b f3=0 f7=5 SECP256K1_MULQ
  0x0b f3=6 f7=5 SECP256K1_DIVR
  0x0b f3=5 f7=5 SECP256K1_SQUARER
  0x0b f3=4 f7=5 SECP256K1_MULR
  0x0b f3=2 f7=5 SECP256K1_DIVQ
  0x0b f3=1 f7=5 SECP256K1_SQUAREQ
  0x0b f3=0 f7=0 SHA256_INLINE
  0x0b f3=1 f7=0 SHA256_INIT_INLINE
inline word: 0x00b5000b
(a) jolt_program::image::decode_elf(RV64IMAC_JOLT_ALL_INLINES): Ok(Ok(5))
(b) jolt_program::build_jolt_program_with_inline_provider: Ok(Ok(1904))
(c) jolt_program::build_jolt_program (RV64IMAC_JOLT, no provider): Ok(Err(Expansion(InlineProviderRequired)))
(d) jolt_host::JoltProgramSource::decode (called by jolt-sdk program_preprocessing): Ok(1904)
(e) tracer::trace: ok (1904 rows)
```

The 1,904 rows are the 1,900 `SHA256` rows and the image's four other instructions (one `AUIPC`, two `LD`, the final `j .`).
Line (c) shows that the base profile without a provider rejects every inline, registered or not.

## Q3. Misaligned and out-of-range `LD`/`SD` inside an inline

### The memory rows of the twelve inlines

I recomputed the memory rows from the expansion-parity templates (`~/claude-work/expansion-parity-work/out/inline_templates.json`, Jolt `a6b6dc71`).
Every memory row of the twelve is an `LD` or `SD` whose base is an operand register (`rs1`, `rs2` or `rs3`) and whose offset is a nonnegative multiple of 8 starting at 0.
In every one of the twelve, the last `LD` comes before the first `SD`.

| Inline | Rows | `VirtualAdvice` rows | Memory rows (base, offsets, count) |
|---|---|---|---|
| `SHA256` | 1,900 | 0 | LD rs1 0..24 (4); LD rs2 0..56 (8); SD rs1 0..24 (4) |
| `SHA256_INIT` | 1,864 | 0 | LD rs2 0..56 (8); SD rs1 0..24 (4) |
| `KECCAK256` | 3,087 | 0 | LD rs1 0..192 (25); SD rs1 0..192 (25) |
| `KECCAK256_ABSORB_PERMUTE` | 3,121 | 0 | LD rs1 0..192 (25); LD rs2 0..128 (17); SD rs1 0..192 (25) |
| `BLAKE2` | 1,067 | 0 | LD rs1 0..56 (8); LD rs2 0..136 (18: 16 message words, `t`, `is_final`); SD rs1 0..56 (8) |
| `MULQ`, `MULR` | 186, 232 | 4 | LD rs1 0..24 (4); LD rs2 0..24 (4); SD rs3 0..24 (4) |
| `SQUAREQ`, `SQUARER` | 167, 213 | 4 | LD rs1 0..24 (4); SD rs3 0..24 (4) |
| `DIVQ`, `DIVR` | 194, 240 | 8 | LD rs2 0..24 (4); LD rs1 0..24 (4); SD rs3 0..24 (4) |
| `GLVR_ADV` | 13 | 6 | SD rs3 0..40 (6); no loads |

### Tracer: runs

Each memory row goes through `Mmu::load_doubleword` (`tracer/src/emulator/mmu.rs:319-327`, alignment assert at 321) or `Mmu::store_doubleword` (`mmu.rs:427-433`, alignment assert at 429).
Both call `assert_effective_address` (`mmu.rs:112-178`), but in a different order:

- `trace_store` (`mmu.rs:484-496`) asserts the address first, and a bad store fails with the MMU's own message.
- `trace_load` (`mmu.rs:472-478`) reads the doubleword for the trace before it asserts anything. A load at or above `heap_end`, or at a wrapped address, panics in `Memory::get_doubleword` (`tracer/src/emulator/memory.rs:36`, "Out of bounds memory access") and never reaches the "Illegal Memory Access" assert (around `mmu.rs:173-176`).

The advice of the secp256k1 inlines reads its operands through `InlineAdviceContext` for `Cpu` (`tracer/src/instruction/inline.rs:71-82`), which calls `mmu.load_doubleword(...).ok()`; the MMU asserts panic instead of returning `Err`, and a bad advice read panics the same way.

`./inline-probe-inlines q3` (abridged to the cases that differ; the full output is in `~/claude-work/i0cf-scratch/out/q3.txt`):

```
SHA256: rs1 = state (read, then written), rs2 = block (read), rd = x0
  valid                                            rs1=0x80000500 rs2=0x80000900: ok (1904 rows); remap: 0 access(es) at address 0 (no access), every other access remaps
  rs1 misaligned by 4                              rs1=0x80000504 rs2=0x80000900: panic at tracer/src/emulator/mmu.rs:321: assertion `left == right` failed: Unaligned load_doubleword
  rs1 misaligned by 1                              rs1=0x80000501 rs2=0x80000900: panic at tracer/src/emulator/mmu.rs:321: assertion `left == right` failed: Unaligned load_doubleword
  rs2 misaligned by 4                              rs1=0x80000500 rs2=0x80000904: panic at tracer/src/emulator/mmu.rs:321: assertion `left == right` failed: Unaligned load_doubleword
  rs1 range wraps past 2^64 (rs1 = 2^64-16)        rs1=0xfffffffffffffff0 rs2=0x80000900: panic at tracer/src/emulator/memory.rs:36: Out of bounds memory access (2305843008945258494 >= 4195504)
  rs2 range wraps past 2^64 (rs2 = 2^64-16)        rs1=0x80000500 rs2=0xfffffffffffffff0: panic at tracer/src/emulator/memory.rs:36: Out of bounds memory access (2305843008945258494 >= 4195504)
  rs1 = heap_end                                   rs1=0x82002580 rs2=0x80000900: panic at tracer/src/emulator/memory.rs:36: Out of bounds memory access (4195504 >= 4195504)
  rs1 = heap_end - 16 (straddles heap_end)         rs1=0x82002570 rs2=0x80000900: panic at tracer/src/emulator/memory.rs:36: Out of bounds memory access (4195504 >= 4195504)
  rs2 = heap_end - 32 (straddles heap_end)         rs1=0x80000500 rs2=0x82002560: panic at tracer/src/emulator/memory.rs:36: Out of bounds memory access (4195504 >= 4195504)
  rs1 in stack canary (= stack_end)                rs1=0x80001500 rs2=0x80000900: panic at tracer/src/emulator/mmu.rs:160: Stack overflow: attempted to write to 0x80001500, which is in the stack canary region. Increase stack_size in MemoryConfig (currently 4096 bytes).
  rs1 below lowest address                         rs1=0x7fff7000 rs2=0x80000900: panic at tracer/src/emulator/mmu.rs:148: Illegal device store: Unknown memory mapping: 0x7FFF7000
  rs2 below lowest address                         rs1=0x80000500 rs2=0x7fff7000: ok (1904 rows); remap: 0 access(es) at address 0 (no access), 8 rejected, first 0x7fff7000: AddressBelowLowest { address: 2147446784, lowest_address: 2147450880 }
  rs1 = 0                                          rs1=0x0 rs2=0x80000900: panic at tracer/src/emulator/mmu.rs:148: Illegal device store: Unknown memory mapping: 0x0
  rs2 = 0                                          rs1=0x80000500 rs2=0x0: ok (1904 rows); remap: 1 access(es) at address 0 (no access), 7 rejected, first 0x8: AddressBelowLowest { address: 8, lowest_address: 2147450880 }
  rs1 in gap above io_end                          rs1=0x7fffc110 rs2=0x80000900: panic at tracer/src/emulator/mmu.rs:126: I/O overflow: Attempted to read from 0x7FFFC110. Out of bounds.
  rs2 in gap above io_end                          rs1=0x80000500 rs2=0x7fffc110: panic at tracer/src/emulator/mmu.rs:126: I/O overflow: Attempted to read from 0x7FFFC110. Out of bounds.
  rs2 = input_start                                rs1=0x80000500 rs2=0x7fffa000: ok (1904 rows); remap: 0 access(es) at address 0 (no access), every other access remaps
  rs1 = input_start                                rs1=0x7fffa000 rs2=0x80000900: panic at tracer/src/emulator/mmu.rs:148: Illegal device store: Unknown memory mapping: 0x7FFFA000
  rs1 = output_start                               rs1=0x7fffb000 rs2=0x80000900: ok (1904 rows); remap: 0 access(es) at address 0 (no access), every other access remaps; output bytes written
  rs1 = panic - 24 (state covers the panic word)   rs1=0x7fffbfe8 rs2=0x80000900: ok (1904 rows); remap: 0 access(es) at address 0 (no access), every other access remaps; device panic flag SET; output bytes written
```

`KECCAK256_ABSORB_PERMUTE` gives the same outcome in every case (3,125 rows when it succeeds; 17 rejected accesses for `rs2` below the lowest address; 1 no-access and 16 rejected for `rs2 = 0`), except one: its 200-byte state at `panic − 24` runs past `io_end` and panics at `mmu.rs:126` ("I/O overflow: Attempted to read from 0x7FFFC011").

`MULQ` has no in-place buffer, and its loads and stores use different registers:

```
MULQ: rs1 = a (read), rs2 = b (read), rs3 = out (written), valid
  rs2 = heap_end - 32 (straddles heap_end)         rs1=0x80000500 rs2=0x82002560: ok (191 rows); remap: 0 access(es) at address 0 (no access), every other access remaps
  rs1 in stack canary (= stack_end)                rs1=0x80001500 rs2=0x80000900: ok (191 rows); remap: 0 access(es) at address 0 (no access), every other access remaps
  rs1 below lowest address                         rs1=0x7fff7000 rs2=0x80000900: ok (191 rows); remap: 0 access(es) at address 0 (no access), 4 rejected, first 0x7fff7000: AddressBelowLowest { address: 2147446784, lowest_address: 2147450880 }
  rs1 = 0                                          rs1=0x0 rs2=0x80000900: ok (191 rows); remap: 1 access(es) at address 0 (no access), 3 rejected, first 0x8: AddressBelowLowest { address: 8, lowest_address: 2147450880 }
  rs1 = input_start                                rs1=0x7fffa000 rs2=0x80000900: ok (191 rows); remap: 0 access(es) at address 0 (no access), every other access remaps
  rs1 = panic - 24 (state covers the panic word)   rs1=0x7fffbfe8 rs2=0x80000900: ok (191 rows); remap: 0 access(es) at address 0 (no access), every other access remaps
  rs3 misaligned by 4                              rs3=0x80000d04: panic at tracer/src/emulator/mmu.rs:429: assertion `left == right` failed: Unaligned store_doubleword
  rs3 = heap_end - 16                              rs3=0x82002570: panic at tracer/src/emulator/mmu.rs:166: Heap overflow: attempted to write to 0x82002580, which is beyond the heap. Increase heap_size in MemoryConfig (currently 33554432 bytes).
  rs3 = 0                                          rs3=0x0: panic at tracer/src/emulator/mmu.rs:148: Illegal device store: Unknown memory mapping: 0x0
  rs3 below lowest                                 rs3=0x7fff7000: panic at tracer/src/emulator/mmu.rs:148: Illegal device store: Unknown memory mapping: 0x7FFF7000
  rs3 in stack canary                              rs3=0x80001500: panic at tracer/src/emulator/mmu.rs:160: Stack overflow: attempted to write to 0x80001500, which is in the stack canary region. Increase stack_size in MemoryConfig (currently 4096 bytes).
```

The misaligned, wrapping, `heap_end` and gap cases of `MULQ` fail exactly as for `SHA256`.

In short, the tracer:

- panics on every misaligned access;
- panics on every access at or above `heap_end`, which includes every wrapping range;
- panics on stores below the lowest address, at 0, in the input region, in the gap above `io_end`, and in the stack canary;
- accepts loads below the lowest address (they read 0), loads in the stack canary and in the input, output, panic and termination words;
- accepts stores to the output region and to the panic and termination words, and a store to the panic word sets the panic flag.

### Constraints: source

Constraint 0 of the RV64 R1CS (`crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs`, comment at 212-243, rows at 244-252) is

```
(Load + Store) · (RamAddress − Rs1Value − Imm + LookupOutput) = 0
```

`LD` and `SD` look up no table. Instruction read-RAF therefore forces `LookupOutput = 0`, and `RamAddress` is the unwrapped integer `rs1 + imm`.
RAM RAF evaluation admits only `RamAddress = Σ_k ra(k)·(8k + lowest_address)` with boolean `ra`, or 0 when every `ra(k)` is 0 (no access).
The verifier rejects a layout whose `lowest_address` is at most 8 or not a multiple of 8 (`validate_ram_remap_base`, `crates/jolt-verifier/src/verifier.rs:952-973`).
Jolt's own comment states the consequences, which match the runs:

- A misaligned `LD` or `SD` has no satisfying `RamAddress`.
- A sum `rs1 + imm` that carries past 2^64 has no satisfying `RamAddress`, because every admissible address is far below 2^64.
- An access below `lowest_address` other than address 0 has no satisfying `RamAddress`; the honest prover fails earlier, in `remapped_ram_address` (`crates/jolt-witness/src/backend/trace/ram.rs:260-283`), with `InvalidWitnessData` ("failed to remap RAM access address ...").
- An access whose index reaches `ram_k` is rejected by the same function.
- Address 0 is "no access": an `LD` there reads 0 and an `SD` there changes nothing. `remap_word_address` returns `Ok(None)` for it (`common/src/jolt_device.rs:539-553`).

What the two commits changed for `LD`/`SD`:

- `629b7d959` ("floor-addressed sub-word loads and stores", #2132):
  - renamed constraint 0 from `RamAddrEqRs1PlusImmIfLoadStore` to `RamAddrEqRs1PlusImmMinusLookupIfLoadStore`; for `LD`/`SD` the address is still `rs1 + imm`;
  - added the check that `lowest_address` is a multiple of 8 to `validate_ram_remap_base` (before, only `lowest_address > 8` was checked); this is what makes a misaligned `LD`/`SD` unsatisfiable;
  - added the check in `materialize_inline` that rejects an inline load or store offset outside [−2048, 2047] with `ExpansionError::InlineMemoryOffsetOutOfRange` (`crates/jolt-program/src/expand/materialize.rs:24, 157-165`; `crates/jolt-program/src/expand/error.rs:14`);
  - removed the `VirtualAssertWordAlignment` and `VirtualAssertHalfwordAlignment` rows of the sub-word accesses, which `LD`/`SD` never used.
- `4e55c9a5f` ("range-check direct RAM loads", #2190): an `LD` routes `RdWriteValue` into the right lookup operand, and read-RAF proves that the loaded value is a 64-bit word. It pins `LookupOutput = 0` for direct loads and changes no address.

### jolt-qed Lean semantics: source

- `.LD` and `.SD` (`JoltBytecode/JoltISA/Semantics.lean:484-495` and `496-506`) compute `addr := base + imm` in `BitVec 64` (wrapping) and return `Memory_Exception` when `addr &&& 7 ≠ 0`.
  `execProgram` (`Semantics.lean:589-597`) stops at the first result that is not success: after a misaligned row the rows do not run to the end.
- An aligned row calls `Mmu.load_doubleword` or `Mmu.store_doubleword` (`JoltBytecode/JoltISA/DeviceMemory.lean`, around 132-143 and 149-164).
  At or above `RAM_START` they check `effective_address_ok` (around 43-58), which mirrors `assert_effective_address`: loads need `ea < heap_end`; stores need `ea < heap_end` and `ea` outside the canary.
  Below `RAM_START`, loads go through `load_raw?`, which accepts the I/O regions and every address at most `RAM_START − 8` (reading 0), and stores go through `store_raw?`, which accepts only the output, panic and termination words.
  Every failure is an `Error.Assertion`, the model of a tracer panic.
- The model therefore agrees with the tracer case by case on success versus failure (by reading; the Lean side was not run).
  The messages differ in one case: the model reports "Illegal Memory Access" for a load at or above `heap_end`, where the tracer panics earlier in `memory.rs:36`. Both are failures.
- A wrapping range fails on its first access in the model as well, because that access is at or above `heap_end`.
- Loads below the lowest address succeed in the model as in the tracer.
  The whole-run layer already excludes them: `NoLowLoad` (`JoltConstraints/WholeRun/Io.lean:84`) and `NoZeroDoublewordLoad` (`Io.lean:97`), derived from `JoltInstance.TracerAddressChecks` (`JoltConstraints/Soundness/Layer5/MemoryAccessRestriction.lean:89`), which quantifies over every `LD`/`SD` and floor row of the bytecode, expanded inline rows included.
  `docs/riscv-alignment.md:85-100` records the open item for address 0.
- Related lemmas: `load_doubleword_zero` (`JoltConstraints/execution_facts.lean:881`), `store_doubleword_zero` (894), `execInstr_load_zero` (907), `execInstr_store_nonzero` (940).

### What this fixes for `Pre c`

For each operand buffer `[base, base + 8·len)` of the call (from the table above):

1. `base` is a multiple of 8.
2. Every load address passes the tracer's read check: below `heap_end` in RAM (the stack canary is allowed), or in the input, advice, output, panic or termination regions.
3. Every store address passes the tracer's write check: below `heap_end` in RAM and outside the stack canary, or in the output, panic or termination words.
4. No range wraps. Conditions 2 and 3 imply this, because every range starts at a nonnegative offset 0 and is at most 200 bytes long.
5. For completeness of the whole proof, no load address is below the lowest address. Jolt's tracer accepts such loads, and the whole-run layer's `TracerAddressChecks` and `NoLowLoad` already demand this; `Pre c` need not repeat it.

Address 0 needs no special case for the twelve: a base of 0 makes the row at offset 8 fail (a load at 8 is rejected by the prover and is unsatisfiable; a store at 8 panics in the tracer).
Condition 2 or 3 excludes such a base already.

Conditions 2 and 3 admit the I/O regions.
If `Pre c` keeps the narrower "buffers inside RAM" of section 5.4, it remains sufficient but no longer covers a guest that hashes directly into the output region.
A buffer that is written and covers the panic or termination word cannot satisfy a functional `InlineSpec` in the usual form: the model reads the panic word as the flag and the termination word as 0 whatever was stored (`JoltBytecode/JoltISA/JoltDevice.lean:203-206`), and the post-state therefore does not hold the computed words there.
The hash `InlineSpec` therefore needs either a precondition that the written buffer avoids those two words, or a statement through the device's read function.

## Q7. `trace_file`

- `register_inlines!` (doc from `jolt-inlines/sdk/src/host.rs:572`, macro at 585) takes a `trace_file` argument and uses it only in the generated `store_inlines` function (`host.rs:591-601`).
- `store_inlines` calls `store_trace` (`host.rs:292-308`), which calls `write_inline_trace` (`host.rs:307`; defined at `tracer/src/utils/inline_sequence_writer.rs:106`).
- `git grep -n store_inlines` at the pin finds only the doc line 572 and the definition at 591. Nothing calls it.
- `trace_file` appears only in the `register_inlines!` invocations of the inline crates (for example `jolt-inlines/sha2/src/host.rs:4`, `jolt-inlines/secp256k1/src/host.rs:7`) and in the macro. `crates/jolt-host/src/program.rs:453` has an unrelated `trace_to_file` parameter.
- `specs/inline-expansion-grammar.md:406-409` ("Trace File Policy") says that the `.joltinline` files are developer fixtures and "not the source of truth for static expansion". `.gitignore:50` ignores `*.joltinline`.

`trace_file` does not affect proving.

## I0(f). SDK call sites against `Pre c`

### What was checked

For each call site: register aliasing (which registers carry which pointers), 8-byte alignment, the footprint in readable or writable memory, no wrap, advice word counts, BLAKE2's `is_final ∈ {0, 1}`, and for secp256k1 canonical inputs and a nonzero divisor.

Facts common to all call sites:

- Every buffer is a Rust array or struct field of `u64` or `u32` words inside an 8-aligned type, allocated on the stack or heap. It therefore lies in RAM below `heap_end` and outside the canary (the tracer panics on a stack overflow into the canary before the inline runs).
- Every footprint is at most 200 bytes from an address inside a live Rust object, and no range wraps.
- Register operands use `in(reg)`. Rust's RISC-V `reg` class never allocates `x0`, and the secp256k1 call sites therefore always pass a real `rd` (Rust's rule; not run). The hash call sites write `x0` literally in the `.insn` template.
- Advice counts: the tracer asserts that each inline consumes exactly the advice it was given (`tracer/src/instruction/inline.rs:347` and `357`). `QuotientAdvice` serializes 4 words, `ModularDivisionAdvice` 8 and `GlvDecompositionAdvice` 6 (`jolt-inlines/sdk/src/host.rs:210-245`), matching the `VirtualAdvice` rows counted in the alias runs (4, 4, 8, 4, 4, 8, 6).

### Call sites

| # | Inline | Call site | Operands | Verdict |
|---|---|---|---|---|
| 1 | `SHA256` | `jolt-inlines/sha2/src/sdk.rs:186-189` (`finalize`) via `sha256_compression` (asm 264-275, `.insn` 267) | rs1 = `self.state` (`[u32; 8]` at offset 0 of the `#[repr(C, align(8))]` struct, line 3, 11), rs2 = `self.buffer` (line 23, offset 32) | Satisfies `Pre`. `update` (48-120) always copies input into `self.buffer` first |
| 2 | `SHA256` | `sha2/src/sdk.rs:234` (`sha256_compress`, 226-240) | same | Satisfies `Pre` |
| 3 | `SHA256_INIT` | `sha2/src/sdk.rs:228` via `sha256_compression_initial` (asm 322-333, `.insn` 325) | same | Satisfies `Pre`. Both functions are `pub(crate) unsafe`; their safety docs (258, 316) require 8-byte alignment |
| 4 | `KECCAK256_ABSORB_PERMUTE` | `keccak256/src/sdk.rs:88` (`absorb_buffer`) | rs1 = `self.state` (`[u64; 25]`), rs2 = `self.buffer` | Satisfies `Pre` |
| 5 | `KECCAK256_ABSORB_PERMUTE` | `keccak256/src/sdk.rs:128` (`absorb_full_blocks`) | rs2 = the caller's input slice, passed directly when it is 8-aligned | Satisfies `Pre`: the code checks 8-byte alignment of the input (124) before passing the pointer |
| 6 | `KECCAK256_ABSORB_PERMUTE` | `keccak256/src/sdk.rs:141` | rs2 = an aligned local copy of an unaligned block | Satisfies `Pre` |
| 7 | `KECCAK256_ABSORB_PERMUTE` | `keccak256/src/sdk.rs:159` (`absorb_final`) | rs2 = the padded final block | Satisfies `Pre` |
| 8 | `BLAKE2` | `blake2/src/sdk.rs:48` (`CompressionBlock::compress`, 43-50); callers at 240, 251 (`false`) and 265 (`true`) | rs1 = `h` (`[u64; 8]`), rs2 = the `#[repr(C)]` block (22-30, size assert at 53) with `t` and `final_flag = u64::from(is_final)` (44) | Satisfies `Pre`; `is_final ∈ {0, 1}` because it comes from a `bool` |
| 9 | `BLAKE2` | `blake2/src/sdk.rs:312` (`pub fn Blake2b::compress(h, m, t, last: bool)`, 305-313, flag `last as u64` at 309) | same layout | Satisfies `Pre`; public but safe |
| 10 | `MULQ` | `secp256k1/src/sdk.rs:173` (`Secp256k1Fq::mul`, 168-187) | rd/rs3 = fresh local `e`, rs1 = `self.e`, rs2 = `other.e` | Satisfies `Pre` when `self` and `other` are canonical; spoils on non-canonical output (184) |
| 11 | `SQUAREQ` | `secp256k1/src/sdk.rs:216` (`square`, 211-229) | rd = fresh local, rs1 = `self.e` | Same; spoil at 226 |
| 12 | `DIVQ` | `secp256k1/src/sdk.rs:257` (private `div_assume_nonzero`, 252-271) | rd = fresh local, rs1 = `self.e`, rs2 = `other.e` | Satisfies `Pre` when the caller guarantees `other ≠ 0`; spoil at 268 |
| 13 | `DIVQ` via `div` | `secp256k1/src/sdk.rs:280-285` | as 12 | `div` spoils when `other` is zero (282) and then calls 12 |
| 14 | `DIVQ` via `ECField::div_assume_nonzero` | `secp256k1/src/sdk.rs:364-366` (in `impl ECField for Secp256k1Fq`, 321-379) | as 12 | Public bypass: no zero check (see below) |
| 15 | `MULR` | `secp256k1/src/sdk.rs:489` (`Secp256k1Fr::mul`, 484-503) | as 10 | As 10; spoil at 500 |
| 16 | `SQUARER` | `secp256k1/src/sdk.rs:532` (`square`, 527-545) | as 11 | As 11; spoil at 542 |
| 17 | `DIVR` | `secp256k1/src/sdk.rs:573` (private `div_assume_nonzero`, 568-587) | as 12 | As 12; spoil at 584 |
| 18 | `DIVR` via `div` | `secp256k1/src/sdk.rs:596-601` | as 17 | `div` spoils when `other` is zero (598) |
| 19 | `DIVR` in `ecdsa_verify` | `secp256k1/src/sdk.rs:899-900` (`ecdsa_verify`, 866-920) | `z / s`, `r / s` | Satisfies `Pre`: `ecdsa_verify` checks canonicity of z, r, s and Q, Q on the curve and not at infinity, and r, s, z nonzero (872-898) before dividing |
| 20 | `GLVR_ADV` | `secp256k1/src/sdk.rs:756` (`decompose_scalar_impl`, 751-789; called from `glv_decompose`, 640) | rd = fresh local `out: [u64; 6]`, rs1 = `k.e`, rs2 = `x0` | Satisfies `Pre`; sign checks at 765-766 and the recombination check at 781-784 |

The curve code in `jolt-inlines/sdk/src/ec.rs` reaches the field inlines through the `ECField` trait: `double` (165-179) divides only when `y ≠ 0`, `add` (182-200) divides only when the x-coordinates differ, and `double_and_add` (204-232) checks its divisor at 224.
`examples/secp256k1-ecdsa-verify/guest/src/lib.rs` uses only the checked constructors.

Out of scope and not counted: the `0x5B` `REV8W` at `sha2/src/sdk.rs:373`, the `0x7B` field inlines in `crates/jolt-algebra/src/field_inline.rs`, and the `0x5B` instructions in `jolt-sdk/src/lib.rs:581-646`.
`KECCAK256` (plain permutation) has no SDK call site; only `jolt-inlines/keccak256/tests/differential_fuzz.rs:61` uses it.

### Bypasses

- `ECField::from_u64_arr_unchecked` (trait `jolt-inlines/sdk/src/ec.rs:27`, doc at 19-26) and `ECField::div_assume_nonzero` (`ec.rs:16`) are public, and `impl ECField for Secp256k1Fq` forwards them to the `pub(crate)` inherent functions (`secp256k1/src/sdk.rs:364-366` and `376-378`).
  `ec` is a public module behind the `elliptic-curve` feature (`jolt-inlines/sdk/src/lib.rs:22-23`).
  A guest can therefore build a non-canonical `Secp256k1Fq` and pass it to `MULQ`, `SQUAREQ` or `DIVQ`, or divide by zero without the spoil check.
  The edge runs below show the effect: non-canonical inputs can make the advice panic (`host.rs:73`), and a zero divisor makes it panic (`sequence_builder.rs:152`).
- `AffinePoint::new_unchecked` (`ec.rs:78`) and `AffinePoint::from_u64_arr_unchecked` (`ec.rs:145`) are public and build points from unchecked coordinates.
- `pub unsafe fn keccak256_absorb_permute` (`keccak256/src/sdk.rs:171`; safety contract at 167-170: aligned pointers, no overlap) is public.
  Its contract asks for no overlap, which the runs show the inline does not need.
- `Secp256k1Fr` has no `ECField` impl, and its unchecked constructor (`sdk.rs:422`) and `div_assume_nonzero` are `pub(crate)` and private.
- `Blake2b::compress` is public but takes `last: bool` and cannot pass another flag value.

### Aliasing runs

`./inline-probe-inlines alias` runs each inline once with disjoint buffers and then with overlapping buffers holding the same input words, and compares the output words.

```
SHA256: disjoint buffers ok, 1904 rows, 0 VirtualAdvice rows
  rs2 = rs1          rs1=0x80000600 rs2=0x80000600 rs3=0x80000d00: outputs equal
  rs2 = rs1 + 8      rs1=0x80000600 rs2=0x80000608 rs3=0x80000d00: outputs equal
KECCAK256_ABSORB_PERMUTE: disjoint buffers ok, 3125 rows, 0 VirtualAdvice rows
  rs2 = rs1          ...: outputs equal
  rs2 = rs1 + 8      ...: outputs equal
MULQ: disjoint buffers ok, 191 rows, 4 VirtualAdvice rows
  rs2 = rs1          rs1=0x80000600 rs2=0x80000600 rs3=0x80000d00: outputs equal
  rs2 = rs1 + 8      rs1=0x80000600 rs2=0x80000608 rs3=0x80000d00: outputs equal
  rs3 = rs1          rs1=0x80000600 rs2=0x80000900 rs3=0x80000600: outputs equal
  rs3 = rs1 + 8      rs1=0x80000600 rs2=0x80000900 rs3=0x80000608: outputs equal
  rs3 = rs1 - 16     rs1=0x80000600 rs2=0x80000900 rs3=0x800005f0: outputs equal
  rs3 = rs2          rs1=0x80000500 rs2=0x80000600 rs3=0x80000600: outputs equal
  rs1 = rs2 = rs3    rs1=0x80000600 rs2=0x80000600 rs3=0x80000600: outputs equal
GLVR_ADV: disjoint buffers ok, 17 rows, 6 VirtualAdvice rows
  rs3 = rs1          rs1=0x80000600 rs2=0x80000900 rs3=0x80000600: outputs equal
  rs3 = rs1 + 8      rs1=0x80000600 rs2=0x80000900 rs3=0x80000608: outputs equal
  rs3 = rs1 - 16     rs1=0x80000600 rs2=0x80000900 rs3=0x800005f0: outputs equal
```

Every applicable shape gave "outputs equal" for all twelve inlines (full output in `~/claude-work/i0cf-scratch/out/alias.txt`): `SHA256_INIT` and `BLAKE2` behave as `SHA256`; `DIVQ`, `MULR` and `DIVR` as `MULQ`; `SQUAREQ` and `SQUARER` for the three `rs3` shapes.
`KECCAK256` has only one buffer and no shape to alias.
Row counts with the setup rows: `SHA256_INIT` 1,868, `KECCAK256` 3,090, `BLAKE2` 1,071, `SQUAREQ` 171, `DIVQ` 199, `MULR` 237, `SQUARER` 217, `DIVR` 245.

`GLVR_ADV`'s rows never load `rs1`; only its advice reads `k`, and `trace_sequence` runs `build_advice` once before any row (`tracer/src/instruction/inline.rs:320-367`, advice failure panic at 332).
`./inline-probe-inlines glv` confirms that this holds when the output overwrites `k`:

```
k = [a95514aaa, a00aaafdf80202bf, 8b13399cd1d1497a, 141dc47f2feffab4]
  disjoint rs3: Ok([0, 91c5c8f7ed64537a, 39cb5fda3596685f, 0, b093ee27c2e45050, 7d8d9a2bdfc733ce])
  rs3 = rs1      out = Ok([0, 91c5c8f7ed64537a, 39cb5fda3596685f, 0, b093ee27c2e45050, 7d8d9a2bdfc733ce]): equal to disjoint run
  rs3 = rs1 + 8  out = Ok([0, 91c5c8f7ed64537a, 39cb5fda3596685f, 0, b093ee27c2e45050, 7d8d9a2bdfc733ce]): equal to disjoint run
  rs3 = rs1 - 16 out = Ok([0, 91c5c8f7ed64537a, 39cb5fda3596685f, 0, b093ee27c2e45050, 7d8d9a2bdfc733ce]): equal to disjoint run
  rs3 = rs1 + 24 out = Ok([0, 91c5c8f7ed64537a, 39cb5fda3596685f, 0, b093ee27c2e45050, 7d8d9a2bdfc733ce]): equal to disjoint run
  after rs3 = rs1 run, memory at rs1 = [0, 91c5c8f7ed64537a, 39cb5fda3596685f, 0] (k was [a95514aaa, a00aaafdf80202bf, 8b13399cd1d1497a, 141dc47f2feffab4])
```

Two more random scalars give the same picture (`~/claude-work/i0cf-scratch/out/glv.txt`).

### Value-range runs

`./inline-probe-inlines edge`:

```
MULQ a = b = 2^256 - 1 (non-canonical)              : panic at jolt-inlines/sdk/src/host.rs:73: Result does not fit in 4 limbs
MULQ a = p, b = 1 (a = p, non-canonical)            : ok (191 rows), out = [0, 0, 0, 0]
SQUAREQ a = 2^256 - 1                               : panic at jolt-inlines/sdk/src/host.rs:73: Result does not fit in 4 limbs
DIVQ a = 1, b = 0                                   : panic at jolt-inlines/secp256k1/src/sequence_builder.rs:152: Attempted to invert zero in secp256k1 base field
DIVQ a = 0, b = 0                                   : panic at jolt-inlines/secp256k1/src/sequence_builder.rs:152: Attempted to invert zero in secp256k1 base field
DIVQ a = 1, b = p (b = 0 mod p, non-canonical)      : panic at jolt-inlines/secp256k1/src/sequence_builder.rs:152: Attempted to invert zero in secp256k1 base field
DIVR a = 1, b = 0                                   : panic at jolt-inlines/secp256k1/src/sequence_builder.rs:146: Attempted to invert zero in secp256k1 scalar field
GLVR_ADV k = 2^256 - 1 (k >= n)                     : ok (17 rows), out = [0, e86c90e59284eee6, 3086d221a7d46bcd, 1, e86c90e49284eb15, 3086d221a7d46bcd]
BLAKE2 is_final = 0x0: ok (1071 rows), h[0] = 0x5fc731331f7d47db
BLAKE2 is_final = 0x1: ok (1071 rows), h[0] = 0xffb0dff157963c3c
BLAKE2 is_final = 0x2: ok (1071 rows), h[0] = 0xd6d54695f51a7d8b
BLAKE2 is_final = 0xffffffffffffffff: ok (1071 rows), h[0] = 0xecdecdd4ac2785ed
```

- `mulq_quotient_advice` (`jolt-inlines/sdk/src/host.rs:98-117`) computes `w = ⌊a·b/m⌋` and `nbiguint_to_field_limbs` asserts that it fits in four limbs (`host.rs:73`). Jolt's advice therefore needs `a·b < 2^256·q`, not canonical inputs.
- `mulq_division_advice` (`host.rs:130-148`) calls `field_inv_mul`, which panics on a divisor that is zero modulo the field (`secp256k1/src/sequence_builder.rs:146` scalar field, `152` base field). `b = p` is nonzero as an integer and still panics.
- `GlvrAdvBuilder::advice` (`secp256k1/src/sequence_builder.rs:25-35`) reads `k` through `load_field_element_limbs` (`host.rs:57-69`) and reduces it with `Fr::new`. Every 256-bit `k` therefore works, and the output is the decomposition of `k mod n`.
- BLAKE2's rows compute `v14 = IV6 ^ (0 − is_final)` (`jolt-inlines/blake2/src/sequence_builder.rs:74-79`, `109-119`). The rows are total on every flag value, and only 0 and 1 give BLAKE2.

## Contradictions with the spec

All line numbers are in `docs/inline-precompiles.md` at `309ba77`.

1. Line 407: "`Pre` collects the caller's obligations: alignment, buffers inside RAM, overlap rules, and value ranges (`is_final ∈ {0, 1}` for `BLAKE2`, inputs below the modulus for secp256k1, a nonzero divisor for DIV)."
   - "overlap rules": none of the twelve needs one. Every load precedes every store, the advice reads its inputs before any row, and every aliasing shape gave the same output as disjoint buffers.
   - "buffers inside RAM": Jolt proves calls whose buffers read from the input, advice, output, panic or termination regions or write to the output, panic or termination words. Keeping "inside RAM" is sufficient for the SDK, but it is a choice and not what Jolt requires. A written buffer that covers the panic or termination word needs separate treatment in `InlineSpec` (section Q3 above).
   - "inputs below the modulus for secp256k1": the soundness relations (`a·b = w·q + c`, `c·b = w·q + a`) hold for every input that gets through the asserts. Jolt's advice needs only `⌊a·b/q⌋ < 2^256` for MUL and SQUARE. Canonical inputs are sufficient, not necessary.
   - "a nonzero divisor for DIV": the divisor must be nonzero modulo `q`. `b = p` is nonzero and makes the advice panic. With canonical inputs the two conditions agree; if `Pre` drops canonicity it must say "nonzero modulo q".
2. Line 466: "`mulq_division_advice` (result and quotient interleaved; it panics when `b = 0`, which `Pre c` excludes)". It panics whenever `b ≡ 0 (mod q)`, which includes `b = q` (run above).
3. Line 140: "the SDK spoils the proof on one (`secp256k1/src/sdk.rs:280-284`)". The citation is `Secp256k1Fq::div` (280-285, spoil at 282). It is correct for `div`, but the ECDSA path calls `div_assume_nonzero` directly (`sdk.rs:899-900`, guarded by the `s ≠ 0` check at 893-895), and `ECField::div_assume_nonzero` is public with no check. Section 12.3 (line 704) already describes the per-call-site argument; line 140 reads as if the spoil covers every division.
4. Line 144: "The guest checks the sign words and `k1 + λ·k2 = k` afterwards (`secp256k1/src/sdk.rs:751`)". Line 751 is the start of `decompose_scalar_impl`; the sign checks are at 765-766 and the recombination check at 781-784. This is imprecise, not wrong.
5. Line 630: "unsatisfiable, a trap, or something else". The answer differs by place: the tracer panics (no trace); the constraints are unsatisfiable; jolt-qed's model returns `Memory_Exception` for misalignment (a trap result) and an assertion error for an out-of-range address. Both Lean outcomes mean the rows do not run to the end, and they agree with Jolt on success versus failure.

The following spec statements were checked and hold: line 120 (SHA-256 buffers), 122 (`is_final ∈ {0, 1}` needed for meaning), 147 (the SDK always passes a real `rd`), 223-235 (registration check; "the registry lookup in the tracer and in preprocessing"), the step-1 citations of section 2.2 (`decode.rs:85`, `inline.rs:113-121`), 457-458 (a buffer over the I/O window can set the panic flag; confirmed by the `SHA256` `panic − 24` run), 467 (`host.rs:233-242`), the L-numbers of the table at 675-677, and the risk table at 703-705.

## What this changes for I1a and I2

### I1a (hash inlines)

- Registration: the Lean registration check models the set of keys linked into the preprocessing binary. An unregistered key makes Jolt's preprocessing panic, and the Lean check that rejects it matches Jolt (no proof exists for such a guest).
- (a) The frame lemma needs no `Pre`, as section 5.4 already says. The hash soundness theorems need less than section 5.4 lists:
  - If the rows run to the end, every access was aligned and in range in the model. Alignment and range therefore need not appear in `Pre` for soundness.
  - No overlap rule is needed: state `InlineSpec` with the words the rows load at the start, which equal the memory contents before the call because every load precedes every store.
  - The written buffer must avoid the panic and termination words, or `InlineSpec` must be stated through the device read function, because the model does not read back stored words there.
  - `BLAKE2` needs `is_final ∈ {0, 1}` only to call the result BLAKE2's F.
  For completeness, `Pre` needs conditions 1-3 of the Q3 section (aligned, every load readable, every store writable); the below-lowest load case is handled by `TracerAddressChecks` and `NoLowLoad` at the whole-run level.
- The I1a acceptance test (preprocessing `KECCAK256_ABSORB_PERMUTE` in the model) is unaffected.

### I2 (secp256k1)

- (b) `MulRel` and `DivRel` (soundness) need no canonical inputs and no nonzero divisor: they hold for every advice that passes the asserts.
  Completeness with Jolt's advice (`rows_jolt_advice_complete`) needs `⌊a·b/q⌋ < 2^256` for MUL and SQUARE, and `b mod q ≠ 0` for DIV; canonical inputs give the first, and with canonical inputs the second is `b ≠ 0`.
  `Canonical` for `GLVR_ADV` takes `k mod n` as its input: the transcription of `GlvrAdvBuilder::advice` must reduce the 256-bit `k` first, and `Pre` needs no range on `k`.
  The transcribed advice word counts are 4 (MUL, SQUARE), 8 (DIV, interleaved) and 6 (GLV), and the tracer rejects any other count.
- No `Pre` for secp256k1 needs an overlap condition: the advice reads `a`, `b` and `k` before any row, the rows load before they store, and `rs3` may equal `rs1` or `rs2`.

### Expansion-parity tests

- (c) Every one of the twelve has nonnegative offsets that are multiples of 8, its base in an operand register, and all loads before all stores. Neither property is checked by the driver today; adding both checks to `scripts/expansion-parity` would turn the "no overlap rule" and "address 0 is not special" conclusions into checked facts for future Jolt revisions.
  Jolt's own `InlineMemoryOffsetOutOfRange` check already bounds offsets to [−2048, 2047] at expansion.
  (Two inlines outside the twelve break the load-before-store order or the operand-base rule: `NTT64_I32_POINTWISE_DOT6` interleaves loads and stores, and both NTT inlines load through bases held in virtual registers.)

## Follow-ups outside this task

- `JoltBytecode/JoltISA/DeviceMemory.lean` cites `mmu.rs` line numbers from an older Jolt (for example 120-184, 329-337, 437-443, 619-635, 729-748). At the pin they are 112-178 (`assert_effective_address`), 319-327 (`load_doubleword`), 427-433 (`store_doubleword`), 565-584 (`load_doubleword_raw`) and 675-694 (`store_doubleword_raw`).
- The SDK's `keccak256_absorb_permute` safety contract asks for no overlap (`keccak256/src/sdk.rs:167-170`), which the inline does not need. This is a note for Jolt, not a defect.
- The latest expansion-parity output (`~/claude-work/expansion-parity-work/out/summary.json`) reports `all_pass: false`. This report uses only its `inline_templates.json`.
