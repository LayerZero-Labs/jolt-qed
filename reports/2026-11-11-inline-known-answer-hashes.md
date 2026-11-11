# Known-answer tests for Jolt's hash inlines

Date: 2026-11-11.
Jolt commit checked: `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5` (`a6b6dc71`).
EthLib commit of the copied specifications: `5310b3ec007b05a2bfe33b01125392b07df5f636` (`5310b3e`).
This report covers phase I0(b) of `docs/inline-precompiles.md` for the five hash inlines: `SHA256`, `SHA256_INIT`, `KECCAK256`, `KECCAK256_ABSORB_PERMUTE` and `BLAKE2`.

## Result

Jolt's tracer agrees with the copied EthLib specifications on every judged case: 354 of 354 pass, with no mismatch.
The 354 cases are 72 for `SHA256`, 70 for `SHA256_INIT`, 70 for `KECCAK256`, 68 for `KECCAK256_ABSORB_PERMUTE` and 74 for `BLAKE2`.
Every case that has a published answer (FIPS 180-4, Keccak-256, `KeccakKAT-3`, RFC 7693 and EIP-152 vectors, and Jolt's own constants) matches it.
Two further `BLAKE2` cases, with final-block flags 2 and `2^64 - 1`, are informational: the specification does not cover them, and the tracer computes the compression with `0 - flag` XORed into word 14 of the work vector.
`lake build JoltTests.InlineKat.Vectors` succeeds, so the specifications alone also give the published answers.
The report found two places where `docs/inline-precompiles.md` is incomplete or inaccurate; the last section lists them.

## What was run

`scripts/inline-kat/` is a Rust crate built against a Jolt checkout, in the way `scripts/difftest/jolt-trace` is.
For each case it writes the bytes at `rs1` and `rs2`, runs the `INLINE` instruction through `INLINE::trace` in Jolt's tracer, and records the bytes before and after.
`INLINE::trace` expands the instruction with `inline_sequence`, which calls the registered sequence builder through `jolt_program::expand::expand_instruction_with_provider` (`tracer/src/instruction/inline.rs:299-318`, `tracer/src/emulator/cpu.rs:636-653`).
So the driver runs the same expansion the prover's bytecode uses, not a reimplementation.
The driver checks that each key is registered under its expected name with `tracer::list_registered_inlines` before it runs any case.
It never computes a hash itself.

`lake exe inline-kat CASES.json` reads the recorded cases and evaluates the copied specifications in `JoltBytecode/Inlines` on the bytes before.
A judged case passes when four checks hold:

- the bytes the tracer left at `rs1` equal the specification's result;
- the bytes at `rs2` did not change;
- the bytes at `rs1` start with the published answer, when the case has one;
- the registers `x1` to `x31` did not change.

`JoltTests/InlineKat/Layout.lean` documents and implements the conversion between memory and the specifications' arguments.
`JoltTests/InlineKat/Vectors.lean` checks the specifications alone, without Jolt, on published vectors.

## How to rerun

From the repository root:

```sh
JOLT_DIR=/path/to/a16z/jolt scripts/inline-kat/build.sh WORK_DIR
scripts/inline-kat/run.sh WORK_DIR WORK_DIR/cases.json
lake build JoltTests.InlineKat.Vectors
lake exe inline-kat WORK_DIR/cases.json
```

`build.sh` copies Jolt's `Cargo.lock` and `rust-toolchain.toml` into `WORK_DIR/inline-kat` and builds there, so it never writes into the Jolt checkout.
`run.sh` passes the checkout's commit to the driver, which records it in the JSON.
The random cases come from a fixed splitmix64 seed per inline, so every run produces the same JSON.
This run used `WORK_DIR = ~/claude-work/inline-kat-work`, and its JSON (356 cases, 428 KB) is not committed.

## The vectors

Every inline gets 64 seeded random cases, plus these.

- `SHA256` and `SHA256_INIT`:
  - FIPS 180-4 `SHA-256("abc")` and `SHA-256("")`, one padded block from the IV.
  - Block 1 of the two-block FIPS 180-4 message `"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"`.
  - For `SHA256` only, block 2 of that message, once from the state `SHA256` left after block 1 and once from the state `SHA256_INIT` left, each checked against the final digest `248d6a61...`.
  - Jolt's three compression vectors from `jolt-inlines/sha2/src/test_constants.rs` (zero block, the NIST byte pattern, all-ones block, each from the IV).
  - `SHA256_INIT` gets a filler pattern at `rs1` instead of the IV, which shows that it does not read the state.
- `KECCAK256`:
  - The Keccak team's `KeccakKAT-3` permutations of the zero state and of its result, as EthLib records them in `tests/cryptography/keccak/permutation`.
  - The padded one-block messages of Keccak-256 `""` and `"abc"`, XORed into the zero state, checked against the digests `c5d24601...` and `4e03657a...`.
  - Jolt's simple pattern (lane `i` is `3i + 5`) and the all-ones state.
  - A filler pattern at `rs2`, which the inline does not read.
- `KECCAK256_ABSORB_PERMUTE`:
  - Jolt's two edge cases (zero state with zero block, all-ones state with all-ones block); the first is checked against `KeccakKAT-3`.
  - The padded blocks of Keccak-256 `""` and `"abc"` absorbed into the zero state, checked against the digests.
- `BLAKE2`:
  - Jolt's three cases from `jolt-inlines/blake2/src/spec.rs`: BLAKE2b-512 of the empty message, of `"abc"` (which is RFC 7693 appendix A and EIP-152 vector 5), and all-ones `h` and `m` with counter 128, not final.
  - EIP-152 vector 6 (the `"abc"` block, not final).
  - Counters above `2^32`: `2^32 + 5`, `2^63` and `2^64 - 1`, each with flag 0 and flag 1. EIP-152 has no such counter.
  - The 64 random cases alternate flags 0 and 1.
  - Two informational cases with flags 2 and `2^64 - 1`, which the specification does not cover.

`Vectors.lean` checks, by `#guard`:

- SHA-256 digests of `"abc"`, `""` and the two-block message, and the derivation of `IV` and `K` from the primes (EthLib's `IV_from_primes` and `K_from_primes`).
- Keccak-256 digests of `""` and `"abc"`, Keccak-f[1600] of the zero state and of its result, and the derivation of `RC` and `RHO` (EthLib's `roundConstants_eq` and `rhoOffsets_eq`).
- The three constant facts behind EthLib's proof that the lane code equals the bit model (`rhoOffset_eq`, `rhoOffset_lt`, `roundConstantBit_eq`) on all their inputs, and the equation `toLanes (permutation (ofLanes S)) = keccakF S` itself on five sample states.
- BLAKE2b `Spec.compress` on EIP-152 vectors 4 to 7 (0, 12 and 1 rounds) and on BLAKE2b-512 of the empty message, and the checks of EthLib's `IV_sqrt` and `SIGMA_perm`.

The bit model builds each state as a chain of closures, so evaluating it directly takes exponential time.
`Vectors.lean` evaluates it through tables instead, and proves that each table version equals the model (`permutationTab_eq`, `roundConstantBitTab_eq`).
So the `#guard` checks there are statements about the model itself.

## Per-inline results

`lake exe inline-kat` printed this summary for the JSON recorded at Jolt `a6b6dc71`:

```text
SHA256: 72 passed, 0 failed, 0 informational; rows per call [1900] (expansion length 1900)
SHA256_INIT: 70 passed, 0 failed, 0 informational; rows per call [1864] (expansion length 1864)
KECCAK256: 70 passed, 0 failed, 0 informational; rows per call [3087] (expansion length 3087)
KECCAK256_ABSORB_PERMUTE: 68 passed, 0 failed, 0 informational; rows per call [3121] (expansion length 3121)
BLAKE2: 74 passed, 0 failed, 2 informational; rows per call [1067] (expansion length 1067)
```

- No case failed, so there is no first differing word to report.
- Every case ran exactly as many rows as the registered expansion has, and those counts are the ones section 3 of `docs/inline-precompiles.md` gives.
- No case changed the bytes at `rs2` or any of the registers `x1` to `x31`.
- For the two informational `BLAKE2` cases the tracer's result differs from `Spec.compress` with `f = true` and with `f = false`, and equals the compression with word 14 XORed by `0 - flag`.
  That is what the builder's `SUB` and `XOR` compute, and it is outside the specification, which takes a Boolean flag.
- To check that a mismatch is caught, I flipped one bit of a recorded `KECCAK256` output: the program printed `FAIL ... word 2: tracer 0x400fec990f4afc14, spec 0x400fec990f4afd14` and exited with status 1.

`lake exe inline-kat` takes about 25 seconds of CPU on the 356 cases, most of it in the SHA-256 message schedule, which the specification computes by unmemoized recursion.
`lake build JoltTests.InlineKat.Vectors` takes about 30 seconds, including five Keccak-f evaluations of the bit model through tables.
`JoltBytecode/Inlines/Blake2b/Spec.lean` takes 157 to 190 seconds to build, most of it in EthLib's bijectivity proofs.

## What the copies leave out

The copies keep every definition the five specifications need, unchanged; `scripts/check-ethlib-copies.sh` checks 143 declarations against EthLib `5310b3e`.
They leave out these EthLib proofs, which use `decide` with the `+kernel` option, which jolt-qed's checking standard forbids:

- SHA-256: `IV_from_primes` and `K_from_primes`.
- Keccak: `roundConstants_eq` and `rhoOffsets_eq`, and `rhoOffset_eq`, `rhoOffset_lt` and `roundConstantBit_eq`, on which EthLib's proof `toLanes_permutation` (the lane code equals the bit model) rests. So `toLanes_permutation` and its step lemmas are left out too.
- BLAKE2b: `IV_sqrt` and `SIGMA_perm`.

`Vectors.lean` evaluates every one of these statements with `#guard` instead, and checks `toLanes_permutation` on five sample states.

They also leave out what the inline specifications do not need:

- SHA-256: EthLib's executable `UInt32` code and its proofs (`compress_toState`, `hash_eq_spec`), since the specification is the model `Spec.compression` itself.
- Keccak: the padding lemmas and `keccakF_bijective`, whose lane lemmas use Mathlib's `fin_cases`.

## Layout and byte order

Jolt's test harness puts the input read through `rs2` at `DRAM_BASE` and the state read and written through `rs1` right after it (`tracer/src/utils/inline_test_harness.rs:31-43`).
It passes the two addresses in `x10` and `x11` (`tracer/src/utils/inline_test_harness.rs:61-62, 220-230`).
The driver uses the same layout and writes each region byte by byte.
RISC-V memory is little-endian, so a `u64` the builder loads with `LD` has its least significant byte at the lowest address.

### SHA-256

- `SHA256` loads the state with four `load_paired_u32_dirty` calls at `rs1 + 8i` (`jolt-inlines/sha2/src/sequence_builder.rs:64-73`).
  Each is an `LD` followed by `SRLI 32`, and the low half is word `2i` (`jolt-inlines/sdk/src/host.rs:399-404`).
  So state word `j` (FIPS 180-4 `H_j`) is the little-endian `u32` at `rs1 + 4j`.
- `SHA256_INIT` does not read `rs1` (`jolt-inlines/sha2/src/sequence_builder.rs:64`): its filler cases pass.
- The builder loads the block with `LD` at `rs2 + 8i`, then `VIRTUAL_REV8_W`, then `SRLI 32` (`jolt-inlines/sha2/src/sequence_builder.rs:74-83`).
  So message word `2i` is the big-endian value of bytes `8i` to `8i + 3`, and word `2i + 1` that of bytes `8i + 4` to `8i + 7`.
  In other words, `rs2` holds the 64 message bytes in order, and the specification's `Spec.inputWords rs2 0` reads them correctly.
  Jolt's own test loads the block with `block.map(u32::to_be)` through `store_word` (`jolt-inlines/sha2/src/spec.rs:37`), which gives the same bytes.
- The result goes back through `store_paired_u32` at `rs1 + 8i` (`jolt-inlines/sha2/src/sequence_builder.rs:88-96`, `jolt-inlines/sdk/src/host.rs:387-394`), so it has the layout of the input state.
- The digest bytes are the big-endian words of the final state, so a guest has to byte-swap each `u32` it reads back from `rs1`.

### Keccak

- Both inlines load the 25 lanes with `load_u64_range` at `rs1 + 8i` and store them back the same way (`jolt-inlines/keccak256/src/sequence_builder.rs:103-104, 119-121`, `jolt-inlines/sdk/src/host.rs:335-345`).
  Lane `i = x + 5y` is the little-endian `u64` at `rs1 + 8i`, which is the FIPS 202 state string, as EthLib's `Internal.laneAt` reads it.
- `KECCAK256_ABSORB_PERMUTE` loads 17 lanes (`RATE_IN_U64`) with `LD` at `rs2 + 8i` and XORs them into lanes 0 to 16 (`jolt-inlines/keccak256/src/sequence_builder.rs:105-116`).
  That is EthLib's `Internal.absorbBlock 136 S rs2 0`.
- `KECCAK256` does not read `rs2`: its filler cases pass.

### BLAKE2b

- `h` is eight little-endian `u64` at `rs1` (`jolt-inlines/blake2/src/sequence_builder.rs:56-62`), and the result is stored back there (`jolt-inlines/blake2/src/sequence_builder.rs:171-177`).
- `m` is sixteen little-endian `u64` at `rs2` (`jolt-inlines/blake2/src/sequence_builder.rs:64-70`).
- The counter `t` is one `u64` at `rs2 + 128`, and the final-block flag one `u64` at `rs2 + 136` (`jolt-inlines/blake2/src/sequence_builder.rs:74-79`).
- The builder XORs `t` into `v[12]` and leaves `v[13]` as `IV[5]` (`jolt-inlines/blake2/src/sequence_builder.rs:92-107`).
  Its comment says this is because the counter is 64-bit.
  So the inline computes RFC 7693's F with the high counter word `t1 = 0`, which is `Spec.compress 12 h m t f` with `t < 2^64`.
- The builder computes `v[14] = IV[6] XOR (0 - flag)` (`jolt-inlines/blake2/src/sequence_builder.rs:109-120`).
  For flag 1 that inverts `IV[6]`, and for flag 0 it leaves it alone, which matches the specification's Boolean `f`.

## Against `docs/inline-precompiles.md`

The run confirms the row counts of section 3, the layouts it describes for `SHA256`, `SHA256_INIT` and the two Keccak inlines, and the precondition `is_final ∈ {0, 1}` of sections 3 and 5.4.
It found two places where the plan says less or something other than what holds.

1. The `BLAKE2` counter is 64 bits, but section 5.6 names `Spec.compress` "with a 128-bit counter" as the specification, and section 3 does not mention the width.
   The inline reads one `u64` counter and keeps `v[13] = IV[5]`, so its specification is `Spec.compress 12 h m t f` with `t < 2^64`, that is with `t1 = 0`.
   Only section 12.3 mentions a 64-bit counter, and only for the SDK.
   The I2 statement for `BLAKE2` should take the counter as a `u64` and widen it to 128 bits.
2. Section 5.6 says that the SHA-256 and BLAKE2b proof files use `decide +kernel` "twice each", which suggests that only those two files need it.
   The Keccak proof files use it five times: `roundConstants_eq` and `rhoOffsets_eq` in `Proofs/Hash/Keccak.lean`, and `rhoOffset_eq`, `rhoOffset_lt` and `roundConstantBit_eq` in `Proofs/Hash/KeccakBitsPermutation.lean`.
   The last three carry EthLib's `toLanes_permutation`, which section 5.6 lists among the theorems the Keccak specification comes with.
   So under the strict standard jolt-qed cannot copy `toLanes_permutation` as it is: it has to re-prove the three constant facts without `decide +kernel`, or state the Keccak inlines against the lane code `Keccak.keccakF` and leave the bit model as a test-only cross-check, as this phase does.

One wording in sections 3 and 12.3 can mislead: both say that the inline expects "a big-endian block" through `rs2`.
The bytes at `rs2` are the message bytes in order, which is what the SDK passes; the builder reads them as big-endian words.
A guest does not byte-swap the block, but it does byte-swap the eight state words it reads back from `rs1`.
