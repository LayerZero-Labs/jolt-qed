# Known-answer tests for Jolt's hash inlines

Date: 2026-11-11.
Jolt commit checked: `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5` (`a6b6dc71`).
jolt-qed commit of the checker that produced the results: `71b3b0cb405744de065e8e71c28d89419705269c` (`71b3b0c`).
EthLib commit of the copied specifications: `5310b3ec007b05a2bfe33b01125392b07df5f636` (`5310b3e`).
This report covers phase I0(b) of `docs/inline-precompiles.md` for the five hash inlines: `SHA256`, `SHA256_INIT`, `KECCAK256`, `KECCAK256_ABSORB_PERMUTE` and `BLAKE2`.

## Result

Jolt's tracer agrees with the copied EthLib specifications on every judged case: 354 of 354 pass, with no mismatch.
The 354 cases are 72 for `SHA256`, 70 for `SHA256_INIT`, 70 for `KECCAK256`, 68 for `KECCAK256_ABSORB_PERMUTE` and 74 for `BLAKE2`.
Every case that has a published answer (FIPS 180-4, Keccak-256, `KeccakKAT-3`, RFC 7693 and EIP-152 vectors, and Jolt's own constants) matches it.
The checker also confirmed that the corpus is complete: it comes from the pinned Jolt commit, covers all five inlines with at least the required number of judged cases, and contains all 24 known-answer cases of its manifest with the recorded inputs and answers.
Two further `BLAKE2` cases, with final-block flags 2 and `2^64 - 1`, are informational: the specification does not cover them, and the tracer computes the compression with `0 - flag` XORed into word 14 of the work vector.
`lake build JoltTests.InlineKat.Vectors` succeeds, so the specifications alone also give the published answers.
The copies also carry EthLib's proofs about the constants, and its proof `toLanes_permutation` that the Keccak lane code equals the FIPS 202 bit model.
Nine of these proofs use `decide +kernel`, as in EthLib, and each kernel check takes under two seconds when checked alone.
The report found two places where `docs/inline-precompiles.md` was incomplete or inaccurate; the last section lists them, and commit `91d2680` has corrected the second.

## What was run

`scripts/inline-kat/` is a Rust crate built against a Jolt checkout, in the way `scripts/difftest/jolt-trace` is.
For each case it writes the bytes at `rs1` and `rs2`, runs the `INLINE` instruction through `INLINE::trace` in Jolt's tracer, and records the bytes before and after.
`INLINE::trace` expands the instruction with `inline_sequence`, which calls the registered sequence builder through `jolt_program::expand::expand_instruction_with_provider` (`tracer/src/instruction/inline.rs:299-318`, `tracer/src/emulator/cpu.rs:636-653`).
So the driver runs the same expansion the prover's bytecode uses, not a reimplementation.
The driver checks that each key is registered under its expected name with `tracer::list_registered_inlines` before it runs any case.
It never computes a hash itself.

`lake exe inline-kat [--jolt-commit SHA] CASES.json` reads the recorded cases and evaluates the copied specifications in `JoltBytecode/Inlines` on the bytes before.
A judged case passes when five checks hold:

- the bytes the tracer left at `rs1` equal the specification's result;
- the bytes at `rs2` did not change;
- the bytes at `rs1` start with the published answer, when the case has one;
- the registers `x1` to `x31` did not change;
- the tracer ran as many rows as the inline's expansion has.

The checker decides itself which cases are judged, and ignores the corpus's `judged` field except to fail a case whose field disagrees.
Every case is judged except a `BLAKE2` case whose final-block flag is outside {0, 1}, which it reports as informational.

The checker also fails the corpus as a whole when it is incomplete:

- its `jolt_commit` is not `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5`, or the commit given with `--jolt-commit` (for a run against another Jolt commit, such as one with a16z/jolt#2414);
- its table of inlines is not exactly the five hash inlines;
- an inline has fewer judged cases than the driver produces (72, 70, 70, 68 and 74), or two cases with one name;
- a case of the manifest `JoltTests/InlineKat/Manifest.lean` is missing, has another input, lacks its published answer or records another one, or has a tracer result that does not start with that answer.

The manifest lists the 24 cases with published answers below, with their inputs and answers written down in Lean from the sources, not taken from the corpus or computed by the specifications.

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

`lake exe inline-kat --jolt-commit SHA WORK_DIR/cases.json` accepts a corpus from another Jolt commit.

`build.sh` copies Jolt's `Cargo.lock` and `rust-toolchain.toml` into `WORK_DIR/inline-kat` and builds there, so it never writes into the Jolt checkout.
`run.sh` passes the checkout's commit to the driver, which records it in the JSON.
The random cases come from a fixed splitmix64 seed per inline, so every run produces the same JSON.
This run used `WORK_DIR = ~/claude-work/inline-kat-work`, and its JSON (356 cases, 428 KB) is not committed.

## The vectors

Every inline gets 64 seeded random cases, plus these.

- `SHA256` and `SHA256_INIT`:
  - FIPS 180-4 `SHA-256("abc")` and `SHA-256("")`, one padded block from the IV.
  - Block 1 of the two-block FIPS 180-4 message `"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"`, checked against the intermediate value `H(1) = 85e655d6 ...` of the NIST CSRC example.
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

- SHA-256 digests of `"abc"`, `""` and the two-block message, and that the model's initial state is `IV`.
- Keccak-256 digests of `""` and `"abc"`, and Keccak-f[1600] of the zero state and of its result.
- BLAKE2b `Spec.compress` on EIP-152 vectors 4 to 7 (0, 12 and 1 rounds) and on BLAKE2b-512 of the empty message.

The derivations of the constants and the equation between the Keccak lane code and the bit model are theorems of the copies (see "What the copies contain"), so `Vectors.lean` no longer evaluates them.

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

To check that the corpus checks catch an incomplete or altered corpus, I ran the checker of `71b3b0c` on altered copies of the JSON.
Each altered copy exits with status 1, and the unaltered JSON exits with status 0:

| Altered corpus | What the checker printed |
| --- | --- |
| `{}` | 32 failures: wrong format, commit missing, empty inline table, every known-answer case missing, every inline below its minimum |
| all fields kept, no cases | 29 failures: every known-answer case missing, every inline below its minimum |
| `jolt_commit` set to forty zeros | `the cases come from Jolt commit 0000..., not a6b6dc71...` |
| only the `KECCAK256` cases | 24 failures: the 20 known-answer cases of the other inlines missing, four inlines below their minimum |
| only the `KECCAK256` cases and table entry | 25 failures: as above, and the inline table is incomplete |
| `SHA256` `random 5` marked not judged, one output bit flipped | `the corpus marks the case as not judged, but the specification covers it; rs1 differs from the specification at word 0` |
| `SHA256` `"abc"` case removed | `the known-answer case ... is missing`, and `SHA256 has 71 judged cases, fewer than 72` |
| answer field of EIP-152 vector 6 removed | `the published answer (EIP-152 vector 6) is missing` |
| last byte of the `KECCAK256` `"abc"` input changed | `rs1 is not the known-answer input; rs1 differs from the specification at word 0` |

With `--jolt-commit 0000...` the checker accepts the corpus with the zero commit.

`lake exe inline-kat` takes about 25 seconds of CPU on the 356 cases, most of it in the SHA-256 message schedule, which the specification computes by unmemoized recursion.
`lake build JoltTests.InlineKat.Vectors` takes 4 to 15 seconds, depending on the load.
The specification files check in a few seconds each; "What the copies contain" gives the times before and after the restored proofs.

## What the copies contain

The copies keep every definition the five specifications need, unchanged; `scripts/check-ethlib-copies.sh` checks 173 declarations against EthLib `5310b3e`, and the workflow `.github/workflows/ethlib-copies.yml` runs it on pull requests that touch `JoltBytecode/Inlines` or the script.

They also carry, unchanged, EthLib's proofs about the constants and the bit model.
The script requires each of these to be present:

- SHA-256: `IV_from_primes` and `K_from_primes`, which derive `IV` and `K` from the primes.
- Keccak:
  - `roundConstants_eq` and `rhoOffsets_eq`, which derive `RC` and `RHO` from FIPS 202 Algorithms 5, 6 and 2;
  - all of `Proofs/Hash/KeccakBitsPermutation.lean`: `toLanes_permutation` (the lane code equals the bit model on every state), the step lemmas `theta_ofLanes`, `rho_ofLanes`, `pi_ofLanes`, `chi_ofLanes`, `iota_ofLanes`, `round_ofLanes`, `roundsFrom_ofLanes` and `permutation_ofLanes`, the three constant facts `rhoOffset_eq`, `rhoOffset_lt` and `roundConstantBit_eq`, and the lemmas about `ofLanes` and `toLanes`;
  - five lane lemmas of `Proofs/Hash/KeccakPermutation.lean` that the proof needs: `getLsbD_rotl`, `lane_ext`, `lane_ofLanes`, `ofLanes_lane` and `State.ext_lane`.
  `lane_ofLanes` uses Mathlib's `fin_cases`, so the Keccak copy now imports `Mathlib.Data.Fintype.Basic` and `Mathlib.Tactic.FinCases`.
- BLAKE2b: `IV_sqrt` and `SIGMA_perm`.

`#print axioms` on each of the 28 public restored theorems lists only `propext`, `Classical.choice` and `Quot.sound`, or a subset; `IV_from_primes`, `K_from_primes` and `rhoOffset_lt` depend on no axiom.

### Uses of `decide +kernel`

Nine of the restored proofs use `decide +kernel`, as in EthLib.
`AGENTS.md` allows it when it is efficient: it adds no axiom, and a use whose kernel check takes more than about ten seconds is not allowed.

| Use | Theorem | Alone | In its file | Axioms |
| --- | --- | --- | --- | --- |
| `JoltBytecode/Inlines/Sha256/Spec.lean:235` | `Sha256.IV_from_primes` | 0.01 s | 0.02–0.03 s | none |
| `JoltBytecode/Inlines/Sha256/Spec.lean:248` | `Sha256.K_from_primes` | 0.10 s | 0.23–0.68 s | none |
| `JoltBytecode/Inlines/Keccak256/Spec.lean:599` | `Keccak.roundConstants_eq` | 0.10 s | 0.5–1.6 s | `propext`, `Quot.sound` |
| `JoltBytecode/Inlines/Keccak256/Spec.lean:606` | `Keccak.rhoOffsets_eq` | 0.07 s | 1.1–2.6 s | `propext`, `Quot.sound` |
| `JoltBytecode/Inlines/Keccak256/Spec.lean:875` | `KeccakBits.rhoOffset_eq` | 0.17 s | 1.7–4.1 s | `propext`, `Quot.sound` |
| `JoltBytecode/Inlines/Keccak256/Spec.lean:879` | `KeccakBits.rhoOffset_lt` | 0.04 s | 1.8–4.4 s | none |
| `JoltBytecode/Inlines/Keccak256/Spec.lean:922` | `KeccakBits.roundConstantBit_eq` | 1.44 s | 7.6–20 s | `propext`, `Quot.sound` |
| `JoltBytecode/Inlines/Blake2b/Spec.lean:280` | `Blake2b.IV_sqrt` | 0.02 s | 0.02 s | `propext`, `Quot.sound` |
| `JoltBytecode/Inlines/Blake2b/Spec.lean:287` | `Blake2b.SIGMA_perm` | 0.06 s | 0.19–0.29 s | `propext`, `Classical.choice`, `Quot.sound` |

Both time columns are wall-clock times of elaboration plus the kernel check, from `trace.profiler` ("elaborating proof of ..."), on a 10-core machine whose load average stayed between 17 and 40 throughout.

- "Alone" checks a copy of the theorem, with the same statement and proof, in a file that imports the built specifications. Nearly all of it is the kernel check.
- "In its file" is the range over two or three runs of the whole specification file. There the file's other proofs check in parallel with it, so these times include waiting for a core.
- In CPU time, `roundConstantBit_eq` alone adds 0.4 to 1.1 seconds of user time to a file that only imports the specifications.

So every use checks in under two seconds by itself.
The 20-second time of `roundConstantBit_eq` in one run of its file comes from the machine's load, not from the check.

The whole files, checked with `lake env lean` twice each before and after the restored proofs, at load average 17 to 25:

| File | Before (wall, user CPU) | After (wall, user CPU) |
| --- | --- | --- |
| `Sha256/Spec.lean` | 1.5–5.6 s, 0.8–1.3 s | 2.5–2.7 s, 1.3–1.4 s |
| `Keccak256/Spec.lean` | 3.6–4.0 s, 2.8–3.1 s | 11.9–15.3 s, 7.0–8.2 s |
| `Blake2b/Spec.lean` | 9.7–14.0 s, 9.6–10.1 s | 10.1–20.9 s, 10.4–13.3 s |

Part of the Keccak increase is the new Mathlib imports; `lake build` reported 21 seconds for the Keccak file at that load.

### What the copies leave out

They leave out what the inline specifications do not need:

- SHA-256: EthLib's executable `UInt32` code and its proofs (`compress_toState`, `hash_eq_spec`), since the specification is the model `Spec.compression` itself.
- Keccak: the padding lemmas and `keccakF_bijective`, with the rest of the rotation and XOR lemmas of `Proofs/Hash/KeccakPermutation.lean`.

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
2. Section 5.6 said that the SHA-256 and BLAKE2b proof files use `decide +kernel` "twice each", which suggested that only those two files need it.
   The Keccak proof files use it five times: `roundConstants_eq` and `rhoOffsets_eq` in `Proofs/Hash/Keccak.lean`, and `rhoOffset_eq`, `rhoOffset_lt` and `roundConstantBit_eq` in `Proofs/Hash/KeccakBitsPermutation.lean`.
   The last three carry EthLib's `toLanes_permutation`, which section 5.6 lists among the theorems the Keccak specification comes with.
   Commit `91d2680` corrected section 5.6, and the copies now carry all nine uses (see "Uses of `decide +kernel`").

One wording in sections 3 and 12.3 can mislead: both say that the inline expects "a big-endian block" through `rs2`.
The bytes at `rs2` are the message bytes in order, which is what the SDK passes; the builder reads them as big-endian words.
A guest does not byte-swap the block, but it does byte-swap the eight state words it reads back from `rs1`.
