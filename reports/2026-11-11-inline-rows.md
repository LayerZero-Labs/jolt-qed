# Inline rows: I0(a) checks, generated Lean and the round trip

Date: 2026-11-11.
This report covers I0(a) of `docs/inline-precompiles.md`: the expansion-parity driver's inline checks, the generated Lean rows of the 27 registered inlines, and the Lean round trip that compares those rows with Jolt.
The T1 comparison is in `reports/2026-11-11-expansion-parity.md`.

## Revisions

jolt-qed: branch `inline/i0a-generated`, on top of `inline/t1-driver` at `32fdd89`.
The generated rows in `JoltBytecode/Inlines/Generated/` come from the pin.
Toolchain: `leanprover/lean4:v4.35.0`.

Jolt revisions:

- Pin: a16z/jolt `main` at `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5` (`a6b6dc717`), the pin of the spec.
- a16z/jolt#2414 at `f1fe17f86e7bde402adb94bd52070d437c31fad9` (`f1fe17f86`), the head when the first round trip ran.
- a16z/jolt#2414 at `da3b89abd700d43bac9319b9c4bfe4e49d598b5e` (`da3b89abd`), the current head.
  It differs from `f1fe17f86` only in one line of `crates/jolt-program/src/expand/tests.rs`.

All driver runs use the default seed `1949392621`.

## How to run

Build the driver, run its checks and regenerate the Lean rows (needs a Jolt checkout):

```
JOLT_DIR=/path/to/jolt scripts/expansion-parity/run.sh WORK_DIR
```

The driver writes `WORK_DIR/out/rows.jsonl`, `WORK_DIR/out/inline_templates.json` and `WORK_DIR/out/summary.json`, and rewrites `JoltBytecode/Inlines/Generated/`.
`--no-lean` leaves the generated Lean alone, and `--lean-chunk N` sets the chunk size (default 100).
The script exits with 0 when every driver check passes.

Build the Lean side and run the round trip and the mutation check:

```
lake build JoltTests.ExpansionParity.Main
EXPANSION_PARITY_ARGS="inline OUT/rows.jsonl OUT/inline_templates.json INLINE_DIR [TRIPLES [SEED]]" lake env lean JoltTests/ExpansionParity/Run.lean
EXPANSION_PARITY_ARGS="mutation OUT/rows.jsonl" lake env lean JoltTests/ExpansionParity/Run.lean
```

`OUT` is `WORK_DIR/out`.
`inline` writes `inline-mismatches.jsonl` and `inline-summary.txt` to `INLINE_DIR`.
`TRIPLES` defaults to 300 random operand triples per template case.
`lean` exits with a nonzero status when a mode reports a disagreement.
The T1 report explains why the comparator runs through `lake env lean` and `#eval` rather than an executable.

The CI workflow `.github/workflows/expansion-parity.yml` runs the round trip when `JoltBytecode/Inlines/Generated/` is in the repository.
It has not run in CI yet.

## Driver checks at the pin

The driver links every `jolt-inlines/*` crate with feature `host` and finds the 27 registrations the spec lists.
Every check passed in the full run at the pin (`~/claude-work/expansion-parity-work/run-full.log`).

- Allocator restoration, fresh: after each successful expansion the allocator's `Debug` text equals that of `ExpansionAllocator::new()`, for every record.
- Allocator restoration, shared: one allocator expands all 1728 cases in sequence (6 of them return errors); after each case the allocator is restored, and every row equals the row from a fresh allocator.
- Fixture hashes: the driver recomputes all 108 lines of `registered_inline_expand_parity_hashes.jsonl` (27 inlines, four scenarios) and every name, registration field, row count and hash matches.
- Templates: each of the 54 cases (27 inlines, `normal` and `rd_zero`) expands to the same rows under operands A = (x11, x12, x13) and B = (x21, x22, x23) up to the register parameters.
- Operand uniformity: the driver expands every inline at every triple (rs1 and rs2 in 0..31, rs3 in 1..31 for `normal`; rs1 and rs2 in 0..31 for `rd_zero`), 884,736 triples in all, and every expansion equals the template at that triple; the run took 29.5 s on 10 threads.
- Write-before-read: in the twelve in-scope inlines (SHA256_INLINE, SHA256_INIT_INLINE, KECCAK256_INLINE, KECCAK256_ABSORB_PERMUTE_INLINE, BLAKE2_INLINE and the seven SECP256K1 inlines), every read of a pool register (vr48..127) follows a write of that register earlier in the same sequence, in both cases.
- Golden fixture: the 360 golden cases match Jolt's expansion fixture, and the rows without an inline provider equal the production rows.

The `out/summary.json` in that work directory comes from a later run with `--skip-uniformity`, which marks the uniformity check as not passed; `run-full.log` holds the full run.

### Observations outside the gated checks

BLAKE3_KEYED64_INLINE reads two pool registers before any row writes them: row 32 (`VirtualXORROTW16`) reads vr60 and row 42 (`VirtualXORROTW16`) reads vr61, in both cases.
BLAKE3_KEYED64 is not one of the twelve in-scope inlines; the check reports the reads and does not fail.
I did not check which value these reads see in a trace or whether BLAKE3_KEYED64's result depends on it.

NTT64_I32_FORWARD is the only inline that writes instruction temporaries: vr40 and vr41 in the `normal` case and vr41 and vr42 in the `rd_zero` case, where the `rd = x0` rewrite holds vr40.
No other inline writes vr32..47.

With rd = x0, Jolt rewrites rd to the temporary vr40 (`crates/jolt-program/src/expand/mod.rs:134-145`).
19 inlines read vr40 before any row writes it in the `rd_zero` case: BIGINT256_MUL_INLINE, BLAKE3_KEYED64_INLINE, the seven SECP256K1 inlines, the three GRUMPKIN inlines and the seven P256 inlines.
The reads are the base-address operands of their `LD` and `SD` rows; for example BLAKE3_KEYED64's rows 0, 2, 4 and 6 (`LD`) and 601, 605, 609 and 613 (`SD`) read vr40.
These are the 19 encodings that a16z/jolt#2414 rejects, and the spec (section 5.2, D7) names the same 19.
The other eight inlines never read vr40.

## Generated Lean

`scripts/expansion-parity/run.sh` writes one file per inline, `JoltBytecode/Inlines/Generated/<Name>.lean`, and `JoltBytecode/Inlines/Generated.lean`, which imports them; the README of the driver gives the naming and rendering rules.
Each file defines `<name>RowsAuto (rs1 rs2 rs3 : regidx)` and, where Jolt accepts rd = x0, `<name>RowsAutoRdZero (rs1 rs2 : regidx)`.
The 27 inlines have between 9 and 3,407 rows (NTT64_I32_FORWARD).

### Chunking

The generator first wrote each definition as one nested `.instr … <|` term.
In that form KECCAK256_ABSORB_PERMUTE_INLINE (3,121 rows) fails to elaborate at a6b6dc717: Lean reports "maximum recursion depth has been reached" at row 250 of both definitions (lines 280 and 3405 of the file), after 8.9 s (`~/claude-work/expansion-parity-work/lean-keccak-unchunked.log`).
Raising `maxRecDepth` is not allowed under `JoltBytecode/`.
The generator therefore splits the rows into chunks of 100 by default: `<name>RowsAuto[RdZero]Chunk<k> : List JoltISA.Instr` holds one chunk, `<name>RowsAuto[RdZero]List` concatenates the chunks, and `<name>RowsAuto[RdZero]` wraps the list with `JoltISA.Program.seq`.
With 100-row chunks every file elaborates under the default limits and without warnings.
The generated files set no option and contain no `sorry`, `native_decide`, `decide +kernel` or `bv_decide`.
`lake env lean` on the chunked KECCAK256_ABSORB_PERMUTE file took 34 s of wall time and 15.5 s of CPU time on a machine with load average 30 (`scripts/expansion-parity/README.md`).

### Elaboration time

`~/claude-work/expansion-parity-work/lean-times.tsv` records a `lake build` of each module on its own, on a machine that other sessions kept loaded.
The wall-clock times add up to 772 s for the 28 modules (27 files and `Generated.lean`).

| Module | Rows | Wall time (s) |
|---|---|---|
| `Blake3Keyed64` | 646 | 108.8 |
| `Blake3` | 648 | 84.1 |
| `Ntt64I32Forward` | 3,407 | 74.2 |
| `Blake2` | 1,067 | 68.6 |
| `Keccak256` | 3,087 | 63.0 |
| `Sha256Init` | 1,864 | 53.7 |
| `GrumpkinDivrAdv` | 9 | 42.6 |
| `GrumpkinDivqAdv` | 9 | 38.9 |
| `Ntt64I32PointwiseDot6` | 3,363 | 37.7 |
| `GrumpkinGlvrAdv` | 13 | 31.5 |
| `Bigint256Mul` | 141 | 23.2 |
| `Sha256` | 1,900 | 20.9 |
| `Keccak256AbsorbPermute` | 3,121 | 11.6 |
| each `Secp256k1*` and `P256*` file | 13 to 272 | 2.6 to 5.0 |
| `Generated` (imports only) | | 62.1 |

The times do not grow with the row count: the 9-row GRUMPKIN files take longer than the 1,900-row SHA256 file.
The measurement mixes elaboration with load on the machine, and the user times (0.8 s to 16.9 s) are much smaller than the wall times.
The `Keccak256AbsorbPermute` line has no build time from `lake`, unlike the other lines; I did not measure it again.

## Round trip

The round trip compares the generated rows with Jolt in two ways.

`compareInlineFixture` (`JoltTests/ExpansionParity/RoundTrip.lean`) takes each `inline_fixture` record of `rows.jsonl`.
It applies the generated `<name>RowsAuto` definition (or `RowsAutoRdZero` when rd = x0) at the record's operands, stamps the rows with `stamp_sequence`, and compares every field, flags, table and RAF bit included.

`compareTemplate` takes each case (`normal` and `rd_zero`) of each inline in `inline_templates.json`.
It instantiates the template at the driver's two triples A and B and at 300 seeded random triples (rs1 and rs2 in 0..31, rs3 in 1..31; rs3 is 0 for `rd_zero`), applies the generated definition at the same triple, and compares kind, address, rd, rs1, rs2, immediate, virtual sequence remaining, first-in-sequence and compressed.

The Lean side renders the `JoltISA.Instr` constructors with `RowView.ofLeanRow` (`JoltTests/ExpansionParity/Row.lean`) and shares no code with the generator (`scripts/expansion-parity/src/lean.rs`).
The table of generated definitions (`JoltTests/ExpansionParity/Inline.lean`) is written by hand.
A renamed or missing definition fails to elaborate, and the run checks that the templates and the table name the same 27 inlines.
Inlines with `VirtualAdvice` rows take an advice function, which the test sets to `k ↦ k`; advice values reach no rendered field.

### At the pin

All 216 fixture records agree (176,600 rows), every field included.
The templates give 16,308 instantiations (27 inlines, two cases each, 302 triples per case) with 13,333,300 rows, and every row agrees.
The template names and the Lean table name the same 27 inlines.
The run reports 0 field mismatches and exits with status 0; it took about 5 minutes.

### At a16z/jolt#2414

The results at `f1fe17f86` and at `da3b89abd` are the same; the driver's `rows.jsonl` is byte-identical at the two commits, `inline_templates.json` differs only in the recorded Jolt commit, and the two round-trip summaries are equal line for line.

178 of the 216 fixture records agree (169,364 rows in all).
The 38 others are the `rd_zero` fixture records of 19 inlines, in both allocators: Jolt returns `InlineReadsZeroRd { register: 40 }`, while Lean has `RowsAutoRdZero` rows for them.
The templates file has `"rd_zero": null` for the same 19 inlines, which the run reports once per inline as "Lean defines rd = x0 rows that Jolt rejects".
The 19 are the inlines that read vr40 in the `rd_zero` case at the pin (listed above).
The other 10,570 template instantiations (12,240,664 rows), which include the `rd_zero` cases of the eight inlines Jolt still accepts with rd = x0, all agree.
The run reports 57 field mismatches (19 + 38) and exits with status 1.

The driver checks at `da3b89abd` all pass.
The fixture file there has 19 lines with an `error` field, and Jolt returns exactly those errors.
Operand uniformity covers 865,280 triples, because the 19 rejected `rd_zero` cases have no template.
In the shared-allocator check 25 of the 1728 cases return errors (6 at the pin), and the allocator is restored after each of them.
The BLAKE3_KEYED64 pool reads and the NTT64_I32_FORWARD temporaries are the same as at the pin.

Classification: expected, and not a fault in the generated rows.
The generated files come from the pin, where Jolt accepts these encodings.
Regenerating them at #2414 drops the 19 `RowsAutoRdZero` definitions, and the registration check of section 5.2 (I1a) excludes these encodings from Lean's source language.

### Mutation checks

The `mutation` mode corrupts one field of one row of a Rust record and checks that the comparison reports the corruption at that row and field.
It does this for each of the 11 compared field kinds (kind, rs1, rd, immediate, virtual sequence remaining, first, compressed, circuit flags, instruction flags, lookup table, RAF flag) on the first T1 record with ten or more rows and on the first inline fixture record (`SHA256_INLINE::normal`).
It also corrupts the 4 metadata fields of a T1 record compared on row metadata only (see the T1 report).
At the pin all three unmutated records give 0 mismatches, and the comparisons report all 26 corruptions.

Two file-level checks confirm that the whole `inline` run fails when Rust's data changes.
I ran them with the same `RoundTrip.lean` on the earlier branch `inline/t1-lean`.

- I raised the immediate of row 100 of `KECCAK256_INLINE::normal` (fresh allocator) by one in a copy of `rows.jsonl`; the run reports exactly that mismatch (`imm of ANDN rows`, Rust 1, Lean 0) and exits with status 1.
- I changed the `rs1` parameter of row 0 of `SECP256K1_MULQ`'s `normal` template from `rs1` to `rs2` in a copy of `inline_templates.json`; the run reports row 0 at both fixed triples (Rust 12, Lean 11 and Rust 22, Lean 21) and exits with status 1.

## Contradictions with the spec

- The spec's round-trip check (section 11) holds at the pin; at #2414 the generated files are out of date for 19 `rd_zero` cases until they are regenerated, as described above.
- The spec asks for a test executable; the round trip runs through `lake env lean` and `#eval` for the reason given in the T1 report.

## Follow-ups

- Regenerate `JoltBytecode/Inlines/Generated/` when #2414 merges and the pin moves, and rerun the round trip.
- Decide whether BLAKE3_KEYED64's reads of vr60 and vr61 before any write need attention before BLAKE3_KEYED64 enters scope.
- The non-blocking CI job in `.github/workflows/expansion-parity.yml` has not run yet.
