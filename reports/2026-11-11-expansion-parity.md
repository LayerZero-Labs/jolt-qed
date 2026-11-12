# Expansion parity: T1

Date: 2026-11-11.
T1 gives zero mismatches at a16z/jolt#2384 head `580084fcf`: every non-inline record agrees with Lean's `expand_instruction` and `metadata.lean`, and the comparator exits with 0.
The CI job checks out that commit, builds the driver with the cargo feature `zicsr-remaining`, and fails on any T1 disagreement.

This report gives the T1 mismatch report of `docs/inline-precompiles.md` (section 7, T1): Jolt's expansion of every non-inline source kind compared row by row with Lean.
The inline checks of I0(a), the generated inline rows and the inline round trip are in `reports/2026-11-11-inline-rows.md`.

## Revisions

jolt-qed: branch `inline/t1-driver` on top of `bf22776`.
I ran the T1 and mutation results at `580084fcf` below with the comparator and driver of commit `97e1aaf`.
The earlier results (at the pin, at `c336a6da7` and at #2414) came from the comparator of commit `77b9f3a` and the driver before the ANDN fix.
The branch has no generated inline rows, and the comparator does not import them.
Toolchain: `leanprover/lean4:v4.35.0`.

Jolt revisions:

- a16z/jolt#2384 (branch `feat/zicsr-remaining-forms`) at `580084fcfad4788ebf48413a92dd640ca090c45f` (`580084fcf`), the revision T1 and CI check.
  It contains the spec's pin `a6b6dc717` as an ancestor (17 commits on top).
  Lean's system expansions and decoder follow #2384.
- Pin: a16z/jolt `main` at `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5` (`a6b6dc717`), the pin of the spec.
- a16z/jolt#2384 at `c336a6da706d0a0d11c3489c7aef71ee80c2e370` (`c336a6da7`), the commit that the module docstring of `System.lean` names, before the restack.
- a16z/jolt#2414 at `f1fe17f86e7bde402adb94bd52070d437c31fad9` (`f1fe17f86`) and at `da3b89abd700d43bac9319b9c4bfe4e49d598b5e` (`da3b89abd`).

All driver runs use the default seed `1949392621`.
The runs at `580084fcf` and `c336a6da7` build the driver with `zicsr-remaining`, which adds the four CSR kinds the pin's decoder lacks and a `csr` group (described below).

### What changed between the pin and `580084fcf`

I compared the driver output at `580084fcf` with the output at the pin.

- The 216 inline fixture records are identical.
- `inline_templates.json` differs only in its `jolt_commit` field.
- The inline hash fixture `registered_inline_expand_parity_hashes.jsonl` is unchanged.
- In the `golden` group 48 records differ: CSRRW 18, CSRRS 18, ECALL 6, MRET 6.
  These are the system expansions that #2384 changes.
  `main_expand_parity_hashes.json` changes in one line, the hash over the golden fixture.

No generated Lean needed regenerating.

## How to run

Build the driver and write its output (needs a Jolt checkout):

```
EXPANSION_PARITY_FEATURES=zicsr-remaining JOLT_DIR=/path/to/jolt-580084fcf scripts/expansion-parity/run.sh WORK_DIR --no-lean
```

`--no-lean` keeps the driver from writing generated inline rows into the repository.
The driver writes `WORK_DIR/out/rows.jsonl`, `inline_templates.json` and `summary.json`.

Build the comparator once, then run a mode by putting its arguments in `EXPANSION_PARITY_ARGS`:

```
lake build JoltTests.ExpansionParity.Main
EXPANSION_PARITY_ARGS="t1 WORK_DIR/out/rows.jsonl T1_DIR" lake env lean JoltTests/ExpansionParity/Run.lean
EXPANSION_PARITY_ARGS="mutation WORK_DIR/out/rows.jsonl" lake env lean JoltTests/ExpansionParity/Run.lean
```

`t1` writes `t1-mismatches.jsonl` (one JSON object per field mismatch) and `t1-summary.txt` (counts per group and mismatches grouped by cause) to `T1_DIR`.
`lean` exits with a nonzero status when a mode reports a disagreement, because `Run.lean` then throws from its `#eval`.
A T1 run takes about 2 minutes on this machine.

The spec asks for a test executable.
A `lean_exe` cannot work here: `LeanRV64D.lean:297` declares a root `main` (the Sail model's entry point), and `JoltBytecode/JoltISA/Core.lean` imports `LeanRV64D`.
Every executable that imports the model therefore already has a `main`.
`Run.lean` calls `ExpansionParity.cli` from `#eval` instead, and the code runs in the interpreter.

The CI workflow `.github/workflows/expansion-parity.yml` sets `JOLT_REV` to `580084fcf` and `EXPANSION_PARITY_FEATURES` to `zicsr-remaining`.
It runs the driver, the T1 comparator and the mutation check, and runs the inline round trip once the generated rows are in the repository.
The job is a normal, blocking check.

## What the comparator checks

`ExpansionParity.compareT1` (`JoltTests/ExpansionParity/Compare.lean`) handles each record whose source is not `Inline`.
It maps the Rust source to a Lean `SourceInstruction` with `SourceView.toLean` (`JoltTests/ExpansionParity/Source.lean:116`).
The map uses Rust's kind names, takes the immediate in the form `decode.rs` produces, and fixes the operands Lean carries but Rust does not (the division quotient is 0 and the atomic `aq` and `rl` bits are false).
It then runs `expand_instruction` (`JoltConstraints/program.lean:186`), which calls `SourceInstruction.expand` (`JoltConstraints/expansions.lean:17`) and `stamp_sequence` (`JoltConstraints/program.lean:161`).
`RowView.ofLeanRow` (`JoltTests/ExpansionParity/Row.lean:283`) renders each Lean row: the kind and registers come from the `JoltISA.Instr` constructor, the immediate from `JoltMetadata.immediate`, the flags from `JoltMetadata.circuitFlag` and `JoltMetadata.instructionFlag`, the table from `JoltMetadata.lookupTable`, and the RAF flag from `JoltMetadata.instructionRafFlag` (`JoltConstraints/metadata.lean:17`, `:58`, `:225`, `:268`, `:334`).
The comparison covers kind, address, rd, rs1, rs2, immediate, virtual sequence remaining, first-in-sequence, compressed, circuit flags, instruction flags, lookup table and RAF flag, and the row count.
When Rust returns an error, the record matches only if Lean rejects as well; the summary says how Lean rejects.
`readResult` (`Compare.lean:50`) requires each record's `result` to hold exactly one field, either a `rows` array of well-formed rows or an `error` string.
Any other `result` (empty, both fields, a non-string error, a non-array `rows`) stops the run with an error.
A malformed record therefore cannot count as a rejection.

Some Rust source kinds have no Lean `SourceInstruction` constructor, and the comparator cannot expand them on the Lean side.
`noLeanSourceKinds` (`Source.lean:235`) lists these 57 kinds explicitly: `NoOp`, `Unimpl` and 55 `Virtual*` kinds.
For records of these kinds `compareRowMetadata` compares each Rust row's circuit flags, instruction flags, lookup table and RAF flag with `metadata.lean`.
Every metadata function depends only on the row's `JoltISA.Instr` constructor and its sequence stamp, not on its operands.
`instrOfKind` (`Row.lean:253`) therefore picks a sample instance of the constructor with the row's kind name, and `RowView.leanMetadataOf` (`Row.lean:302`) stamps it with the Rust row's virtual sequence remaining, first-in-sequence and compressed fields.
The summary reports these records as a separate class, "row metadata compared, no Lean source constructor", with their own counts.
A record of any other kind that `SourceView.toLean` does not map is a disagreement with the cause "unknown Rust source kind", whether Rust returned rows or an error.

Every record appears twice, once per driver allocator (`fresh` and `shared`); the counts below count both.

### NoOp: padding, not a Lean source instruction

Jolt uses `NoOp` rows only as bytecode padding, and no decode or expansion path yields one.
I checked this at `580084fcf`:

- The decoder never produces a `NoOp` source.
  `decode_instruction` (`crates/jolt-program/src/image/decode.rs:22`) has no opcode arm that returns `NoOp`.
  The only mention of `NoOp` in `decode.rs` is the operand-format arm at line 356, which gives `NoOp` empty operands.
- The `rd = x0` rewrite does not emit a `NoOp` row.
  `noop_for` (`crates/jolt-program/src/expand/operands.rs:4`), called at `expand/mod.rs:146` and `expand/materialize.rs:93`, emits `ADDI x0, x0, 0`.
- A `NoOp` row arises only from a `NoOp` source built directly.
  `NoOp` is not in `is_source_only` (`expand/grammar.rs:388`).
  `JoltInstructionRow::try_from` (`expand/materialize.rs:100`) therefore turns such a source into one `NoOp` row.
- Jolt itself builds `NoOp` rows only to pad the bytecode: `preprocess/bytecode.rs:47` inserts `noop_instruction()` (`:288`) at index 0, and `:51` pads the bytecode to a power of two with it.

Lean's row language (`JoltISA.Instr`) has no `NoOp` constructor, and I did not change `JoltISA`.
The comparator encodes the facts above as two checks:

- A record whose source is `NoOp` and whose rows are exactly one `NoOp` row is classified as padding, not a Lean source instruction (`T1Outcome.padding`), and the summary counts these records on their own line.
- Every row of every record whose source is not `NoOp` must have a kind other than `NoOp` (`noOpRows`, check `noop_rows`).
  A `NoOp` row there is a disagreement.

A `NoOp` source with rd = x0 (`rd_zero` group) becomes `ADDI x0, x0, 0` through the rewrite; its record stays in the row-metadata class and agrees.

## T1 at `580084fcf`

Records compared per group, and records that agree:

| Group | Compared | Agree |
|---|---|---|
| `golden` | 720 | 720 |
| `aliased` | 206 | 206 |
| `rd_zero` | 204 | 204 |
| `rs1_zero` | 206 | 206 |
| `random` | 1216 | 1216 |
| `native_kind` | 206 | 206 |
| `csr` | 864 | 864 |

The comparator left the 216 `inline_fixture` records to the inline round trip.
No record disagrees, and the run has 0 field mismatches.
Every Zicsr kind that Lean decodes has records.

The `csr` group runs each of the six Zicsr kinds (CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI) on each of the six CSRs Jolt models (`mstatus`, `mtvec`, `mscratch`, `mepc`, `mcause`, `mtval`), with rd in {x0, x9} and rs1 in {0, 2, 3, 8, 9, 31}.
For the immediate forms rs1 is the five-bit constant.
The values cover a zero source, the reserved `mtvec` MODE bit (2), `mstatus.MIE` (8), rs1 = rd (9) and all five bits set.
The group has 432 cases, 864 records with both allocators.

The system instructions account for 1112 records with 2076 rows, all equal on every field:

| Kind | Records | Rows |
|---|---|---|
| ECALL | 26 | 156 |
| EBREAK | 26 | 26 |
| MRET | 26 | 78 |
| CSRRW | 198 | 436 |
| CSRRS | 198 | 446 |
| CSRRC | 160 | 246 |
| CSRRWI | 158 | 246 |
| CSRRSI | 160 | 220 |
| CSRRCI | 160 | 222 |

Both sides reject 30 records:

- 22 Zicsr records in the `random` group whose CSR Jolt does not model: Rust returns `UnsupportedCsr`, and Lean's constructors take a `JoltISA.SystemCSR`, which cannot hold the CSR.
- 8 `Unimpl` records: Rust returns `IllegalSourceInstruction(Unimplemented(Unimpl(())))`, and Lean has no `SourceInstruction` constructor for `Unimpl`.

The comparator classifies 8 `NoOp` records as padding (2 each in `aliased`, `native_kind`, `random` and `rs1_zero`).
It checked the 189,334 rows of all records whose source is not `NoOp` for `NoOp` rows and found none.

### Row metadata compared, no Lean source constructor

This class has 554 records with one row each (110 in each of `aliased`, `native_kind`, `random` and `rs1_zero`, and 114 in `rd_zero`), and all 554 agree.
Their source kinds are the 57 kinds of `noLeanSourceKinds`; the `NoOp` records here are the two in `rd_zero`, whose row is `ADDI x0, x0, 0`.
Rust's decoder never produces these kinds; the driver builds them directly from a `SourceInstructionRow` (`summary.json` lists them as `direct_kinds`).
Every `Virtual*` row agrees with `metadata.lean`, flags, table and RAF bit included.

`Unimpl` has rows only in its 2 `rd_zero` records; the other 8 `Unimpl` records are rejected by both sides.
With rd = x0 the `rd = x0` rewrite (`crates/jolt-program/src/expand/mod.rs:146`) returns `ADDI x0, x0, 0` before the expander rejects `Unimpl`.
Rust therefore accepts `Unimpl` with rd = x0 and rejects it otherwise.
This does not reach a guest, because the decoder never produces `Unimpl`.

### ANDN: the driver no longer gives a direct ANDN source an immediate

`ANDN` is an R-type kind that the decoder never produces (it is in `direct_kinds`).
Before the fix, the `random` group gave every direct case a random immediate, and the record `random/0608/ANDN/direct` (both allocators) carried immediate -1522 into its `ANDN` row.
Lean's `ANDN` constructor has no immediate, which left 0 in Lean's row, and the two records disagreed on the immediate.
`random_group` (`scripts/expansion-parity/src/cases.rs`) now sets the immediate of a direct `ANDN` case to 0, as an R-type word from the decoder would have.
It still draws the random value, and every later case keeps its operands.
At `580084fcf` the record has immediate 0 and agrees.

## Earlier results

These results came from the comparator of commit `77b9f3a`, before the `NoOp` and ANDN changes.

At the pin `a6b6dc717`, 116 records disagreed, with 1808 field mismatches.
114 of them were the system instructions: every ECALL and MRET record (26 each), and CSRRW and CSRRS on `mstatus`, `mtvec` and `mepc` (30 CSRRW and 32 CSRRS records).
Lean transcribes these expansions from #2384 (for example ECALL: 7 rows at the pin and 6 in Lean, MRET: 1 row at the pin and 3 in Lean), and the pin has the older expanders (`crates/jolt-program/src/expand/control_flow/ecall.rs:10`, `mret.rs:8`, `csrrw.rs:10`, `csrrs.rs:11`).
The pin's decoder also rejects CSRRC, CSRRWI, CSRRSI and CSRRCI, which Lean decodes (`JoltBytecode/Decode/Jolt.lean:181-184`).
The other 2 records were the direct ANDN source with an immediate (`random/0584/ANDN/direct`, immediate -414).
The 8 direct `NoOp` records disagreed in the row-metadata class, because `JoltISA.Instr` has no `NoOp` constructor.

At #2384 `c336a6da7` every system instruction agreed, with the same system-instruction counts as at `580084fcf`.
The only disagreements were the ANDN records and the 8 `NoOp` records.

At #2414 (`f1fe17f86` and `da3b89abd`) T1 gave the same counts and causes as at the pin, field for field.
#2414 changes only inline expansion, and the driver's `rows.jsonl` at `da3b89abd` is byte-for-byte the same as at `f1fe17f86`.

Quang decided that T1 checks #2384 rather than the pin, that the goal is zero mismatches, and that `NoOp` is classified as padding with the check above rather than by a change to `JoltISA`.

## A mapping artefact fixed in the comparator

The first run also reported a gap for 54 golden records of SRAI and SRAIW.
Jolt's golden fixture passes the bare shift amount as the immediate, while `decode.rs` produces `0x400 | shamt`.
`expand_srai` and `expand_sraiw` read only `imm & 0x3f` and `imm & 0x1f` (`crates/jolt-program/src/expand/shifts/srai.rs:11`, `sraiw.rs:6`).
`shamt` (`JoltTests/ExpansionParity/Source.lean:89`) accepts both forms, and the 54 records agree.

## Mutation check

The `mutation` mode corrupts one field of one row of a Rust record and checks that the comparison reports the corruption at that row and field.
On the first T1 record with ten or more rows (`MULHSU_imm_0_compressed_false`) it corrupts each of the 13 compared row fields: kind, address, rd, rs1, rs2, immediate, virtual sequence remaining, first, compressed, circuit flags, instruction flags, lookup table and RAF flag.
On the first agreeing record of the row-metadata class whose row has flags and a table (`aliased/VirtualAssertLTE/direct`) it corrupts the 4 metadata fields.
It then corrupts whole records and checks that each corrupted record is flagged, either as a disagreement or as a record the comparator refuses to read.
On each of these two records it replaces the source kind with `UNKNOWN_KIND` and replaces `result` with `{}`, with an `error` that is a number, with an `error` that is null, with a `rows` that is a string, and with both `rows` and `error` (6 corruptions per record).
On the first record both sides reject by kind (`aliased/Unimpl/direct`) it makes the same corruptions except the last, which needs rows (5 corruptions).
Last, it sets the kind of row 0 of the `MULHSU` record to `NoOp` and checks that `noOpRows` reports it.
At `580084fcf` the three unmutated records pass, and the comparator flags all 35 corruptions (17 field corruptions, 17 record corruptions and the `NoOp` row).

## Fixes

No fix to the model came out of T1.
The fixes are in the test harness: the driver's ANDN immediate, the explicit list of source kinds without a Lean constructor, strict reading of `result`, and the `NoOp` padding check.

## Contradictions with the spec

- The T1 row asks for a Lean test executable; `LeanRV64D.lean:297` rules out a `lean_exe` that imports the model, and the comparator runs through `lake env lean` and `#eval` instead.
- The spec cites a16z/jolt `main` at `a6b6dc717` for its code references, but T1 checks #2384 at `580084fcf`, because Lean's system expansions and decoder follow #2384.
  `580084fcf` contains `a6b6dc717`, and the inline rows are the same at both.
- The T1 row lists "every native kind once" among the inputs; Lean's source language has no constructor for 57 of Jolt's source kinds, and T1 compares only the row metadata of those kinds (and classifies direct `NoOp` sources as padding).

## Follow-ups

- When #2383 and #2384 merge, move `JOLT_REV` and the spec's pin to a `main` commit that contains them.
- The module docstring of `JoltBytecode/JoltISA/Expansions/System.lean` still names `c336a6da7`; it could name `580084fcf`, which gives the same system rows.
