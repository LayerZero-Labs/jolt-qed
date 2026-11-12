# Expansion parity: T1

Date: 2026-11-11.
This report gives the T1 mismatch report of `docs/inline-precompiles.md` (section 7, T1): Jolt's expansion of every non-inline source kind compared row by row with Lean's `expand_instruction` and `metadata.lean`.
The inline checks of I0(a), the generated inline rows and the inline round trip are in `reports/2026-11-11-inline-rows.md`.

## Revisions

jolt-qed: branch `inline/t1-driver` on top of `bf22776`.
I ran every T1 and mutation result below with the comparator of commit `77b9f3a`.
The branch has no generated inline rows, and the comparator does not import them.
Toolchain: `leanprover/lean4:v4.35.0`.

Jolt revisions:

- Pin: a16z/jolt `main` at `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5` (`a6b6dc717`), the pin of the spec.
- a16z/jolt#2384 at `c336a6da706d0a0d11c3489c7aef71ee80c2e370` (`c336a6da7`), the commit that Lean's system expansions and decoder transcribe.
  #2384 is stacked on a16z/jolt#2383; both are open.
- a16z/jolt#2414 at `f1fe17f86e7bde402adb94bd52070d437c31fad9` (`f1fe17f86`) and at its current head `da3b89abd700d43bac9319b9c4bfe4e49d598b5e` (`da3b89abd`).
  #2414 makes Jolt reject `rd = x0` for inlines that read rd; `da3b89abd` differs from `f1fe17f86` only in one line of `crates/jolt-program/src/expand/tests.rs`.

All driver runs use the default seed `1949392621`.
The run at `c336a6da7` builds the driver with the cargo feature `zicsr-remaining`, which adds the four CSR kinds the pin's decoder lacks and a `csr` group (described below).

## How to run

Build the driver and write its output (needs a Jolt checkout):

```
JOLT_DIR=/path/to/jolt scripts/expansion-parity/run.sh WORK_DIR --no-lean
EXPANSION_PARITY_FEATURES=zicsr-remaining JOLT_DIR=/path/to/jolt-c336a6da7 scripts/expansion-parity/run.sh WORK_DIR --no-lean
```

The second line is the run against a16z/jolt#2384.
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

The CI workflow `.github/workflows/expansion-parity.yml` runs the driver at the pin, the T1 comparator and the mutation check, and runs the inline round trip once the generated rows are in the repository.
It is non-blocking and has not run in CI yet.

## What the comparator checks

`ExpansionParity.compareT1` (`JoltTests/ExpansionParity/Compare.lean:129`) handles each record whose source is not `Inline`.
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
`noLeanSourceKinds` (`Source.lean:235`) lists these kinds explicitly: the 57 kinds of the pin given below.
For records of these kinds `compareRowMetadata` (`Compare.lean:113`) compares each Rust row's circuit flags, instruction flags, lookup table and RAF flag with `metadata.lean`.
Every metadata function depends only on the row's `JoltISA.Instr` constructor and its sequence stamp, not on its operands.
`instrOfKind` (`Row.lean:253`) therefore picks a sample instance of the constructor with the row's kind name, and `RowView.leanMetadataOf` (`Row.lean:302`) stamps it with the Rust row's virtual sequence remaining, first-in-sequence and compressed fields.
The summary reports these records as a separate class, "row metadata compared, no Lean source constructor", with their own counts.
A record of any other kind that `SourceView.toLean` does not map is a disagreement with the cause "unknown Rust source kind", whether Rust returned rows or an error.

Every record appears twice, once per driver allocator (`fresh` and `shared`); the counts below count both.

## T1 at the pin

Records compared per group, and records that agree:

| Group | Compared | Agree | Disagree |
|---|---|---|---|
| `golden` | 720 | 672 | 48 |
| `aliased` | 198 | 190 | 8 |
| `rd_zero` | 196 | 188 | 8 |
| `rs1_zero` | 198 | 190 | 8 |
| `random` | 1168 | 1132 | 36 |
| `native_kind` | 198 | 190 | 8 |

The comparator left the 216 `inline_fixture` records to the inline round trip.
116 records disagree, with 1808 field mismatches.
Two causes explain all of them: the system instructions (114 records: 48 `golden`, 8 in each of `aliased`, `rd_zero`, `rs1_zero` and `native_kind`, and 34 `random`) and a direct ANDN source with an immediate (2 `random` records).

Both sides reject 12 records:

- `Unimpl` (8 records): Rust returns `IllegalSourceInstruction(Unimplemented(Unimpl(())))`, and Lean has no `SourceInstruction` constructor for `Unimpl`.
- `CSRRW` and `CSRRS` with CSR 3484 and 2101 (2 records each): Rust returns `UnsupportedCsr` (`crates/jolt-program/src/expand/control_flow/csrrw.rs:14`, `csrrs.rs:15`), and Lean's `CSRRW` and `CSRRS` constructors take a `JoltISA.SystemCSR`, which has no such CSR.

### Row metadata compared, no Lean source constructor

This class has 562 records, one row each: 112 in each of `aliased`, `native_kind`, `random` and `rs1_zero`, and 114 in `rd_zero`.
Their source kinds are `NoOp`, `Unimpl` and 55 `Virtual*` kinds (57 kinds in all, for example `VirtualAdvice`, `VirtualSRA`, `VirtualLoadW`, `VirtualStoreB`, `VirtualXORROT32`).
Rust's decoder never produces these kinds; the driver builds them directly from a `SourceInstructionRow` (`summary.json` lists them as `direct_kinds`).
`Unimpl` has rows only in its 2 `rd_zero` records (see below); the other 8 `Unimpl` records are rejected by both sides.

554 records agree, and 8 disagree:

| Group | Records | Agree | Disagree |
|---|---|---|---|
| `aliased` | 112 | 110 | 2 |
| `native_kind` | 112 | 110 | 2 |
| `random` | 112 | 110 | 2 |
| `rd_zero` | 114 | 114 | 0 |
| `rs1_zero` | 112 | 110 | 2 |

The 8 disagreements are the `NoOp` records outside `rd_zero`: Rust emits one row of kind `NoOp` (instruction flag `IsNoop`, circuit flag `DoNotUpdateUnexpandedPC`, no table), and `JoltISA.Instr` has no `NoOp` constructor.
`JoltMetadata.instructionFlag` returns `false` for `IsNoop` on every row.
No expansion in any record emits a `NoOp` row; the 8 rows come from direct `NoOp` sources.
In `rd_zero` the `rd = x0` rewrite turns `NoOp` into `ADDI x0, x0, 0`, whose metadata agrees.

Every `Virtual*` row agrees with `metadata.lean`, flags, table and RAF bit included.
The two `rd_zero/Unimpl/direct` records show an ordering detail in Rust: with rd = x0, the `rd = x0` rewrite (`crates/jolt-program/src/expand/mod.rs:134-145`) returns a no-op row before the expander rejects `Unimpl`.
Rust therefore accepts `Unimpl` with rd = x0 and rejects it otherwise.
This does not reach a guest, because the decoder never produces `Unimpl`.

Classification: the source-level gap is a driver artefact, since these kinds lie outside Lean's source language by design and T2 (the decoder sweep) is the check that the decoder never produces them.
The `NoOp` row disagreement is a gap in Lean's row language for direct `NoOp` sources only; I did not change anything for it.

### Cause 1: Lean's system instructions follow a16z/jolt#2384, not the pin

Every ECALL and MRET record disagrees (26 each).
CSRRW and CSRRS disagree on every record whose CSR is `mstatus` (0x300), `mtvec` (0x305) or `mepc` (0x341): 30 CSRRW and 32 CSRRS records.
They agree on `mscratch`, `mcause` and `mtval`, and EBREAK agrees everywhere.

Examples from the `native_kind` group at the pin (ECALL and MRET have no operands; the CSR examples have rd = x9 and rs1 = x5):

- ECALL: Rust emits 7 rows: `AUIPC v40, 0`; `ADDI v36, v40, 0`; `ADDI v37, x0, 11`; `ADDI v38, x0, 0`; `ADDI v40, x0, 3`; `VirtualMULI v39, v40, 2048`; `JALR v40, v34, 0`.
  Lean emits 6 rows: `AUIPC v36, 0`; `ADDI v37, x0, 11`; `ADDI v38, x0, 0`; `ANDI v40, v39, 8`; `VirtualMULI v39, v40, 16`; `JALR v40, v34, 0`.
- MRET: Rust emits 1 row, `JALR v40, v36, 0`.
  Lean emits 3 rows: `VirtualSRLI v39, v39` (shift by 4), `ORI v39, v39, 0x80`, `JALR v40, v36, 0`.
- CSRRW `mstatus`: Rust emits `ADDI x9, v39, 0` and `ADDI v39, x5, 0`.
  Lean emits `ORI x9, v39, 0x1800` and `ANDI v39, x5, 0x88`.
- CSRRS `mstatus`: Rust emits `ADDI x9, v39, 0` and `OR v39, v39, x5`.
  Lean emits `ANDI v40, x5, 0x88`, `ORI x9, v39, 0x1800` and `OR v39, v39, v40`.

Rust at the pin: `expand_ecall` (`crates/jolt-program/src/expand/control_flow/ecall.rs:10`), `expand_mret` (`mret.rs:8`), `expand_csrrw` (`csrrw.rs:10`), `expand_csrrs` (`csrrs.rs:11`).
Lean: `JoltISA.ecallProgram` (`JoltBytecode/JoltISA/Expansions/System.lean:66`), `JoltISA.mretProgram` (`:88`), `JoltISA.csrrwProgram` (`:127`), `JoltISA.csrrsProgram` (`:190`) with `csrReadInto` (`:100`), `csrSwapWrite` (`:111`) and `csrBitUpdateProgram` (`:153`).
The module docstring of `System.lean` says that these programs transcribe Jolt's expander at `c336a6da7`.

Lean's decoder also accepts four source kinds that the pin rejects.
`JoltBytecode/Decode/Jolt.lean:181-184` decodes CSRRC, CSRRWI, CSRRSI and CSRRCI, and `JoltConstraints/expansions.lean:117-120` expands them.
At the pin `decode_system` (`crates/jolt-program/src/image/decode.rs:195-203`) returns "unsupported system instruction" for them, and the driver has no record for them at the pin.

## T1 at a16z/jolt#2384 (`c336a6da7`)

Lean agrees with #2384 on every system instruction, row by row.

The run adds a `csr` group: each of the six Zicsr kinds (CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI) on each of the six CSRs Jolt models (`mstatus`, `mtvec`, `mscratch`, `mepc`, `mcause`, `mtval`), with rd in {x0, x9} and rs1 in {0, 2, 3, 8, 9, 31}.
For the immediate forms rs1 is the five-bit constant.
The values cover a zero source, the reserved `mtvec` MODE bit (2), `mstatus.MIE` (8), rs1 = rd (9) and all five bits set.
The group has 432 cases, 864 records with both allocators.

Records compared per group, and records that agree:

| Group | Compared | Agree |
|---|---|---|
| `golden` | 720 | 720 |
| `aliased` | 206 | 206 |
| `rd_zero` | 204 | 204 |
| `rs1_zero` | 206 | 206 |
| `random` | 1216 | 1214 |
| `native_kind` | 206 | 206 |
| `csr` | 864 | 864 |

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

Every CSR kind is compared on all six CSRs.
Both sides reject the 22 Zicsr records whose CSR Jolt does not model (random CSRs in the `random` group): Rust returns `UnsupportedCsr`, and Lean's constructors cannot hold the CSR.
Both sides also reject the 8 `Unimpl` records, as at the pin.

The only disagreement is cause 3 below (2 `random` records, `random/0608/ANDN/direct`).
The row-metadata class gives the same counts as at the pin: 562 records, 554 agree, and the 8 `NoOp` records disagree.

### Proposal for Ari: the Jolt revision T1 checks for the system instructions

The system expansions feed `InLanguage`, and I did not change them.
Lean matches #2384 at `c336a6da7` exactly and disagrees with the pin on ECALL, MRET, and CSRRW and CSRRS on `mstatus`, `mtvec` and `mepc`.
Two ways to make T1 clean:

1. Wait for a16z/jolt#2383 and #2384 to merge and move the pin to a commit that contains them.
2. Check the system kinds against `c336a6da7` now: run the driver there with `zicsr-remaining` for ECALL, MRET and the six Zicsr kinds, and record that revision in the coverage ledger (T3b) and the provenance manifest (T7).

## T1 at a16z/jolt#2414

At `f1fe17f86` and at `da3b89abd` T1 gives the same counts and the same causes as at the pin, field for field.
The driver's `rows.jsonl` at `da3b89abd` is byte-for-byte the same as at `f1fe17f86`.
#2414 changes only inline expansion.

## Cause 3: a direct ANDN source with a nonzero immediate

Two `random` records (`random/0584/ANDN/direct` at the pin and at #2414, `random/0608/ANDN/direct` at `c336a6da7`, both allocators) disagree on the immediate of their single `ANDN` row.
Rust carries the source immediate (-414 at the pin, -1522 at `c336a6da7`) into the row, and Lean's `ANDN` constructor has no immediate, which leaves 0 in Lean's row.
`ANDN` is an R-type kind that the decoder never produces (it is in `direct_kinds`), and the driver gives direct cases a random immediate.
The other ANDN records, whose immediate is 0, agree.

Classification: driver artefact.

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
At the pin the three unmutated records pass, and the comparator flags all 34 corruptions (17 field corruptions and 17 record corruptions).

## Fixes

No fix to the model came out of T1.
Every disagreement is cause 1, which concerns definitions under `InLanguage` and is a proposal, a driver artefact, or the `NoOp` row gap for direct sources.

## Contradictions with the spec

- The T1 row asks for a Lean test executable; `LeanRV64D.lean:297` rules out a `lean_exe` that imports the model, and the comparator runs through `lake env lean` and `#eval` instead.
- The spec cites a16z/jolt `main` at `a6b6dc717` for its code references, but Lean's system expansions and decoder transcribe a16z/jolt#2384 at `c336a6da7`; T1 at the pin cannot be clean for ECALL, MRET, CSRRW and CSRRS until the proposal above is decided.
- The T1 row lists "every native kind once" among the inputs; Lean's source language has no constructor for 57 of Jolt's source kinds, and T1 compares only the row metadata of those kinds.

## Follow-ups

- Decide the Jolt revision for the system instructions (proposal above).
- Decide whether Lean's row language needs a `NoOp` constructor; no expansion emits one.
- The non-blocking CI job in `.github/workflows/expansion-parity.yml` has not run yet.
