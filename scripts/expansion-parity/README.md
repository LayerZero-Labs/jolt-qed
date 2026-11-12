# Expansion parity driver (T1 and I0(a))

This driver runs Jolt's production bytecode expansion on a fixed set of source instructions and writes the final rows as JSON.
It also checks Jolt's two expansion fixtures, the allocator state after each expansion, the operand templates of every registered inline, and which virtual registers each inline reads before writing.
From the templates it generates `JoltBytecode/Inlines/Generated/<Name>.lean`.
The plan is in `docs/inline-precompiles.md` (section 5.1 and the T1 and I0 rows of section 7).

## Running it

```
JOLT_DIR=~/claude-work/jolt-inline-pin-a6b6 scripts/expansion-parity/run.sh [WORK_DIR] [options]
```

`WORK_DIR` defaults to `~/claude-work/expansion-parity-work`.
`run.sh` calls `build.sh WORK_DIR`, then runs the driver with `--out WORK_DIR/out` and `--lean-root` set to this repository.
The driver exits with status 0 when every check passes, 1 when a check fails, and 2 when it cannot run.

`build.sh WORK_DIR` assembles the crate in `WORK_DIR/expansion-parity` the way `scripts/difftest/build.sh` assembles `jolt-trace`.
It fills `@JOLT_DIR@` in `Cargo.toml.in`, links `src/`, and copies Jolt's `Cargo.lock` and `rust-toolchain.toml`.
It also copies Jolt's `[patch]` tables with absolute paths, because the crate is its own workspace and would otherwise take arkworks from crates.io instead of Jolt's fork.
`EXPANSION_PARITY_FEATURES` passes cargo features to the build.
The one feature, `zicsr-remaining`, adds encodings for CSRRC, CSRRWI, CSRRSI and CSRRCI and a T1 group `csr`, which runs every Zicsr kind on each of the six CSRs Jolt models with several rd and rs1 values; enable it only against a Jolt checkout whose decoder has these kinds, such as a16z/jolt#2384.

Driver options:

| Option | Default | Meaning |
|---|---|---|
| `--jolt-dir DIR` | `$JOLT_DIR` | Jolt checkout whose fixtures the driver reads; it must be the checkout the binary was built against |
| `--out DIR` | required | Output directory |
| `--lean-root DIR` | none | Repository root to write the generated Lean into; without it the driver writes no Lean |
| `--seed N` | `1949392621` | Seed of the random group |
| `--random-per-kind N` | 6 | Random cases per decoder kind |
| `--lean-chunk N` | 100 | Rows per chunk in the generated Lean; 0 writes one nested `Program` term |
| `--skip-uniformity` | off | Skip the exhaustive uniformity check (the check then fails) |

`run.sh --no-lean` drops `--lean-root`.

## Outputs

`WORK_DIR/out/rows.jsonl` has one line per expansion, in the schema of the I0 design note.
Kind names are `SourceInstructionKind::name` and `JoltInstructionKind::name` (for example `ADDI`, `VirtualXORROTW16`).
Circuit flags are listed in the order of Jolt's `CIRCUIT_FLAGS`, instruction flags in enum order, and the lookup table is the `LookupTableKind` variant name.
The `error` field holds the `Debug` form of `ExpansionError`.

`WORK_DIR/out/inline_templates.json` has, per registered inline, the template of the `normal` case and of the `rd_zero` case when Jolt accepts rd = x0.
Each register field is `{"param": "rs1" | "rs2" | "rs3"}` or `{"lit": n}`.

`WORK_DIR/out/summary.json` has every check with its result and counts, the expansion-error count per group, and per inline its rd = x0 status, row counts, write-before-read result and write set.
The driver also prints a short summary.

## T1 rows

| Group | Cases |
|---|---|
| `golden` | The 360 inputs of `crates/jolt-program/src/expand/fixtures/main_expand_parity_hashes.json` |
| `aliased` | Every source kind except `Inline` with rd = rs1 = rs2 = x7 |
| `rd_zero` | Every source kind except `Inline` with rd = x0, rs1 = x5, rs2 = x6 |
| `rs1_zero` | Every source kind except `Inline` with rd = x7, rs1 = x0, rs2 = x6 |
| `random` | Six seeded cases per decoder kind and one per other kind: random registers, immediates, compression and even addresses at or above 0x8000_0000 |
| `native_kind` | Every source kind except `Inline` once, with rd = x9, rs1 = x5, rs2 = x6 |
| `inline_fixture` | The four scenarios of Jolt's inline fixture for each of the 27 inlines |

Every row comes from `expand_instruction_with_provider` with `TracerInlineExpansionProvider` and `RV64IMAC_JOLT_ALL_INLINES`, with a fresh `ExpansionAllocator` per case.

For the golden group the driver first repeats Jolt's own test: `expand_instruction` (no inline provider) with `RV64IMAC_JOLT` and a fresh allocator, hashed as `hex(sha256(serde_json::to_vec(rows)))`.
Any hash that differs from the fixture fails the check.
A second check requires the production rows to equal those rows, so the emitted rows are the ones the fixture pins.

For kinds that Jolt's decoder produces, the driver builds each case by encoding a 32-bit word and decoding it with `jolt_program::image::decode::decode_instruction`.
The operands and immediate are therefore normalized exactly as the decoder normalizes them (for example SRAI's immediate is `0x400 | shamt`, and CSR immediates are sign-extended).
The driver fails if a word decodes to a different kind.
The decoder never produces `NoOp`, `Unimpl`, `ANDN`, or most `Virtual*` source kinds.
The driver builds those cases directly from a `SourceInstructionRow` with all three registers present; their case names end in `/direct`.
A direct ANDN case has immediate 0, as an R-type word from the decoder would.
In the random group, the other direct cases keep their random immediate.

The flags come from `jolt_riscv::Flags`, the lookup table from `InstructionLookupTable::<64>::lookup_table`, and the RAF flag from `jolt_witness::witnesses::InstructionRafFlag::extract`.
For the RAF flag the driver builds the `JoltTraceRow` that Jolt would record: a RAM read for a `Load` row, a RAM write for a `Store` row, and no RAM access otherwise.
`JoltTraceRow::new` rejects a NoOp that carries sequence or compression metadata, so the driver clears that metadata on NoOp rows before building their trace row.
The RAF flag depends only on the circuit flags, which depend only on the kind.

## Allocator restoration

`ExpansionAllocator` derives `Debug` and `Clone` but not `PartialEq`.
Its `Debug` output prints all three fields (`allocated`, `pending_clearing_inline`, `recursion_depth`), so the driver compares `format!("{:?}", allocator)` with the `Debug` string of `ExpansionAllocator::new()`.
It checks this after every successful fresh expansion, after every inline expansion of the uniformity check, and after each step of the shared run.

The shared run expands every case above, in order, through one allocator.
After each expansion the allocator must equal a fresh one, and the rows must equal the fresh-allocator rows.
When the allocator is not fresh, the driver records the case and the allocator state and continues with a fresh allocator.
Shared rows are in `rows.jsonl` with `"allocator": "shared"` and case names ending in `@shared`.

## Inline checks

The driver links every `jolt-inlines/*` crate with feature `host` and requires 27 registrations.

**Fixture hashes.**
The driver recomputes `jolt-inlines/fixtures/fixtures/registered_inline_expand_parity_hashes.jsonl` as `compute_cases` does: registrations sorted by (opcode, funct7, funct3, name), four scenarios, a fresh allocator each.
It compares the name, registration metadata, row count and hash of each line.
A line with an `error` field (added in a16z/jolt#2414) requires Jolt to return an error whose `Display` text equals the field, with row count 0 and an empty hash.

**Templates.**
For each inline and allocation case the driver expands the inline with operands A = (rs1, rs2, rs3) = (x11, x12, x13) and B = (x21, x22, x23) at address 0x8000_0000, where rs3 is the source rd.
In the `rd_zero` case rd is x0 and rs3 is not a parameter.
A register field equal to A's and B's value of the same operand is that parameter; a field equal under A and B is a literal; anything else fails.
In the `rd_zero` case the temporary that Jolt's rd = x0 rewrite allocates is therefore a literal.
Kind, immediate, address and sequence metadata must agree between A and B.

**Exhaustive operand uniformity.**
For every triple (rs1 in 0..31, rs2 in 0..31, rs3 in 1..31 for `normal`; rs1 and rs2 in 0..31 with rd = x0 for `rd_zero`) the driver expands the inline and compares every row, field by field, with the template instantiated at that triple.
It runs the triples on all cores with rayon and reports the time.
For an inline whose rows depend on register identity it reports the first differing triple and row.

**Write-before-read.**
On the rows of operand triple A, a row reads every register in a present `rs1` or `rs2` field and writes the register in a present `rd` field.
Every read of a pool register (vr48..127) must follow a write of that register by an earlier row of the same sequence.
The check gates the twelve in-scope inlines (SHA256_INLINE, SHA256_INIT_INLINE, KECCAK256_INLINE, KECCAK256_ABSORB_PERMUTE_INLINE, BLAKE2_INLINE and the seven SECP256K1 inlines) and is reported for the other 15.
The driver also reports reads of the instruction temporaries vr40..47 before a write; in the `rd_zero` case such a read is the read of rd that a16z/jolt#2414 rejects.

The read and write slots follow the operand fields because Jolt's register checking reads every present operand: `JoltTraceRow` captures `integer_operands`, which for these kinds are the row's own operands.
The table lists the row kinds that the 27 inlines use at the pin, with the flags that say how each operand value is used (from `crates/jolt-riscv/src/instructions/`).

| Row kind | Reads | Writes | Operand-use flags |
|---|---|---|---|
| ADD, ADDW, SUB, SUBW, MUL, MULW, MULHU, AND, ANDN, OR, XOR, SLTU | rs1, rs2 | rd | LeftOperandIsRs1Value, RightOperandIsRs2Value |
| VirtualXORROT16/24/32/63, VirtualXORROTL1, VirtualXORROTW6/7/8/12/16/19/22, VirtualPextSigned | rs1, rs2 | rd | LeftOperandIsRs1Value, RightOperandIsRs2Value |
| ADDI, ADDIW, ANDI, XORI, VirtualMULI, VirtualROTRI, VirtualROTRIW, VirtualSRAI, VirtualSRLI, VirtualSRLIW, VirtualWindowMaskW | rs1 | rd | LeftOperandIsRs1Value, RightOperandIsImm |
| VirtualRev8W, VirtualZeroExtendWord | rs1 | rd | LeftOperandIsRs1Value |
| LUI | none | rd | RightOperandIsImm |
| VirtualAdvice | none | rd | Advice circuit flag |
| LD | rs1 (address) | rd | Load circuit flag, RightOperandIsRdWriteValue |
| VirtualLoadW | rs1 (address) | rd | Load circuit flag, LeftOperandIsRs1Value, RightOperandIsImm |
| SD | rs1 (address), rs2 (value) | none | Store circuit flag |
| VirtualAssertEQ, VirtualAssertLTE | rs1, rs2 | none | LeftOperandIsRs1Value, RightOperandIsRs2Value |

`summary.json` repeats this table, computed from the rows, under the `write_before_read_in_scope` check.

**Write sets.**
Per inline and case, `summary.json` lists the architectural registers written (parameters and literals), the written registers in vr32..39, vr40..47 and the pool, and the number of load and store rows.

## Generated Lean

The driver writes one file per inline, `JoltBytecode/Inlines/Generated/<Name>.lean`, and `JoltBytecode/Inlines/Generated.lean`, which imports all 27.
`<Name>` is the registration name without a trailing `_INLINE`, split at `_`, with each part's first character upper case and the rest lower case: `SHA256_INIT_INLINE` gives `Sha256Init` and `SECP256K1_MULQ` gives `Secp256k1Mulq`.
The definitions use the same name with a lower-case first character (`sha256Init`).

In `namespace JoltISA.Inlines.Generated` each file defines:

- `<name>RowsAuto (rs1 rs2 rs3 : regidx) : JoltISA.Program` for the `normal` case;
- `<name>RowsAutoRdZero (rs1 rs2 : regidx) : JoltISA.Program` when Jolt accepts rd = x0;
- with chunking, `<name>RowsAuto[RdZero]Chunk<k>` of type `List JoltISA.Instr` per chunk, `<name>RowsAuto[RdZero]List` as their concatenation, and `<name>RowsAuto[RdZero] := JoltISA.Program.seq (…List …)`.

A parameter that no row uses is named with a leading underscore.
Rows are raw `JoltISA.Instr` constructors with operands in the order of `ExpansionsAutomated.lean`: `rd` is the destination, then `rs1`, then `rs2`.
Register parameters render as `(.xreg rsN)`, architectural literals as `(.xreg (regidx.Regidx n))`, and virtual literals as `(.vreg (BitVec.ofNat 7 n))`.
A `BitVec 64` immediate is the Rust immediate modulo 2^64, a `BitVec 128` immediate is the Rust immediate modulo 2^128, and a `Nat` immediate must be non-negative.
Loads and stores use the `.normal` fault class with `E_Load_Addr_Align` for loads and `E_SAMO_Addr_Align` for stores, as the plain load and store helpers in `ExpansionsAutomated.lean` do.

Inlines with `VirtualAdvice` rows take `(advice : Nat → BitVec 64)`, and the k-th `VirtualAdvice` row in row order (from 0) writes `advice k`.
A function indexed by advice-row position keeps the signature the same size for every inline, and the advice lemmas of section 5.3 can state the honest value of each position.

**Chunking.**
The generator writes 100-row chunks by default.
At a6b6dc717 the unchunked form (one nested `.instr … <|` term per definition) fails on `KECCAK256_ABSORB_PERMUTE_INLINE` (3,121 rows) with "maximum recursion depth has been reached" at row 250.
With 100-row chunks the file elaborates under the default limits: `lake env lean` on it took 34 s of wall time and 15.5 s of CPU time on a machine with load average 30.
The generated files never set `maxRecDepth`, `maxHeartbeats` or any other option.
