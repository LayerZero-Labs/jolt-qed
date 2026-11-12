# decoder-sweep: Jolt's decoder against Lean's `joltDecode`

This check compares the decoder that builds Jolt's committed bytecode with the Lean decoder that the whole-run theorem assumes.
On the Jolt side it runs `jolt_riscv::uncompress_rv64_instruction` and `jolt_program::image::decode::decode_instruction` with the `RV64IMAC_JOLT` profile.
These are the functions `decode_elf` uses; the tracer's decoder is not involved.
On the Lean side it runs `Decode.joltUncompress` and `Decode.joltDecode` from `JoltBytecode/Decode/Jolt.lean`.
The results are in `reports/2026-11-11-decoder-sweep.md`.

## What is compared

- Every 16-bit parcel (65,536 inputs).
  Jolt uncompresses the parcel and decodes the result with `is_compressed = true`.
  The comparator checks that `joltUncompress` gives the same 32-bit word and that `joltDecode` agrees on that word.
- A sweep of 32-bit words.
  A word's selector class is its opcode (the 32 opcodes with low bits `0b11`), funct3 and bits 31..25, and for SYSTEM (`0x73`) also bits 24..20, which are part of the CSR address.
  In each class the sweep tries a fixed set of operand patterns over the remaining bits (rd, rs1 and rs2, or rd and rs1 for SYSTEM).
  The patterns are zero, all ones, every combination of zero and all-ones fields, each operand bit alone, each operand bit cleared from all ones, and four seeded random values.
- In Rust alone, every one of the 2^30 words with low bits `0b11`.
  For each class this exhaustive check verifies two properties of Jolt's decoder.
  First, the decoded kind (or the rejection) depends on the operand bits only through which operand fields are zero.
  Second, for the class's most common accepted kind, each output field (rd, rs1, rs2, imm) is an affine function over GF(2) of the operand bits.
  Together with the patterns above, these properties mean that the sweep's words determine Jolt's result on every word of the class.

The exhaustive check covers Jolt's side only.
Lean's side is argued from the definition of `joltDecode`: it reads fixed bit ranges, and its only operand-dependent cases are LR's `rs2 = 0` requirement, the CSR-address check and the exact ECALL, EBREAK and MRET words, all of which fall inside the sweep's patterns or selector classes.
The comparator does not prove this; the report states it as an argument.

## How a result is classified

For each input the comparator compares Jolt's result with `joltDecode w 0`:

- both reject;
- both accept: T1's `SourceView.toLean` maps Jolt's record to `.riscv j`, and `joltDecode` returns `i` with `i = j` once the division advice and the atomic `aq`/`rl` bits (which Jolt's record does not carry) are cleared;
- Jolt-only kind: Jolt accepts with a Jolt-specific kind (one `toLean` maps to `.jolt`, or one in T1's `noLeanSourceKinds`) and `joltDecode` returns `none`; `ImageDecoded` constrains only `.riscv` rows;
- rejected by Jolt's expansion: Jolt's decoder accepts a Zicsr instruction (CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI) at any CSR address, and Jolt's expansion then rejects it with `ExpansionError::UnsupportedCsr` unless the address is one of the six in `virtual_register_for_csr` (`crates/jolt-program/src/expand/allocator.rs`); `joltDecode` makes the same six-address check at decode and returns `none`.
  The comparator counts a word here only if its CSR address is outside the six and the same record at address 0x300 maps to a Lean instruction;
- otherwise a mismatch, grouped by cause.

## Running it

Build the driver and run the sweep (a16z/jolt#2384 needs the `zicsr-remaining` feature, as `build.sh` explains):

```bash
JOLT_DIR=<a16z/jolt checkout> EXPANSION_PARITY_FEATURES=zicsr-remaining \
  scripts/expansion-parity/run-decoder-sweep.sh WORK_DIR
```

The sweep writes `decoder_parcels.tsv`, `decoder_words.tsv` and `decoder_summary.json` to `WORK_DIR/out`.
It exits with 1 if the exhaustive check finds a class where the properties above fail, and with 2 if it cannot run.
Options: `--seed N`, `--random-patterns N` (default 4), `--skip-exhaustive`.

The driver builds `jolt-program` with its default features.
Jolt's `field-inline` feature adds a decoder for opcode 0x7b, which this sweep therefore does not exercise.

Then run the Lean comparator and its mutation check:

```bash
lake build JoltTests.DecoderSweep.Main
DECODER_SWEEP_ARGS="compare WORK_DIR/out WORK_DIR/report" lake env lean JoltTests/DecoderSweep/Run.lean
DECODER_SWEEP_ARGS="mutation WORK_DIR/out" lake env lean JoltTests/DecoderSweep/Run.lean
```

`compare` writes `decoder-summary.txt` and `decoder-mismatches.tsv` to `WORK_DIR/report` and fails on any mismatch.
`mutation` corrupts a few inputs in memory and fails unless the comparator reports each one.
The comparator runs in Lean's interpreter, because `LeanRV64D.lean` declares a root `main` and no `lean_exe` can link this library.

The CI workflow `.github/workflows/decoder-sweep.yml` runs these steps against a16z/jolt#2384 at `580084fcf` and fails on any mismatch.
At that commit the comparison is clean.
