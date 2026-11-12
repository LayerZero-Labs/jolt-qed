# Decoder sweep: Jolt's decoder against Lean's `joltDecode` (T2)

Date: 2026-11-12 (Track T phase T2 of `docs/inline-precompiles.md`).
Jolt: a16z/jolt#2384 at `580084fcfad4788ebf48413a92dd640ca090c45f` (primary run), and the Track T pin `a6b6dc7177ec5ea5a3c60bd5cea4409c07ca6dc5` (second run).
Lean and the comparator: branch `inline/t2-decoder-sweep` at `08f56a2f0` (based on `inline/t1-driver` at `b648846`); later commits on the branch change only this report.
How to run it: `scripts/expansion-parity/DECODER-SWEEP.md`.

## Result

At `580084fcf` the Lean decoder agrees with Jolt's decoder on every input the sweep tried: 0 mismatches.
Every disagreement in acceptance falls into one of two explained classes, neither of which reaches a committed RISC-V row:

- Jolt-only kinds (93,394 words): Jolt decodes its custom opcodes 0x0b, 0x2b and 0x5b, and `joltDecode` returns `none` for them.
- Rejected by Jolt's expansion (687,120 words): Jolt's decoder accepts a Zicsr instruction at any CSR address, Jolt's expansion then rejects every address outside six, and `joltDecode` rejects the same addresses at decode.

At the pin `a6b6dc717` the comparison has 672 mismatches, all of one kind: Lean decodes CSRRC, CSRRWI, CSRRSI and CSRRCI, which Jolt decodes only from #2384.
This is expected, because Lean's system decoding transcribes #2384.

The mutation check detects all 12 corruptions it makes.

## What this covers and what it does not

The parcel comparison is exhaustive: it covers all 65,536 16-bit parcels.

The word comparison is a sweep, not an exhaustive comparison.
Lean's decoder runs in the interpreter (no compiled executable can link this library), which rules out all 2^32 words.
The sweep groups words into selector classes: opcode (the 32 opcodes with low bits `0b11`), funct3 and bits 31..25, and for SYSTEM also bits 24..20, which are part of the CSR address.
Every class is swept with 42 operand patterns (28 for SYSTEM, whose free operand bits are only rd and rs1): zero, all ones, every combination of zero and all-ones operand fields, each operand bit alone, each operand bit cleared from all ones, and 4 seeded random values.
That is 2,250,752 words.

The argument that the sweep stands for every word has two halves, and only the first is machine-checked.

1. Jolt's side is checked exhaustively in Rust.
   The driver decodes all 2^30 words with low bits `0b11` (1,073,741,824 words, 310,321,155 accepted) and verifies, for every selector class, that:
   - the decoded kind, or the rejection, depends on the operand bits only through which operand fields are zero (no violations);
   - every accepted word in a class has the same kind, and its output fields (rd, rs1, rs2, imm) are affine over GF(2) in the operand bits (all 310,321,155 accepted words checked, none skipped, no violations).
   The check fails unless every accepted word was checked, so a class with a second accepted kind cannot pass with words left out.
   The sweep's patterns contain every zero/non-zero combination of the operand fields and a basis of single-bit differences, so in each class they determine Jolt's result on every word.
   This ran at `580084fcf` in 273 seconds; the pin run skipped it.
2. Lean's side is argued by reading `joltDecode` (`JoltBytecode/Decode/Jolt.lean:64`), not checked.
   It extracts fixed bit ranges, and its only operand-dependent tests are equalities of whole fields with zero (LR's `rs2 = 0` at lines 152-153, and the exact ECALL, EBREAK and MRET words at lines 176-178) and the CSR address at line 51, which lies in the SYSTEM selector class.
   Under this reading Lean's result has the same structure as Jolt's, and the sweep determines it too.

The sweep decodes every word at one address (0x80000000).
`RV64IMAC_JOLT` includes the C extension, so Jolt's decoder does not check alignment, and the address only reaches the source row.

The driver builds `jolt-program` with its default features.
Jolt's `field-inline` feature adds a decoder for opcode 0x7b (`decode.rs:87-88`), which this sweep does not exercise; Lean has no model of those instructions.

## How each input is classified

For each input the comparator `JoltTests/DecoderSweep/Main.lean` compares Jolt's result with `joltDecode w 0`.

- Both reject.
- Both accept: T1's `SourceView.toLean` maps Jolt's record to `.riscv j`, and `joltDecode` returns `i` with `eraseAdvice i = withOrdering aq rl j`.
  Jolt's record carries neither the division advice nor the atomic `aq`/`rl` bits, so the comparison settles them separately.
  `eraseAdvice` (`Main.lean:64`) sets the advice of `i` to 0; `ImageDecoded` quantifies the advice existentially, so comparing at advice 0 loses nothing.
  `withOrdering` (`Main.lean:80`) sets the ordering bits of `j` from the word, `aq` from bit 26 and `rl` from bit 25, so a Lean decoder that dropped or swapped them would be reported.
- Jolt-only kind: Jolt accepts with a kind that `toLean` maps to a `.jolt` source instruction, a kind in T1's `noLeanSourceKinds`, or `Inline` (`joltOnlyDecodeKinds`, `Main.lean:159`), and `joltDecode` returns `none`.
- Rejected by Jolt's expansion: see the next section (`rejectedAtExpansion`, `Main.lean:176`).
- Anything else is a mismatch.

A parcel is compared in two steps: `joltUncompress` must give the same 32-bit word as Jolt's `uncompress_rv64_instruction`, and then the two decoders must agree on that word (Jolt decodes it with `is_compressed = true`).

## Results at `580084fcf`

| Inputs | Count | Both reject | Both accept | Jolt-only kind | Rejected by Jolt's expansion | Mismatches |
|---|---:|---:|---:|---:|---:|---:|
| Compressed parcels (low bits not `0b11`) | 49,152 | 10,601 | 38,551 | 0 | 0 | 0 |
| Parcels with low bits `0b11` | 16,384 | 16,384 | 0 | 0 | 0 | 0 |
| 32-bit words | 2,250,752 | 1,195,401 | 274,837 | 93,394 | 687,120 | 0 |

The words that both decoders accept cover 94 kinds; the parcels cover 23.
Every one of the 49,152 compressed parcels uncompresses to the same word in both.

### Jolt-only kinds

Jolt's `decode_instruction` (`crates/jolt-program/src/image/decode.rs:22`) accepts three custom opcodes that Lean's decoder does not model.

| Kind | Words | Jolt source |
|---|---:|---|
| `Inline` (opcodes 0x0b and 0x2b, every funct3 and funct7) | 86,016 | `decode.rs:85` |
| `VirtualAssertEQ` (0x5b, funct3 1) | 5,376 | `decode_custom`, `decode.rs:210-229` |
| `VirtualHostIO` (0x5b, funct3 2, rd = 0) | 1,792 | same |
| `AdviceLB`, `AdviceLH`, `AdviceLW`, `AdviceLD`, `VirtualRev8W` (0x5b, funct3 0) | 42 each | same |

These are not decoder disagreements for the whole-run theorem.
`ImageDecoded` (`JoltConstraints/WholeRun/Decoded.lean:316`) constrains only rows whose instruction is `.riscv i`; inline rows are covered by the inline templates, and the custom instructions by their own `JoltCustomInstruction` constructors.
Jolt's decoder accepts every 0x0b and 0x2b word, whatever its funct3 and funct7.
Whether an inline with that key is registered is checked later, at expansion.

### Zicsr instructions rejected at expansion

Jolt's `decode_system` (`decode.rs:195-207`) accepts CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI and CSRRCI at any of the 4,096 CSR addresses.
Jolt's expansion then rejects every address that `virtual_register_for_csr` (`crates/jolt-program/src/expand/allocator.rs:59-68`) does not map, with `ExpansionError::UnsupportedCsr` (`expand/control_flow/csrrw.rs:15`, `csrrs.rs:14`, `csrrc.rs:14`, `csr_immediate.rs:13` and `:56`).
The mapped addresses are 0x300, 0x305, 0x340, 0x341, 0x342 and 0x343.
Lean's `csr` (`JoltBytecode/Decode/Jolt.lean:51`) accepts exactly these six, so `joltDecode` rejects the other addresses at decode.

The two pipelines therefore reject the same words, at different stages.
A program image with such a word fails Jolt's expansion and yields no committed row, so `ImageDecoded` does not need to cover it.
Jolt's expansion reads the address as `imm & 0xfff` (`csr_address`, `expand/operands.rs:46`), and Jolt's record holds the sign-extended 12-bit field as its immediate.
The comparator counts a word in this class only when all of these hold: its kind is one of the six Zicsr kinds; its immediate is a sign-extended 12-bit value whose low 12 bits equal the word's bits 31..20; that address is outside the six; and the same record at address 0x300 maps to a Lean instruction.
A record with any other immediate, for example one whose masked address is supported, is a mismatch.
At the six supported addresses the two decoders agree on all forms (168 words per form, in the "both accept" count).

## Results at the pin `a6b6dc717`

| Inputs | Count | Both reject | Both accept | Jolt-only kind | Rejected by Jolt's expansion | Mismatches |
|---|---:|---:|---:|---:|---:|---:|
| Compressed parcels | 49,152 | 10,601 | 38,551 | 0 | 0 | 0 |
| Parcels with low bits `0b11` | 16,384 | 16,384 | 0 | 0 | 0 | 0 |
| 32-bit words | 2,250,752 | 1,653,481 | 274,165 | 93,394 | 229,040 | 672 |

The 672 mismatches are CSRRC, CSRRWI, CSRRSI and CSRRCI at the six supported addresses, 168 words each.
Lean decodes them (`Jolt.lean:181-184`); the pin's `decode_system` (`decode.rs:195-204` at `a6b6dc717`) accepts only funct3 1 and 2 and rejects the rest with "unsupported system instruction".
For example, word `30003073` is `CSRRC x0, mstatus, x0` in Lean and an error in Jolt.
Lean follows #2384 here on purpose, as T1 does; the mismatches disappear at `580084fcf`.
Outside the system opcode the per-class counts of the two runs are identical.

## Mutation check

`DECODER_SWEEP_ARGS="mutation OUT"` corrupts one input of each shape in memory and checks that the comparator reports a mismatch.
At `580084fcf` it detects all 12:

- rd changed, immediate changed, kind changed;
- an accepted word turned into an error, and a rejected word turned into ADDI;
- a supported CSR address changed to an unsupported one (0x301), and an unsupported one changed to mstatus;
- for a word rejected at expansion, its immediate moved outside the 12-bit range (plus 0x1000), and its address changed to an unsupported address other than the word's; these check the boundary of the expansion class;
- for an AMO word, Lean's `aq` bit flipped, and Lean's `rl` bit flipped;
- an uncompressed word changed.

## CI

`.github/workflows/decoder-sweep.yml` checks out a16z/jolt at `580084fcf`, builds the driver with the `zicsr-remaining` feature, runs the sweep with its exhaustive check, builds `JoltTests.DecoderSweep.Main`, and runs the comparison and the mutation check.
The job fails on any mismatch, on a failed exhaustive check and on a missed mutation.
It is blocking because the comparison is clean at that commit.
It had not run in CI when this report was written.

## Timing

Local runs on a shared, heavily loaded Apple Silicon machine:

- Driver at `580084fcf`, including the incremental Rust build: 324 seconds wall time, of which the exhaustive check took 273 seconds.
- Lean comparison of all 2,316,288 inputs: 4 minutes 6 seconds (42 minutes in an earlier run under heavier load).
- Mutation check: 3 minutes 7 seconds, mostly spent reading the input files.
- `lake build JoltTests.DecoderSweep.Main` after changing only the comparator: about 5 minutes; the first build on a populated cache took about 13 minutes.
