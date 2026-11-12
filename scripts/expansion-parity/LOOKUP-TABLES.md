# lookup-tables: Jolt's lookup tables against a computable Lean twin

This check (T4 of `docs/inline-precompiles.md`, section 7) compares Jolt's lookup tables with the Lean tables of `JoltConstraints/lookup_table.lean`.
On the Jolt side the emitter evaluates `LookupTableKind::<64>::materialize_entry` (`crates/jolt-lookup-tables/src/tables/mod.rs`) at chosen indices.
On the Lean side the comparator evaluates `LookupTables.lookupTableEntryNat` (`JoltTests/LookupTables/Twin.lean`), a computable copy of `lookupTableEntry` with values in `Nat`.
The theorem `LookupTables.lookupTableEntry_eq_twin` proves that `lookupTableEntry` in any field is the cast of the twin.
The check samples indices and does not prove agreement at every index.
The results are in `reports/2026-11-11-lookup-table-vectors.md`.

## Running it

```
JOLT_DIR=~/claude-work/jolt-t2-580084 EXPANSION_PARITY_FEATURES=zicsr-remaining \
  scripts/expansion-parity/run-lookup-tables.sh WORK_DIR [--seed N] [--random-per-table N]
lake build JoltTests.LookupTables.Main
LOOKUP_TABLES_ARGS="compare WORK_DIR/out WORK_DIR/report" lake env lean JoltTests/LookupTables/Run.lean
LOOKUP_TABLES_ARGS="mutation WORK_DIR/out" lake env lean JoltTests/LookupTables/Run.lean
```

`run-lookup-tables.sh` calls `build.sh WORK_DIR`, which builds every binary of the crate, and then runs `lookup-tables --jolt-dir "$JOLT_DIR" --out WORK_DIR/out`.
`EXPANSION_PARITY_FEATURES=zicsr-remaining` is needed at a16z/jolt#2384 for the other driver binary, not for this one.
The emitter exits with 0 when every table was evaluated without a panic, with 1 when an entry panicked and with 2 when it cannot run.
The comparator's `#eval` throws on any failure, and `lean` then exits with a nonzero status.

Emitter options:

| Option | Default | Meaning |
|---|---|---|
| `--out DIR` | required | Output directory |
| `--jolt-dir DIR` | `$JOLT_DIR` | Jolt checkout, used only to record its commit |
| `--seed N` | `1949589229` (`0x74345eed`) | Seed of the random sample |
| `--random-per-table N` | 2000 | Random indices per table |

## Outputs

`OUT/lookup_vectors.jsonl` has one line per (table, index): `{"table": …, "index": …, "value": …, "class": "edge" | "random"}`.
The table is the `LookupTableKind` variant name (for example `VirtualXORROTW16`), and the index (a `u128`) and the value (a `u64`) are decimal strings.

`OUT/lookup_summary.json` has the Jolt commit, the seed, the number of random indices per table, the Rust variant names in enum order, per table its index family and its edge and random counts, the total, any panics, and the run time.

The comparator writes `REPORT/lookup-mismatches.jsonl` (one line per disagreeing vector, with the Rust and Lean values, or per vector whose table has no Lean constructor) and `REPORT/lookup-summary.txt` (per-table counts, name gaps, timing).

## Which indices

The emitter lists the tables with `LookupTableKind::<64>::iter()` and checks that each variant's `index()` equals its position.
A `match` without a wildcard assigns each variant an index family.
A variant added to Jolt therefore fails to compile until it is classified.

Every table gets these edge indices:

- 0, 1, 2, 2^64 − 1, 2^64, 2^127, 2^128 − 1 and every 2^i for i < 128;
- `interleave_bits(x, y)` (Jolt's own function) for x and y in 0, 1, 2, 2^31 − 1, 2^31, 2^32 − 1, 2^32, 2^63 − 1, 2^63, 2^64 − 1.

Each family adds indices that exercise its case split:

| Family | Tables | Extra edge indices |
|---|---|---|
| `IndexShift` | Pow2, Pow2W, ShiftRightBitmask, ShiftRightBitmaskW, WindowMaskB/H/W, AddressOffsetB/H/W | every shift amount 0..63 in the low bits (with zero, all-ones and patterned high bits) and as the right operand y, plus y equal to the 64-bit and 32-bit right-shift bitmasks |
| `ShiftData` | ShiftDataB/H/W | as `IndexShift` |
| `ShiftBitmask`, `ShiftBitmaskW` | VirtualSRL, VirtualSRA, VirtualROTR; VirtualSRLW, VirtualSRAW, VirtualROTRW | as `IndexShift`, operands of both signs, and y = 0 and every bitmask for signed and patterned x |
| `IndexSigned`, `NegateIf` | SignMask, LowerHalfWord, SignExtendWord; VirtualNegateIf | operand pairs of both signs (64-bit and 32-bit), and each operand alone with bit 127 and patterned high bits |
| `Compare` | the seven comparison tables (Equal, NotEqual, the signed and unsigned orders) | operand pairs of both signs, and equal and adjacent operands |
| `DivisorX`, `DivisorY` | ValidDiv0; ValidUnsignedRemainder | a zero divisor in either operand position, and equal and adjacent operands |
| `Bitwise` | And, Andn, Or, Xor, VirtualXORROT*, VirtualXORROTW*, VirtualXORROTL1 | patterned operand pairs and each single bit against a pattern |
| `Pext` | Pext, PextSigned | operand pairs of both signs, and single-bit, contiguous, bitmask and scattered masks y |
| `Index` | RangeCheck, RangeCheckAligned, UpperWord, MulUNoOverflow, VirtualRev8W | signed operands with high words 0, 1, 2^64 − 1 and 2^63 |

The random sample has `--random-per-table` indices per table from a SplitMix64 generator seeded with the seed and the table's position.
Indices are uniform `u128` values, except that for the six shift and rotate tables every second index has the bitmask-shaped right operand of Jolt's own test generators (`gen_bitmask_lookup_index` and `gen_bitmask_w_lookup_index` in `tables/test_utils.rs`).

## The twin

`lookupTableEntryNat` copies each table of `lookup_table.lean` with the cast to the field removed: the four sum tables become the same sum in `Nat`, an `if … then 1 else 0` becomes the same `if` in `Nat`, and a final `(v.toNat : F)` becomes `v.toNat`.
Every bit operation is unchanged.
`lookupTableEntry_eq_twin` is then proved by unfolding and the cast lemmas `Nat.cast_sum`, `Nat.cast_ite` and `Nat.cast_pow`, with no argument about bits.
An agreement between Jolt and the twin at an index is therefore an agreement between Jolt and `lookupTableEntry` at that index, in any field.

## Mutation check

`mutation` adds one (modulo 2^64) to the value of the first vector of each table, in memory, and checks that the comparison reports each corruption.
It also renames one vector's table to an unknown name and checks that the comparison flags the vector.
