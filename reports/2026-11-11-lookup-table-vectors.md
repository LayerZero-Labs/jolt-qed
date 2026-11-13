# Lookup-table vectors: T4

Date: 2026-11-12.
This report gives the T4 check of `docs/inline-precompiles.md` (section 7).
At a16z/jolt#2384 head `580084fcf`, Jolt's `materialize_entry` agrees with the Lean tables at all 162,551 sampled (table, index) pairs, across all 55 tables, with no name gap.

This check samples entries and does not prove agreement at every index.
The proof covers only "twin = Lean table": `lookupTableEntry_eq_twin` shows that `lookupTableEntry` in any field is the cast of the computable twin `lookupTableEntryNat` at every index.
Agreement with Jolt holds only at the sampled indices.

## Revisions

- jolt-qed: branch `inline/t4-lookup-tables`, on `inline/t1-driver` at `b648846`.
  I ran the results below with the emitter of commit `b8be11c`, the twin of commit `41fff36`, and the comparator of commit `02f6f84`, which added the coverage checks and the four-case mutation run.
- Jolt: a16z/jolt#2384 (branch `feat/zicsr-remaining-forms`) at `580084fcfad4788ebf48413a92dd640ca090c45f` (`580084fcf`), the commit that the expansion-parity and decoder-sweep jobs use.
  Its `crates/jolt-lookup-tables` is byte-identical to the one at the Track T pin `a6b6dc717`: `git diff a6b6dc717 580084fcf -- crates/jolt-lookup-tables` is empty, and both commits have tree `080fd63f` for that directory.
- Toolchain: `leanprover/lean4:v4.35.0`; Rust from Jolt's `rust-toolchain.toml`, release profile (wrapping arithmetic, as in Jolt's own release profile).

`JoltConstraints/lookup_table.lean` cites most tables by path without a commit, `addressOffsetTableEntry` (line 172) and `lookupTableEntry` (line 560) at `c6703570`, and `virtualXorRotL1TableEntry` (line 87) at a fork URL, `https://github.com/abiswas3/jolt/tree/main/…/virtual_xor_rotl1.rs`.
`LookupTableKind` (`JoltConstraints/witness.lean:57`) cites `c6703570` as well.
The vectors check `580084fcf`, whose lookup-table crate equals the pin's; they do not check `c6703570` or the fork.

## What is compared

The Rust emitter (`scripts/expansion-parity/src/bin/lookup-tables.rs`) lists the tables with `LookupTableKind::<64>::iter()` (`crates/jolt-lookup-tables/src/tables/mod.rs:137`, which derives `strum::EnumIter`) and evaluates `LookupTableKind::<64>::materialize_entry` at:

- edge indices common to every table: 0, 1, 2, 2^64 − 1, 2^64, 2^127, 2^128 − 1, every 2^i for i < 128, and `interleave_bits(x, y)` for x and y in 0, 1, 2, 2^31 − 1, 2^31, 2^32 − 1, 2^32, 2^63 − 1, 2^63, 2^64 − 1;
- edge indices for each table's case split: every shift amount 0..63 in the low bits and in the right operand y for the shift, rotate, window, pow2, shift-data and address-offset tables; bitmask-shaped y for the shift and rotate tables; zero divisors in either operand position for ValidDiv0 and ValidUnsignedRemainder; operands of both signs for the sign, comparison, shift and negate tables; single-bit, contiguous and scattered masks for Pext and PextSigned;
- 2,000 seeded random indices per table (seed `1949589229`); for the six shift and rotate tables every second random index has the bitmask-shaped y of Jolt's test generators.

`scripts/expansion-parity/LOOKUP-TABLES.md` lists the index families in full.
The emitter assigns each variant a family in a `match` with no wildcard.
A new Jolt variant therefore fails to compile until it is classified.
It also checks that each variant's `index()` equals its position in `iter()`.

The Lean comparator (`JoltTests/LookupTables/Main.lean`) maps each Rust variant name to the `LookupTableKind` constructor of the same name, evaluates `lookupTableEntryNat` at the index and compares the value.

## How to run it

```
JOLT_DIR=<a16z/jolt checkout at 580084fcf> EXPANSION_PARITY_FEATURES=zicsr-remaining \
  scripts/expansion-parity/run-lookup-tables.sh WORK_DIR
lake build JoltTests.LookupTables.Main
LOOKUP_TABLES_ARGS="compare WORK_DIR/out WORK_DIR/report" \
  lake env lean JoltTests/LookupTables/Run.lean
LOOKUP_TABLES_ARGS="mutation WORK_DIR/out" \
  lake env lean JoltTests/LookupTables/Run.lean
```

The CI job `.github/workflows/lookup-tables.yml` runs the same steps at `580084fcf` and fails on any mismatch, name gap, coverage error or missed mutation.
When I added it, the job had been run locally only, not in CI.

## The twin and the theorem

`JoltTests/LookupTables/Twin.lean:381` defines `LookupTables.lookupTableEntryNat : LookupTableKind → Fin (2 ^ 128) → Nat`.
Each table's twin copies the definition in `lookup_table.lean` with the cast removed: the four sum tables (And, Or, Xor, VirtualXORROTL1) are the same sum over `Fin 64` in `Nat`, the `if … then 1 else 0` tables are the same `if` in `Nat`, and every table that ends in `(v.toNat : F)` ends in `v.toNat`.
No bit operation changes.
Every table could be written this way; none needed a change to an existing definition.

`JoltTests/LookupTables/Twin.lean:448`:

```lean
theorem lookupTableEntry_eq_twin {F : Type} [Field F] (t : LookupTableKind)
    (a : Fin (2 ^ 128)) :
    lookupTableEntry (F := F) t a = (lookupTableEntryNat t a : F)
```

The proof splits on `t`, unfolds both sides, and moves the cast with `Nat.cast_sum`, `Nat.cast_ite`, `Nat.cast_pow`, `Nat.cast_ofNat`, `Nat.cast_one` and `Nat.cast_zero`; for the `v.toNat` tables `dsimp only` closes the goal once both sides' `let`s and operand-pair `match`es are reduced.
It uses no `sorry`, `native_decide`, `decide +kernel`, `bv_decide`, and no `maxHeartbeats`, `maxRecDepth` or `synthInstance` option.
`lake build JoltTests.LookupTables.Twin` takes 8 to 10 seconds for the whole file.

```
#print axioms LookupTables.lookupTableEntry_eq_twin
'LookupTables.lookupTableEntry_eq_twin' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Results

The comparator reports 162,551 vectors, 0 value mismatches and 0 vectors with no Lean table.
Jolt has 55 variants and Lean has 55 constructors, with the same names.
No Rust variant lacks a Lean constructor, and no Lean constructor lacks a Rust variant.
No `materialize_entry` call panicked.

Per table, every checked vector agrees:

| Tables | Edge | Random | Checked (each) |
|---|---|---|---|
| RangeCheck, RangeCheckAligned, UpperWord, MulUNoOverflow, VirtualRev8W | 250 | 2000 | 2250 |
| And, Andn, Or, Xor, VirtualXORROTL1, VirtualXORROT32/24/16/63, VirtualXORROTW16/12/8/7/22/19/6 | 872 | 2000 | 2872 |
| Equal, NotEqual, SignedLessThan, SignedGreaterThanEqual, UnsignedLessThan, UnsignedLessThanEqual, UnsignedGreaterThanEqual | 309 | 2000 | 2309 |
| SignMask, LowerHalfWord, SignExtendWord, VirtualNegateIf | 299 | 2000 | 2299 |
| ValidDiv0, ValidUnsignedRemainder | 256 | 2000 | 2256 |
| Pow2, Pow2W, ShiftRightBitmask, ShiftRightBitmaskW, WindowMaskB/H/W, ShiftDataB/H/W, AddressOffsetB/H/W | 1188 | 2000 | 3188 |
| VirtualSRL, VirtualSRA, VirtualROTR, VirtualROTRW, VirtualSRLW, VirtualSRAW | 2062 | 2000 | 4062 |
| Pext, PextSigned | 2831 | 2000 | 4831 |

The comparison also checks the vectors against the emitter's summary (total count, and per table the edge and random counts); at `580084fcf` it finds 0 coverage errors.
The mutation check corrupts the vectors in memory and runs them through `compareVectors`, the function `compare` uses.
It detects all four corruptions: one value changed in each of the 55 tables (55 mismatches in 55 tables), one vector's table renamed, the last vector dropped, and all but the first vector of each table dropped.
I also changed one value in a copy of the vector file (RangeCheck at index 4, value 4 changed to 7): the comparator reported that one mismatch and `lean` exited with status 1.

## Mismatches and name gaps

None.

## Timing

Measured on a shared, loaded laptop (wall times).

| Step | Time |
|---|---|
| Emitter build (driver crate only, Jolt dependencies already built) and run | 15 s |
| Emitter evaluation of 162,551 entries | 0.4 s |
| `lake build JoltTests.LookupTables.Twin` | 8 to 10 s |
| `lake build JoltTests.LookupTables.Main` | 4 to 7 s |
| Comparator `compare`, end to end | 27 to 37 s (4 to 5 s reading, 14 to 16 s evaluating) |
| Comparator `mutation`, end to end (four comparison runs) | 70 s |

At 2,000 random indices per table the comparison runs in well under a minute.
I kept that default.
