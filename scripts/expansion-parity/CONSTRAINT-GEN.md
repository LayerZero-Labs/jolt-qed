# Constraint generation (T3)

`constraint-gen` links Jolt's own crates and writes three Lean files under `JoltConstraints/ConstraintGen/Generated/`.
It is ported from LayerZero-Labs/jolt-qed#56 (`dd6b7b87e`) and targets Jolt main `ff6fc656813d950565c9f6e1258b78bdaf0e60e8`.
The Cargo package contains only T3 and its flag-order/RAF helpers; it has no expansion, decoder-sweep, inline, lookup-vector or expansion-recipe driver.

| File | Contents | Jolt source |
| --- | --- | --- |
| `R1CS.lean` | 22 per-cycle R1CS rows over 40 variables; row 21 and the row list take the public panic bit | `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs` (`rv64_trace_constraints`) |
| `Relations.lean` | Four extractor relations with 14 claims: RAM and register read/write checking, instruction-input virtualization, Spartan shift | `zklean-extractor/src/sumchecks.rs` (`extracted_claims`), `crates/jolt-claims/src/protocols/jolt/relations/` (`unbatched_relation`) |
| `KindTables.lean` | 96 instruction kinds, 16 circuit flags, instruction flags, lookup tables, RAF flags and 16 stamp entries | `crates/jolt-riscv` (`Flags`), `crates/jolt-lookup-tables` (`InstructionLookupTable`), `crates/jolt-witness` (`InstructionRafFlag::extract`) |

## Regenerate

Use a read-only Jolt checkout at the target commit and run from this repository's root.
Keep the work directory inside this checkout; the shared Cargo target directory below is the one prescribed for this repin.

```bash
JOLT_DIR="$HOME/claude-work/jolt-main-ff6fc" \
CARGO_TARGET_DIR="$HOME/claude-work/jq-repin/cargo-target" \
  scripts/expansion-parity/run-constraint-gen.sh "$PWD/.cache/constraint-gen"
```

`build.sh` copies Jolt's lockfile and toolchain and preserves its dependency patch tables, using absolute paths to its checkout.
It builds only the `constraint-gen` binary and respects `CARGO_TARGET_DIR` (default: `WORK_DIR/cargo-target`).
The run script writes the three Lean files and `WORK_DIR/out/constraint_summary.json`.
Pass `--no-lean` to write only the summary.
No decoder feature or inline crate is needed.

Then build the comparison module through the shared build lock:

```bash
~/claude-work/track-t-build.sh lake build JoltConstraints.ConstraintGen.Equiv
```

## Reading the result at this repin

`Types.lean` fixes the shapes of rows and relations.
`Semantics.lean` maps generated names to this branch's `translation/` witness model.
Its `RepinInputs` keeps the new `Halt`, `HaltPanic` columns and public protected-word mask C explicit, since the old witness model lacks them.
The C mask multiplies the output inside the RAM-address sum; it is not dropped or treated as a constant-one weight.
Generated circuit-flag and lookup-table types preserve names the old types cannot represent.
The name-preserving bridges map every old flag/table exhaustively; halt flags are false on old instructions, whose ISA has no halt constructor.

`Equiv.lean` proves the unchanged comparisons and retains marked mismatch admissions for the changed comparisons and missing kind coverage.
The aggregate theorems depend on those admissions and do not certify equivalence to Jolt main.
The handwritten constraints, witness, ISA, language and soundness proofs are unchanged.
See [the complete repin inventory](../../reports/2026-11-24-constraint-repin-diff.md) for exact old/new equations, source lines, PRs, proof status and the uncovered handwritten conjuncts.

## Checks

The generator retains #56's original checks:

- `r1cs_shape`: matrix dimensions, row-array lengths and constraint-name count agree with Jolt's exported constants.
- `r1cs_outer_is_prefix`: the Spartan outer matrices are the first 19, equality-conditional rows of the full matrix.
- `r1cs_variable_names_unique`: column names are unique and the constant column is `One`.
- `relations_match_extractor`: the four linked `unbatched_relation` calls equal the source list in `extracted_claims`, in order.
- `relations_count`: exactly four relations are emitted.
- `kind_names_unique`: instruction-kind names are unique.
- `stamp_uniformity`: over 4,108 stamps per kind, circuit flags equal canonical flags plus stamp flags, while instruction flags and lookup table do not depend on the stamp.
- `raf_stamp_independent`: the RAF flag does not depend on the stamp, with the original exclusion of invalid stamped NoOp trace rows.

R1CS checks run for both public panic-bit values.
The added `panic_only_changes_row21` check requires rows 0–20 to be identical in both matrices.
Row 21 emits both matrices' actual integer coefficients, using a Lean Boolean parameter rather than fixing the statement to success.
The stamp check compares every count in `1..=1024` and `65535` with the same stamp whose nonzero count is replaced by 1, matching `stampClass`.

The extractor-list parser keeps #56's restricted grammar.
It requires one line-start `fn extracted_claims()` whose body, after line comments and whitespace are removed, is exactly `vec![A::unbatched_relation(), ...]`.
It rejects block comments, string/character literals, other body forms and unexpected list items.
If Jolt changes that grammar, extend the parser deliberately.

| Exit status | Meaning |
| --- | --- |
| 0 | All checks passed; output was written. |
| 1 | A check failed; `checks` in the summary records it, and the Lean files are still written. |
| 2 | The generator could not run or parse its input. |

## CI and future changes

`.github/workflows/constraint-generation.yml` checks out the full target hash as `JOLT_REV`, regenerates data, fails on generated-file differences, and builds `Equiv`.
This port has been checked locally; the workflow has not been run remotely.
A new variable/polynomial/weight changes the generated types and requires an exhaustive semantic mapping.
New kinds must be represented or recorded as explicit mismatch obligations; an unrecorded missing kind or a wrong `kindOf` arm fails the metadata check.
A changed coefficient, weight, flag or table must be investigated against the pinned Jolt source.
Do not edit generated files by hand or alter handwritten constraints to make this comparison pass.
