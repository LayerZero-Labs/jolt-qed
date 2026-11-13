# Constraint generation (T3)

`constraint-gen` reads Jolt's own code and writes three Lean files under
`JoltConstraints/ConstraintGen/Generated/`:

| File | Contents | Jolt source |
| --- | --- | --- |
| `R1CS.lean` | The 22 per-cycle R1CS rows of `rv64_trace_constraints`, with their variables and integer coefficients | `crates/jolt-claims/src/protocols/composed/r1cs/rv64.rs` |
| `Relations.lean` | The four relations that `zklean-extractor` extracts (`extracted_claims` in `zklean-extractor/src/sumchecks.rs`): RAM and register read-write checking, instruction-input virtualization, and the Spartan shift | `unbatched_relation` in `crates/jolt-claims/src/protocols/jolt/relations/` |
| `KindTables.lean` | For each `JoltInstructionKind`: its circuit flags, instruction flags, lookup table and RAF flag, plus the circuit flags each sequence stamp adds | `crates/jolt-riscv` (`Flags`), `crates/jolt-lookup-tables`, `crates/jolt-witness` (`InstructionRafFlag::extract`) |

`JoltConstraints/ConstraintGen/Semantics.lean` says which witness column each
generated name stands for. `JoltConstraints/ConstraintGen/Equiv.lean` proves
that the handwritten constraints and metadata equal the generated data under
that reading.

## Regenerate

Check out a16z/jolt at the pinned commit (`580084fcf`, the commit of the
expansion-parity job), then run from the repository root:

```bash
JOLT_DIR=/path/to/jolt EXPANSION_PARITY_FEATURES=zicsr-remaining scripts/expansion-parity/run-constraint-gen.sh /tmp/constraint-gen
```

The script builds the crate with `build.sh`, runs `constraint-gen`, rewrites
the three generated files and writes `WORK_DIR/out/constraint_summary.json`.
Pass `--no-lean` to write only the summary.

Then rebuild the proofs:

```bash
lake build JoltConstraints.ConstraintGen.Equiv
```

## Exit status

| Status | Meaning |
| --- | --- |
| 0 | Every check passed and the files were written. |
| 1 | A check failed. The summary lists it under `checks`. The Lean files are still written. |
| 2 | The generator could not run (bad arguments, unreadable Jolt checkout). |

## Checks the generator runs

* `r1cs_shape`: 22 rows over 38 variables.
* `r1cs_outer_is_prefix`: the matrices of the Spartan outer sumcheck are the
  first 19 rows (the eq-conditional ones) of the full matrices.
* `r1cs_variable_names_unique`: no two variables share a name.
* `relations_match_extractor`: the generator's relations are the
  `X::unbatched_relation()` calls in `extracted_claims`
  (`zklean-extractor/src/sumchecks.rs`), in order. The generator reads that
  list from the extractor's source, since the extractor is a binary crate,
  under a restricted grammar: the file declares `fn extracted_claims()` once,
  at the start of a line; the body may contain `//` comments but no block
  comment, string or character literal; and without comments and whitespace
  it is `vec![A::unbatched_relation(), ...]`. Anything else is an error
  (status 2). If Jolt changes that function's form, extend the parser rather
  than loosen it.
* `relations_count`: the generator emits exactly four relations.
* `kind_names_unique`: no two instruction kinds share a name.
* `stamp_uniformity`: for every kind and every stamp
  (`virtual_sequence_remaining` in `None`, `0..=1024` and `65535`, times
  `is_first_in_sequence` and `is_compressed`), the circuit flags are the
  kind's canonical flags plus the stamp's flags, and the instruction flags and
  lookup table do not depend on the stamp. Each stamp must also add exactly
  the flags of the same stamp with a nonzero count replaced by `1`, which is
  how Lean's `stampClass` reads it.
* `raf_stamp_independent`: over the same stamps, the RAF flag does not depend
  on the stamp.

## CI

`.github/workflows/constraint-generation.yml` checks out Jolt at `JOLT_REV`,
reruns the generator, fails if any generated file changes, and builds
`JoltConstraints.ConstraintGen.Equiv`.

## When Jolt changes

If the regenerated files differ, read the diff first. A renamed or added
variable, polynomial or weight changes a generated inductive type, so
`Semantics.lean` stops compiling until someone maps the new name. A new
instruction kind fails the `run_meta` check in `Equiv.lean` until Lean has an
instruction of that name. A changed
coefficient, flag or table makes a proof in `Equiv.lean` fail. Decide whether
Jolt or the handwritten model is wrong before you change either. Do not edit
the generated files by hand.
