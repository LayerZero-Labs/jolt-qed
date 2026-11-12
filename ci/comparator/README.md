# Comparator gate

This directory runs [`leanprover/comparator`](https://github.com/leanprover/comparator) over jolt-qed's headline theorems.
The comparator exports the `Challenge` and `Solution` modules with `lean4export` and replays them in a `landrun` sandbox.
It then checks three things for every name in `theorem_names`.

1. The `Solution` theorem proves the same statement as the `Challenge` theorem of the same name.
2. The kernel accepts the exported proof.
3. The proof depends on no axiom outside `permitted_axioms` (`propext`, `Quot.sound`, `Classical.choice`).

The gate is the third of three checks on the same theorems.

| Check | Mechanism | CI job |
|-------|-----------|--------|
| `scripts/check_hygiene.py` | Text scan for `sorry`, trusted tactics, raised limits and axioms | `hygiene` in `provenance.yml` |
| `JoltAudit/Axioms.lean` | `Lean.collectAxioms` against an allowlist, during `lake build JoltAudit` | `build` in `lean.yml` |
| This gate | Export, sandboxed replay and statement comparison by a separate tool | `comparator` in `provenance.yml` |

The comparator does not trust Lean's own axiom bookkeeping, because it re-reads the exported declarations.

## Status

The `comparator` CI job has not run yet, and nobody has run the external comparator, because `landrun` uses Linux Landlock and does not build on macOS.
The job's steps use `continue-on-error: true`, and a failure shows as a warning that does not block a pull request.
Once the job passes on a runner, drop `continue-on-error` and the warning step.

On macOS, `COMPARATOR_ENGINE=lake COMPARATOR_NO_SANDBOX=1 scripts/run_comparator.sh` accepts all six theorems.
That run uses the built-in `lake comparator` without its `bwrap` sandbox.
It checks the statements, the kernel and the axioms but not the isolation.
With one proof in `Solution.lean` replaced by `sorry`, the same run rejects the solution with `Illegal axiom detected: 'sorryAx'`.

The leanprover/comparator README now marks the project as deprecated.
Lean v4.35.0, the toolchain of this repository, ships the same check as `lake comparator`, sandboxed with `bwrap` instead of `landrun`.
`scripts/run_comparator.sh` runs the built-in command when `COMPARATOR_ENGINE=lake` is set.
Moving the CI job to `lake comparator` would remove the three external builds in `scripts/setup_comparator_toolchain.sh`.

## Layout

- `lakefile.toml` declares a separate Lake package, `ComparatorGate`, that requires jolt-qed by path.
  It shares jolt-qed's dependency directory and reuses the Mathlib cache and the root build.
- `lake-manifest.json` records the same dependency revisions as the root manifest.
  `lake comparator` needs a manifest, because it resolves dependencies inside its sandbox.
- `lean-toolchain` is a copy of the root `lean-toolchain`.
- `Challenge.lean` states each gated theorem verbatim and proves it with `sorry`.
  The file lives outside `JoltBytecode/` and `JoltConstraints/`, which keeps its `sorry`s outside the hygiene scan.
- `Solution.lean` repeats each statement and proves it by applying the jolt-qed theorem.
- `config.json` names the modules, the theorems and the permitted axioms.

## Gated theorems

| Comparator name | jolt-qed theorem | Source |
|-----------------|------------------|--------|
| `ComparatorGate.sail_reproduces` | `WholeRun.HonestTrace.sail_reproduces` | `JoltConstraints/WholeRun/Top.lean` |
| `ComparatorGate.sail_soundness` | `JoltInstance.sail_soundness` | `JoltConstraints/WholeRun/Top.lean` |
| `ComparatorGate.soundness` | `JoltInstance.soundness` | `JoltConstraints/Soundness/soundness.lean` |
| `ComparatorGate.joltDecode_agrees` | `Decode.joltDecode_agrees` | `JoltBytecode/Decode/Agreement.lean` |
| `ComparatorGate.joltDecode_compressed_agrees` | `Decode.joltDecode_compressed_agrees` | `JoltBytecode/Decode/Compressed.lean` |
| `ComparatorGate.joltRun_eq_execute` | `RiscvInstruction.joltRun_eq_execute` | `JoltBytecode/Step/Instructions.lean` |

The completeness theorems are not gated, because they depend on `sorryAx` through five open gaps in `JoltConstraints/Completeness/`.
`JoltAudit/Axioms.lean` gates the same six theorems and three more step theorems.

To add a theorem, copy its statement verbatim into `Challenge.lean` and `Solution.lean`, and append its name to `theorem_names`.
When two source namespaces reuse a name, put each statement in its own `section` with a section-scoped `open`.

## Required tools

`scripts/setup_comparator_toolchain.sh` builds three binaries at pinned revisions.

1. `comparator`, from leanprover/comparator, built with its own Lean toolchain.
2. `lean4export`, from leanprover/lean4export, built against this repository's `lean-toolchain`.
   The export must come from the same Lean version as the `.olean` files it reads.
3. `landrun`, from Zouuup/landrun, built with Go from a pinned `main` commit.
   openvm-fv found that the tagged releases fail to apply comparator's Landlock ruleset.

The script prints `COMPARATOR_BIN`, `COMPARATOR_LEAN4EXPORT` and `COMPARATOR_LANDRUN`, and appends them to `$GITHUB_ENV` inside GitHub Actions.

## Running

On Linux, from the repository root:

```bash
lake exe cache get
lake build
scripts/setup_comparator_toolchain.sh
COMPARATOR_NO_SANDBOX=1 scripts/run_comparator.sh
```

`run_comparator.sh` wraps the comparator in `systemd-run --user` unless `COMPARATOR_NO_SANDBOX=1` is set.
The comparator still sandboxes its own replay with `landrun` in that case.

With the built-in command, no setup script is needed, but `bwrap` must be installed:

```bash
COMPARATOR_ENGINE=lake scripts/run_comparator.sh
```
