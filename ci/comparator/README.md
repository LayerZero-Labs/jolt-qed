# Comparator gate

This directory runs Lean's built-in `lake comparator` (Lean v4.35.0) over jolt-qed's headline theorems.
The comparator builds and exports the `Challenge` and `Solution` modules inside a `bwrap` sandbox and replays the exports.
It then checks three things for every name in `theorem_names`.

1. The `Solution` theorem proves the same statement as the `Challenge` theorem of the same name.
2. The kernel accepts the exported proof.
3. The proof depends on no axiom outside `permitted_axioms` (`propext`, `Quot.sound`, `Classical.choice`).

The gate is the third of three checks on the same theorems.

| Check | Mechanism | CI job |
|-------|-----------|--------|
| `scripts/check_hygiene.py` | Text scan for `sorry`, trusted tactics, raised limits and axioms | `hygiene` in `provenance.yml` |
| `JoltAudit/Axioms.lean` | `Lean.collectAxioms` against an allowlist, during `lake build JoltAudit` | `build` in `lean.yml` |
| This gate | Sandboxed build, export, replay and statement comparison | `comparator` in `provenance.yml` |

The comparator does not trust Lean's own axiom bookkeeping, because it re-reads the exported declarations.

## Status

The `comparator` CI job has not passed yet.
Its steps use `continue-on-error: true`, and a failure shows as a warning that does not block a pull request.
Once the job passes on a runner, drop `continue-on-error` and the warning step.

On macOS, `COMPARATOR_NO_SANDBOX=1 scripts/run_comparator.sh` accepts all six theorems.
That run uses `lake comparator --inadvisably-no-sandbox`, because macOS has no `bwrap`.
It checks the statements, the kernel and the axioms but not the isolation.
With one proof in `Solution.lean` replaced by `sorry`, the same run rejects the solution with `Illegal axiom detected: 'sorryAx'`.

## Trust

`Solution.lean` is the untrusted input.
`scripts/run_comparator.sh` never builds it, or `Challenge.lean`, outside the comparator's sandbox, and deletes any of their build output left in `.lake/`.
It builds only the jolt-qed modules that `Challenge.lean` imports, which are trusted.
`scripts/check_comparator_imports.py` fails the run unless `Solution.lean` has exactly the import header of `Challenge.lean` and that header imports exactly `TRUSTED_IMPORTS`.
It reads the header with comments removed, so a comment cannot hide an import and an `import` line inside a comment does not count.
To change the imports, change both files and `TRUSTED_IMPORTS` in the script.

The deprecated external tool, [`leanprover/comparator`](https://github.com/leanprover/comparator) with `lean4export` and `landrun`, still runs with `COMPARATOR_ENGINE=external`.
It also builds both modules inside its own sandbox.

## Layout

- The root `lakefile.toml` declares `Challenge` and `Solution` as libraries with `srcDir = "ci/comparator"`, outside the default targets.
  They live in the root package because the `lake comparator` sandbox exposes only the project directory, the toolchain and the Lake home.
  A separate package under `ci/comparator/` could not read the root package or its `.lake/packages` from inside the sandbox.
  The script therefore runs `lake comparator` from the repository root, with the root `lake-manifest.json`.
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

`lake comparator` needs only the repository's toolchain and `bwrap` (bubblewrap) with unprivileged user namespaces.
On Ubuntu 24.04, AppArmor restricts those namespaces; the CI job lifts the restriction with `sysctl kernel.apparmor_restrict_unprivileged_userns=0`.

For the external engine, `scripts/setup_comparator_toolchain.sh` builds `comparator`, `lean4export` (against this repository's `lean-toolchain`) and `landrun` at pinned revisions, and prints `COMPARATOR_BIN`, `COMPARATOR_LEAN4EXPORT` and `COMPARATOR_LANDRUN`.

## Running

On Linux, from the repository root:

```bash
lake exe cache get
scripts/run_comparator.sh
```

On macOS, without the sandbox, for a smoke test only:

```bash
COMPARATOR_NO_SANDBOX=1 scripts/run_comparator.sh
```

With the external engine, on Linux:

```bash
scripts/setup_comparator_toolchain.sh
COMPARATOR_ENGINE=external COMPARATOR_NO_SANDBOX=1 scripts/run_comparator.sh
```
