#!/usr/bin/env bash
# Run the comparator gate over ci/comparator/. Adapted from openvm-fv.
#
# The comparator exports the Challenge and Solution modules and checks that
# every theorem in ci/comparator/config.json proves the same statement in both,
# that the kernel accepts it, and that it uses only the permitted axioms.
#
# Engines (COMPARATOR_ENGINE):
#   lake (default)      `lake comparator`, built into Lean v4.35.0. It needs
#                       `bwrap` (bubblewrap). COMPARATOR_NO_SANDBOX=1 passes
#                       --inadvisably-no-sandbox, which is for local smoke tests
#                       only.
#   external            leanprover/comparator with lean4export and landrun
#                       (deprecated upstream in favour of `lake comparator`).
#                       Tools come from PATH or from COMPARATOR_BIN,
#                       COMPARATOR_LEAN4EXPORT and COMPARATOR_LANDRUN, which
#                       scripts/setup_comparator_toolchain.sh prints.
#                       The run is wrapped in `systemd-run --user` unless
#                       COMPARATOR_NO_SANDBOX=1; comparator still sandboxes its
#                       builds and replay with landrun either way.
#
# The script never builds Challenge or Solution itself: Solution is the
# untrusted input, and building it outside the comparator's sandbox would run
# its elaborators unsandboxed before the check starts. Both engines build the
# two modules inside their sandbox. The script first builds the jolt-qed
# modules that Challenge imports (trusted code, the same build as lean.yml), so
# that the sandboxed build compiles only the two gate modules. It deletes any
# Challenge or Solution build output left in .lake/build first, so the
# comparator cannot reuse output built outside its sandbox.
#
# Challenge and Solution are libraries of the root package (lakefile.toml,
# srcDir ci/comparator) because the `lake comparator` sandbox exposes only the
# project directory, the toolchain and the Lake home. The script runs the
# comparator from the repository root.
#
# Usage: scripts/run_comparator.sh
# Exit status: 0 accepted, 1 rejected or build failure, 2 missing tools.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GATE_DIR="$REPO_ROOT/ci/comparator"
CONFIG="$GATE_DIR/config.json"
ENGINE="${COMPARATOR_ENGINE:-lake}"

case "$ENGINE" in
  external | lake) ;;
  *)
    echo "ERROR: COMPARATOR_ENGINE must be 'external' or 'lake', not '$ENGINE'." >&2
    exit 2
    ;;
esac

missing=0
need() {
  local name="$1" path="$2"
  if ! command -v "$path" >/dev/null 2>&1 && [ ! -x "$path" ]; then
    echo "ERROR: required tool '$name' not found (looked for: $path)." >&2
    missing=1
  fi
}
if [ "$ENGINE" = external ]; then
  COMPARATOR_BIN="${COMPARATOR_BIN:-comparator}"
  need comparator "$COMPARATOR_BIN"
  need lean4export "${COMPARATOR_LEAN4EXPORT:-lean4export}"
  need landrun "${COMPARATOR_LANDRUN:-landrun}"
elif [ "${COMPARATOR_NO_SANDBOX:-0}" != 1 ]; then
  need bwrap "${COMPARATOR_BWRAP:-bwrap}"
fi
if [ "$missing" -ne 0 ]; then
  echo "See ci/comparator/README.md for how to obtain the comparator tools." >&2
  exit 2
fi

# The jolt-qed modules that Challenge.lean imports. Solution.lean must import
# nothing else (ci/comparator/README.md).
TRUSTED_IMPORTS=(JoltConstraints.WholeRun.Top JoltBytecode.Decode.Compressed JoltBytecode.Step.Instructions)
python3 "$REPO_ROOT/scripts/check_comparator_imports.py" \
  "$GATE_DIR/Challenge.lean" "$GATE_DIR/Solution.lean" "${TRUSTED_IMPORTS[@]}"

echo ">> building the trusted jolt-qed imports of the gate"
( cd "$REPO_ROOT" && lake build "${TRUSTED_IMPORTS[@]}" )

echo ">> removing Challenge and Solution build output built outside the sandbox"
rm -rf "$REPO_ROOT/.lake/build/lib/lean/Challenge".* "$REPO_ROOT/.lake/build/lib/lean/Solution".* \
  "$REPO_ROOT/.lake/build/ir/Challenge".* "$REPO_ROOT/.lake/build/ir/Solution".*

echo ">> running the comparator ($ENGINE) on ci/comparator/config.json"
if [ "$ENGINE" = lake ]; then
  flags=()
  if [ "${COMPARATOR_NO_SANDBOX:-0}" = 1 ]; then flags+=(--inadvisably-no-sandbox); fi
  ( cd "$REPO_ROOT" && lake comparator --config "$CONFIG" ${flags[@]+"${flags[@]}"} )
elif [ "${COMPARATOR_NO_SANDBOX:-0}" = 1 ]; then
  ( cd "$REPO_ROOT" && lake env "$COMPARATOR_BIN" "$CONFIG" )
else
  ( cd "$REPO_ROOT" && systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
      -E PATH="$PATH" \
      ${COMPARATOR_LANDRUN:+-E COMPARATOR_LANDRUN="$COMPARATOR_LANDRUN"} \
      ${COMPARATOR_LEAN4EXPORT:+-E COMPARATOR_LEAN4EXPORT="$COMPARATOR_LEAN4EXPORT"} \
      --working-directory "$REPO_ROOT" -- \
      bash -c "lake env '$COMPARATOR_BIN' '$CONFIG'" )
fi
echo ">> comparator gate passed"
