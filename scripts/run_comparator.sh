#!/usr/bin/env bash
# Run the comparator gate over ci/comparator/. Adapted from openvm-fv.
#
# The comparator exports the Challenge and Solution modules and checks that
# every theorem in ci/comparator/config.json proves the same statement in both,
# that the kernel accepts it, and that it uses only the permitted axioms.
#
# Engines (COMPARATOR_ENGINE):
#   external (default)  leanprover/comparator with lean4export and landrun.
#                       Tools come from PATH or from COMPARATOR_BIN,
#                       COMPARATOR_LEAN4EXPORT and COMPARATOR_LANDRUN, which
#                       scripts/setup_comparator_toolchain.sh prints.
#                       The run is wrapped in `systemd-run --user` unless
#                       COMPARATOR_NO_SANDBOX=1; comparator still sandboxes its
#                       replay with landrun either way.
#   lake                `lake comparator`, built into Lean v4.35.0. It needs
#                       `bwrap` (bubblewrap). COMPARATOR_NO_SANDBOX=1 passes
#                       --inadvisably-no-sandbox, which is for local smoke tests
#                       only.
#
# The script builds Challenge and Solution first. Build the root package (and
# fetch the Mathlib cache) before running it, so that this build only compiles
# the two gate modules.
#
# Usage: scripts/run_comparator.sh
# Exit status: 0 accepted, 1 rejected or build failure, 2 missing tools.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GATE_DIR="$REPO_ROOT/ci/comparator"
CONFIG="$GATE_DIR/config.json"
ENGINE="${COMPARATOR_ENGINE:-external}"

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

echo ">> building Challenge and Solution in ci/comparator"
( cd "$GATE_DIR" && lake build Challenge Solution )

echo ">> running the comparator ($ENGINE) on ci/comparator/config.json"
if [ "$ENGINE" = lake ]; then
  flags=()
  if [ "${COMPARATOR_NO_SANDBOX:-0}" = 1 ]; then flags+=(--inadvisably-no-sandbox); fi
  ( cd "$GATE_DIR" && lake comparator --config "$CONFIG" ${flags[@]+"${flags[@]}"} )
elif [ "${COMPARATOR_NO_SANDBOX:-0}" = 1 ]; then
  ( cd "$GATE_DIR" && lake env "$COMPARATOR_BIN" "$CONFIG" )
else
  ( cd "$GATE_DIR" && systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
      -E PATH="$PATH" \
      ${COMPARATOR_LANDRUN:+-E COMPARATOR_LANDRUN="$COMPARATOR_LANDRUN"} \
      ${COMPARATOR_LEAN4EXPORT:+-E COMPARATOR_LEAN4EXPORT="$COMPARATOR_LEAN4EXPORT"} \
      --working-directory "$GATE_DIR" -- \
      bash -c "lake env '$COMPARATOR_BIN' '$CONFIG'" )
fi
echo ">> comparator gate passed"
