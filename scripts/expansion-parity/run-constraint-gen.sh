#!/usr/bin/env bash
# Build constraint-gen and regenerate the constraint data from a Jolt checkout.
# Usage: JOLT_DIR=/path/to/jolt CARGO_TARGET_DIR=/path/to/cache \
#   scripts/expansion-parity/run-constraint-gen.sh WORK_DIR [--no-lean]
# Only constraint-gen is built. Output: Generated/{R1CS,Relations,KindTables}.lean
# (unless --no-lean) and WORK_DIR/out/constraint_summary.json.
# Exit status is 0 for passing checks, 1 for failed checks, 2 for invalid input.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
work="${1:?usage: run-constraint-gen.sh WORK_DIR [--no-lean]}"
shift

lean=(--lean-root "$REPO")
for a in "$@"; do
  case "$a" in
    --no-lean) lean=() ;;
    *) echo "constraint-gen/run: unknown option $a" >&2; exit 2 ;;
  esac
done

[[ -n "${JOLT_DIR:-}" ]] || { echo "constraint-gen/run: set JOLT_DIR" >&2; exit 2; }
"$HERE/build.sh" "$work"
work="$(cd "$work" && pwd)"
# shellcheck source=/dev/null
source "$work/env.sh"

exec "$CONSTRAINT_GEN" \
  --jolt-dir "$JOLT_DIR" --out "$work/out" ${lean[@]+"${lean[@]}"}
