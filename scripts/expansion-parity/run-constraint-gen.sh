#!/usr/bin/env bash
# Build the expansion-parity crate and generate the T3 constraint data.
#
# Usage:
#   JOLT_DIR=<a16z/jolt checkout at 3cc6e7bd1> EXPANSION_PARITY_FEATURES=zicsr-remaining \
#     scripts/expansion-parity/run-constraint-gen.sh WORK_DIR [--no-lean]
#
# EXPANSION_PARITY_FEATURES is passed to build.sh; a16z/jolt#2384 (3cc6e7bd1)
# needs zicsr-remaining for the expansion-parity binary in the same crate.
# The script calls build.sh WORK_DIR, which builds every binary of the crate,
# then runs the constraint-gen binary. It writes the generated Lean to
# JoltConstraints/ConstraintGen/Generated/ in this repository (unless
# --no-lean) and WORK_DIR/out/constraint_summary.json.
# The script exits with the binary's status: 0 when every check passes.
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

exec "$work/expansion-parity/target/release/constraint-gen" \
  --jolt-dir "$JOLT_DIR" --out "$work/out" ${lean[@]+"${lean[@]}"}
