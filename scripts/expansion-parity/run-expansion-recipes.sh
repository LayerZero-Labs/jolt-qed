#!/usr/bin/env bash
# Build the expansion-parity crate and derive the T6 expansion recipes.
#
# Usage:
#   JOLT_DIR=<a16z/jolt checkout at 3cc6e7bd1> EXPANSION_PARITY_FEATURES=zicsr-remaining \
#     scripts/expansion-parity/run-expansion-recipes.sh WORK_DIR [--no-lean]
#
# EXPANSION_PARITY_FEATURES is passed to build.sh; the recipes of CSRRC,
# CSRRWI, CSRRSI and CSRRCI need zicsr-remaining (a16z/jolt#2384).
# The script calls build.sh WORK_DIR, which builds every binary of the crate,
# then runs the expansion-recipes binary. Unless --no-lean is given, it writes
# JoltBytecode/JoltISA/ExpansionsAutomated.lean,
# JoltConstraints/ExpansionGen/Generated.lean and
# JoltConstraints/ExpansionGen/Equiv.lean in this repository. It always writes
# WORK_DIR/out/recipes.json and WORK_DIR/out/summary.json.
# The script exits with the binary's status: 0 when every check passes.
# See scripts/expansion-parity/EXPANSION-RECIPES.md.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
work="${1:?usage: run-expansion-recipes.sh WORK_DIR [--no-lean]}"
shift

lean=(--lean-root "$REPO")
for a in "$@"; do
  case "$a" in
    --no-lean) lean=() ;;
    *) echo "expansion-recipes/run: unknown option $a" >&2; exit 2 ;;
  esac
done

[[ -n "${JOLT_DIR:-}" ]] || { echo "expansion-recipes/run: set JOLT_DIR" >&2; exit 2; }
"$HERE/build.sh" "$work"
work="$(cd "$work" && pwd)"
# shellcheck source=/dev/null
source "$work/env.sh"

exec "$work/expansion-parity/target/release/expansion-recipes" \
  --jolt-dir "$JOLT_DIR" --out "$work/out" ${lean[@]+"${lean[@]}"}
