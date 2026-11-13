#!/usr/bin/env bash
# Build the expansion-parity driver and run it against an a16z/jolt checkout.
#
# Usage:
#   JOLT_DIR=~/claude-work/jolt-inline-pin-a6b6 \
#     scripts/expansion-parity/run.sh [WORK_DIR] [driver options...]
#
# WORK_DIR defaults to ~/claude-work/expansion-parity-work. The driver writes
# rows.jsonl, inline_templates.json and summary.json to WORK_DIR/out and the
# generated Lean files to JoltBytecode/Inlines/Generated/ in this repository.
# Driver options (see README.md): --seed N, --random-per-kind N,
# --lean-chunk N, --skip-uniformity, --no-lean.
# The script exits with the driver's status: 0 when every check passes.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
work="${1:-$HOME/claude-work/expansion-parity-work}"
shift || true

[[ -n "${JOLT_DIR:-}" ]] || { echo "expansion-parity/run: set JOLT_DIR" >&2; exit 2; }
"$HERE/build.sh" "$work"
# shellcheck source=/dev/null
source "$work/env.sh"

lean=(--lean-root "$REPO")
args=()
for a in "$@"; do
  if [[ "$a" == "--no-lean" ]]; then lean=(); else args+=("$a"); fi
done

exec "$EXPANSION_PARITY" --jolt-dir "$JOLT_DIR" --out "$work/out" \
  ${lean[@]+"${lean[@]}"} ${args[@]+"${args[@]}"}
