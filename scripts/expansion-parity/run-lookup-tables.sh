#!/usr/bin/env bash
# Build the expansion-parity crate and emit lookup-table vectors (track T, T4).
#
# Usage:
#   JOLT_DIR=~/claude-work/jolt-t2-580084 EXPANSION_PARITY_FEATURES=zicsr-remaining \
#     scripts/expansion-parity/run-lookup-tables.sh WORK_DIR [options...]
#
# EXPANSION_PARITY_FEATURES is passed to build.sh; a16z/jolt#2384 (580084fcf)
# needs zicsr-remaining for the other driver binary in the crate.
# The script calls build.sh WORK_DIR, which builds every binary of the crate,
# then runs the lookup-tables binary with --out WORK_DIR/out. It writes
# WORK_DIR/out/lookup_vectors.jsonl and WORK_DIR/out/lookup_summary.json.
# Options (see LOOKUP-TABLES.md): --seed N, --random-per-table N.
# The script exits with the binary's status: 0 when every table was evaluated
# without a panic.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:?usage: run-lookup-tables.sh WORK_DIR [options...]}"
shift

[[ -n "${JOLT_DIR:-}" ]] || { echo "lookup-tables/run: set JOLT_DIR" >&2; exit 2; }
"$HERE/build.sh" "$work"
work="$(cd "$work" && pwd)"
# shellcheck source=/dev/null
source "$work/env.sh"

exec "$work/expansion-parity/target/release/lookup-tables" \
  --jolt-dir "$JOLT_DIR" --out "$work/out" "$@"
