#!/usr/bin/env bash
# Build the driver crate and run the T2 decoder sweep against an a16z/jolt checkout.
#
# Usage:
#   JOLT_DIR=<a16z/jolt checkout> \
#     scripts/expansion-parity/run-decoder-sweep.sh [WORK_DIR] [decoder-sweep options...]
#
# WORK_DIR defaults to ~/claude-work/decoder-sweep-work. The sweep writes
# decoder_parcels.tsv, decoder_words.tsv and decoder_summary.json to WORK_DIR/out.
# Options (see DECODER-SWEEP.md): --seed N, --random-patterns N, --skip-exhaustive.
# Set EXPANSION_PARITY_FEATURES=zicsr-remaining for a16z/jolt#2384, as build.sh says.
# The script exits with the sweep's status: 0 when its Rust-side checks pass.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:-$HOME/claude-work/decoder-sweep-work}"
shift || true

[[ -n "${JOLT_DIR:-}" ]] || { echo "decoder-sweep/run: set JOLT_DIR" >&2; exit 2; }
"$HERE/build.sh" "$work"
# shellcheck source=/dev/null
source "$work/env.sh"

exec "$(dirname "$EXPANSION_PARITY")/decoder-sweep" --jolt-dir "$JOLT_DIR" --out "$work/out" "$@"
