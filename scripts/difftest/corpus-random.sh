#!/usr/bin/env bash
# Run random RV64IMAC guests through the difftest harness.
#
# Usage:
#   scripts/difftest/corpus-random.sh WORK_DIR [FIRST_SEED [COUNT [LENGTH]]]
#
# Generates COUNT guests (default 100) with gen-random.py, from seeds
# FIRST_SEED (default 0) onwards, each LENGTH instructions long (default 200),
# into WORK_DIR/random-src/, and runs them. Other settings are as for run.sh;
# results go to WORK_DIR/random-results/.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:?usage: corpus-random.sh WORK_DIR [FIRST_SEED [COUNT [LENGTH]]]}"
first="${2:-0}" count="${3:-100}" length="${4:-200}"
work="$(cd "$work" && pwd)"
src="$work/random-src"
mkdir -p "$src"
guests=()
for ((seed = first; seed < first + count; seed++)); do
  python3 "$HERE/gen-random.py" "$seed" "$length" > "$src/random-$seed.S"
  guests+=("$src/random-$seed.S")
done
RESULTS=random-results "$HERE/run.sh" "$work" "${guests[@]}"
