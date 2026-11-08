#!/usr/bin/env bash
# Run random RV64IMAC guests through the difftest harness.
#
# Usage:
#   scripts/difftest/corpus-random.sh WORK_DIR [FIRST_SEED [COUNT [LENGTH]]]
#
# Generates COUNT guests (default 100) with gen-random.py, from seeds
# FIRST_SEED (default 0) onwards, each LENGTH items long (default 200), and
# runs them. MIX (default base) is gen-random.py's instruction mix; the guests
# go to WORK_DIR/random-src/ and the results to WORK_DIR/random-results/, or
# to random-MIX-src/ and random-MIX-results/ for another mix. Other settings
# are as for run.sh.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:?usage: corpus-random.sh WORK_DIR [FIRST_SEED [COUNT [LENGTH]]]}"
first="${2:-0}" count="${3:-100}" length="${4:-200}"
mix="${MIX:-base}"
work="$(cd "$work" && pwd)"
dir=random
[[ "$mix" == base ]] || dir="random-$mix"
src="$work/$dir-src"
mkdir -p "$src"
guests=()
for ((seed = first; seed < first + count; seed++)); do
  python3 "$HERE/gen-random.py" "$seed" "$length" "$mix" > "$src/random-$seed.S"
  guests+=("$src/random-$seed.S")
done
RESULTS="$dir-results" "$HERE/run.sh" "$work" "${guests[@]}"
