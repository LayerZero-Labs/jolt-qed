#!/usr/bin/env bash
# Run random RV64IMAC guests through the difftest harness.
#
# Usage:
#   scripts/difftest/corpus-random.sh WORK_DIR [FIRST_SEED [COUNT [LENGTH]]]
#
# Generates COUNT guests (default 100, at least 1) with gen-random.py, from
# seeds FIRST_SEED (default 0) onwards, each LENGTH items long (default 200),
# and runs them. MIX (default base) is gen-random.py's instruction mix; the
# guests go to WORK_DIR/random-src/ and the results to WORK_DIR/random-results/,
# or to random-MIX-src/ and random-MIX-results/ for another mix. Every random
# guest exits with code 0 unless it takes a trap it did not expect, so the
# guests run with EXPECT_CODE=0 (see run.sh). Other settings are as for run.sh.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:?usage: corpus-random.sh WORK_DIR [FIRST_SEED [COUNT [LENGTH]]]}"
first="${2:-0}" count="${3:-100}" length="${4:-200}"
mix="${MIX:-base}"
for v in "$first" "$count" "$length"; do
  [[ "$v" =~ ^[0-9]+$ ]] || { echo "corpus-random: '$v' is not a number" >&2; exit 2; }
done
first=$((10#$first)) count=$((10#$count)) length=$((10#$length))
[[ $count -ge 1 ]] || { echo "corpus-random: COUNT must be at least 1" >&2; exit 2; }
work="$(cd "$work" && pwd)"
dir=random
[[ "$mix" == base ]] || dir="random-$mix"
src="$work/$dir-src"
mkdir -p "$src"
guests=()
for ((seed = first; seed < first + count; seed++)); do
  python3 "$HERE/gen-random.py" "$seed" "$length" "$mix" > "$src/random-$seed.S" ||
    { echo "corpus-random: gen-random.py failed for seed $seed" >&2; exit 2; }
  guests+=("$src/random-$seed.S")
done
EXPECT_CODE=0 RESULTS="$dir-results" "$HERE/run.sh" "$work" "${guests[@]}"
