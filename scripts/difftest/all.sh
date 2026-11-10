#!/usr/bin/env bash
# Build both simulators and run every guest set through the difftest harness.
#
# Usage:
#   scripts/difftest/all.sh WORK_DIR
#
# Runs, in order: the comparator's self-test (test_difftest.py), build.sh,
# the reproducers in guest/repro/, riscv-tests, random guests of the base mix,
# random guests of the system mix, and the ACT4 architectural tests. Each set
# keeps its results in its own directory under WORK_DIR (see the README), and
# the last line of each set's output is collected in WORK_DIR/summary.txt,
# which is printed at the end.
#
# Environment (besides those of build.sh and run.sh):
#   SEEDS         random guests per mix (default 1000)
#   LENGTH        items per random guest (default 200)
#   ACT4_ELF_DIR  directory of ready ACT4 ELFs; without it they are generated
#                 with Docker (see corpus-arch-test.sh)
#
# The exit status is 2 when the self-test or the build fails or a set cannot
# run, 1 when every set ran and some guest differs, and 0 otherwise. A set
# that cannot run does not stop the sets after it.
set -uo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:?usage: all.sh WORK_DIR}"
mkdir -p "$work"
work="$(cd "$work" && pwd)"
seeds="${SEEDS:-1000}" length="${LENGTH:-200}"
summary="$work/summary.txt"
: > "$summary"

python3 "$HERE/test_difftest.py" > "$work/self-test.log" 2>&1 ||
  { tail -20 "$work/self-test.log" >&2; echo "difftest/all: self-test failed" >&2; exit 2; }
"$HERE/build.sh" "$work" || { echo "difftest/all: build failed" >&2; exit 2; }

worst=0
# run_set NAME COMMAND...: run one guest set, log it, record its last line.
run_set() {
  local name="$1" status=0 line
  shift
  echo "difftest/all: $name"
  "$@" > "$work/$name.log" 2>&1 || status=$?
  line="$(grep '^difftest/run: ' "$work/$name.log" | tail -1)"
  if [[ $status -le 1 && -n "$line" ]]; then
    printf '%-14s %s\n' "$name" "${line#difftest/run: }" >> "$summary"
    [[ $status -eq 0 || $worst -eq 2 ]] || worst=1
  else
    printf '%-14s did not run (exit %d; see %s)\n' "$name" "$status" "$work/$name.log" >> "$summary"
    worst=2
  fi
}

act4=("$HERE/corpus-arch-test.sh" "$work")
[[ -z "${ACT4_ELF_DIR:-}" ]] || act4+=("$ACT4_ELF_DIR")

run_set repro "$HERE/run.sh" "$work"
run_set riscv-tests "$HERE/corpus-riscv-tests.sh" "$work"
run_set random-base env MIX=base "$HERE/corpus-random.sh" "$work" 0 "$seeds" "$length"
run_set random-system env MIX=system "$HERE/corpus-random.sh" "$work" 0 "$seeds" "$length"
run_set act4 "${act4[@]}"

echo
cat "$summary"
exit "$worst"
