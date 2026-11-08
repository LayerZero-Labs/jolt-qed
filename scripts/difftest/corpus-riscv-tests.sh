#!/usr/bin/env bash
# Run riscv-tests through the difftest harness.
#
# Usage:
#   scripts/difftest/corpus-riscv-tests.sh WORK_DIR [SUITE ...]
#
# SUITE is a directory under riscv-tests/isa (default: rv64ui rv64um rv64ua
# rv64uc rv64mi). The tests are built against guest/riscv-tests-env/, an
# M-mode-only copy of riscv-tests' env/p that touches only the CSRs Jolt
# models. riscv-tests is cloned into WORK_DIR/riscv-tests on first use; every
# run checks it out at RISCV_TESTS_COMMIT (default below), updates its `env`
# submodule to the revision that commit records, and stops if either differs
# or the checkout has local changes. Every test of each suite must build, or
# the script stops with status 2 before running any. Other settings are as
# for run.sh; results go to WORK_DIR/riscv-tests-results/.
set -euo pipefail

RISCV_TESTS_COMMIT="${RISCV_TESTS_COMMIT:-3df703cd52d5f0d8224e3c50bf03c6cb70efff98}"
HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:?usage: corpus-riscv-tests.sh WORK_DIR [SUITE ...]}"
shift
work="$(cd "$work" && pwd)"
suites=("$@")
[[ ${#suites[@]} -gt 0 ]] || suites=(rv64ui rv64um rv64ua rv64uc rv64mi)
source "$HERE/toolchain.sh"

die() { echo "corpus-riscv-tests: $*" >&2; exit 2; }
src="$work/riscv-tests"
[[ -d "$src/.git" ]] || git clone -q https://github.com/riscv-software-src/riscv-tests "$src" ||
  die "cannot clone riscv-tests"
if [[ "$(git -C "$src" rev-parse HEAD)" != "$RISCV_TESTS_COMMIT" ]]; then
  git -C "$src" cat-file -e "$RISCV_TESTS_COMMIT^{commit}" 2>/dev/null ||
    git -C "$src" fetch -q origin "$RISCV_TESTS_COMMIT" || die "cannot fetch $RISCV_TESTS_COMMIT"
  git -C "$src" checkout -q "$RISCV_TESTS_COMMIT" || die "cannot check out $RISCV_TESTS_COMMIT"
fi
git -C "$src" submodule -q update --init env || die "cannot update the env submodule"
[[ "$(git -C "$src" rev-parse HEAD)" == "$RISCV_TESTS_COMMIT" ]] ||
  die "$src is not at $RISCV_TESTS_COMMIT"
status="$(git -C "$src" submodule status env)" || die "cannot read the env submodule"
[[ "$status" == " "* ]] || die "the env submodule is not at its recorded revision: $status"
changes="$(git -C "$src" status --porcelain --ignore-submodules=none)" || die "cannot read $src"
[[ -z "$changes" ]] || die "$src has local changes; remove it to clone afresh"

elfs=()
failed=()
for suite in "${suites[@]}"; do
  out="$work/riscv-tests-elf/$suite"
  mkdir -p "$out"
  tests=("$src/isa/$suite"/*.S)
  [[ -f "${tests[0]}" ]] || die "no tests in $src/isa/$suite"
  for test in "${tests[@]}"; do
    elf="$out/$suite-$(basename "${test%.S}").elf"
    # Preprocess first, and drop `.global mtvec_handler` (or stvec_handler):
    # the environment declares both weak so that tests may leave them out,
    # and clang's assembler, unlike GNU as, rejects making them global later.
    if "$CLANG" -E -P -x assembler-with-cpp --target=riscv64 -march=rv64imac_zicsr_zifencei \
          -mabi=lp64 -I "$HERE/guest/riscv-tests-env" -I "$src/env" \
          -I "$src/isa/macros/scalar" "$test" 2> "${elf%.elf}.build.log" |
        sed -E '/^[[:space:]]*\.glob(a)?l[[:space:]]+[ms]tvec_handler[[:space:]]*$/d' \
          > "${elf%.elf}.s" &&
        assemble "${elf%.elf}.s" "$elf" 2>> "${elf%.elf}.build.log"; then
      elfs+=("$elf")
    else
      failed+=("$suite/$(basename "$test")")
    fi
  done
done
[[ ${#failed[@]} -eq 0 ]] ||
  die "did not build (see riscv-tests-elf/*/*.build.log): ${failed[*]}"
RESULTS=riscv-tests-results "$HERE/run.sh" "$work" "${elfs[@]}"
