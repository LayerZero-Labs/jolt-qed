#!/usr/bin/env bash
# Run the RISC-V architectural tests (ACT4, riscv/riscv-arch-test) through the
# difftest harness.
#
# Usage:
#   scripts/difftest/corpus-arch-test.sh WORK_DIR [ELF_DIR]
#
# The tests are the self-checking RV64IMAC ELFs that Jolt's own arch-test CI
# builds: ACT4 from the `third-party/riscv-arch-test` submodule of a Jolt
# checkout, with the DUT configuration in its `tests/arch-tests/jolt/`
# (unprivileged tests only). With ELF_DIR, the ELFs under it are run as they
# are, except the `*.sig.elf` builds ACT4 uses to compute the expected
# signatures. Without it, they are generated into WORK_DIR/arch-test-work/ first.
#
# Generation runs Jolt's `make bootstrap` and `make arch-tests-generate` in an
# ubuntu:24.04 container, as Jolt's CI does, so it needs a Docker daemon. ACT4
# does not build natively on macOS (its UDB gem downloads Linux-only
# binaries); on a Mac without Docker, generate on a Linux machine and pass the
# directory as ELF_DIR.
#
# Environment:
#   ACT4_JOLT_DIR  Jolt checkout that provides ACT4 and the DUT configuration
#                  (default: JOLT_DIR from WORK_DIR/env.sh). Its
#                  riscv-arch-test submodule is initialised if it is empty.
# Other settings are as for run.sh; results go to WORK_DIR/arch-test-results/.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:?usage: corpus-arch-test.sh WORK_DIR [ELF_DIR]}"
work="$(cd "$work" && pwd)"
[[ -f "$work/env.sh" ]] || { echo "corpus-arch-test: run build.sh $work first" >&2; exit 2; }
source "$work/env.sh"

if [[ $# -ge 2 ]]; then
  elf_dir="$(cd "$2" && pwd)"
else
  jolt="$(cd "${ACT4_JOLT_DIR:-$JOLT_DIR}" && pwd)"
  docker info >/dev/null 2>&1 ||
    { echo "corpus-arch-test: no Docker daemon; generate the ELFs elsewhere and pass ELF_DIR" >&2; exit 2; }
  [[ -f "$jolt/third-party/riscv-arch-test/Makefile" ]] ||
    git -C "$jolt" submodule update --init third-party/riscv-arch-test
  elf_dir="$work/arch-test-work"
  mkdir -p "$elf_dir"
  # ACT4 writes its work directory inside the container; the bind mount of
  # WORK_DIR makes it appear at $elf_dir.
  docker run --rm -v "$jolt":/jolt -v "$elf_dir":/act-out \
    -v difftest-act4-opt:/opt/riscv -v difftest-act4-home:/root -w /jolt ubuntu:24.04 \
    bash -lc "set -e
      export DEBIAN_FRONTEND=noninteractive
      apt-get update -qq
      apt-get install -y -qq --no-install-recommends ca-certificates curl git make >/dev/null
      git config --global --add safe.directory '*'
      make bootstrap
      make arch-tests-generate ARCH_TEST_WORK=/act-out
      chown -R $(id -u):$(id -g) /act-out" > "$work/arch-test-generate.log" 2>&1 ||
    { tail -20 "$work/arch-test-generate.log"; echo "corpus-arch-test: ELF generation failed" >&2; exit 2; }
fi

elfs=()
while IFS= read -r elf; do elfs+=("$elf"); done < <(find "$elf_dir" -name '*.elf' ! -name '*.sig.elf' | sort)
[[ ${#elfs[@]} -gt 0 ]] || { echo "corpus-arch-test: no ELFs under $elf_dir" >&2; exit 2; }
RESULTS=arch-test-results "$HERE/run.sh" "$work" "${elfs[@]}"
