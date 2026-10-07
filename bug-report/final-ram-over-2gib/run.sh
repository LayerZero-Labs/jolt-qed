#!/bin/sh
# Reproduces the final-RAM misplacement for a program whose RAM extends more than
# 2 GiB above RAM_START.
#
# Usage: sh run.sh /absolute/path/to/jolt
# Needs about 17 GiB of free RAM (the final-RAM table has 2^29 slots).
# Set SKIP_BUILD=1 to reuse an existing debug build, and RUST_TOOLCHAIN to override
# the toolchain used for the build (default: the repo's pinned toolchain).
set -eu

repro_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if [ "$#" -ne 1 ] || [ ! -d "$1" ]; then
  printf 'Usage: sh %s /absolute/path/to/jolt\n' "$0" >&2
  exit 2
fi
rust_repo=$(CDPATH= cd -- "$1" && pwd)
toolchain=${RUST_TOOLCHAIN:-1.95}
build_dir=$(mktemp -d "${TMPDIR:-/tmp}/ramfinal.XXXXXX")
deps_dir="$rust_repo/target/debug/deps"

python3 "$repro_dir/make_elf.py" "$build_dir/guest.elf" > /dev/null

if [ "${SKIP_BUILD:-0}" != 1 ]; then
  (cd "$rust_repo" && cargo +"$toolchain" build -p jolt-prover -p tracer -p jolt-witness \
    -p jolt-program -p jolt-riscv -p common -p jolt-claims -p jolt-field)
fi

latest_lib() {
  ls -t "$deps_dir/lib$1"-*.rlib | head -n 1
}

rustup run "$toolchain" rustc --edition=2021 "$repro_dir/ramfinal_repro.rs" \
  -L "dependency=$deps_dir" \
  --extern "tracer=$(latest_lib tracer)" \
  --extern "jolt_program=$(latest_lib jolt_program)" \
  --extern "jolt_riscv=$(latest_lib jolt_riscv)" \
  --extern "common=$(latest_lib common)" \
  --extern "jolt_witness=$(latest_lib jolt_witness)" \
  --extern "jolt_claims=$(latest_lib jolt_claims)" \
  --extern "jolt_field=$(latest_lib jolt_field)" \
  --extern "jolt_prover=$(latest_lib jolt_prover)" \
  -o "$build_dir/repro"

"$build_dir/repro" "$build_dir/guest.elf"
