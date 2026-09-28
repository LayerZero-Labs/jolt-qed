#!/bin/sh
set -eu

repro_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if [ "$#" -ne 1 ] || [ ! -d "$1" ]; then
  printf 'Usage: sh %s /absolute/path/to/jolt\n' "$0" >&2
  exit 2
fi
rust_repo=$(CDPATH= cd -- "$1" && pwd)
build_dir=$(mktemp -d "${TMPDIR:-/private/tmp}/ram37.XXXXXX")
deps_dir="$rust_repo/target/debug/deps"

python3 "$repro_dir/make_ram37_elf.py" "$build_dir/guest.elf"

if [ "${SKIP_BUILD:-0}" != 1 ]; then
  (cd "$rust_repo" && cargo +1.95 build -p tracer -p jolt-witness)
fi

latest_lib() {
  ls -t "$deps_dir/lib$1"-*.rlib | head -n 1
}

rustup run 1.95 rustc --edition=2021 "$repro_dir/ram37_repro.rs" \
  -L "dependency=$deps_dir" \
  --extern "tracer=$(latest_lib tracer)" \
  --extern "jolt_program=$(latest_lib jolt_program)" \
  --extern "jolt_riscv=$(latest_lib jolt_riscv)" \
  --extern "common=$(latest_lib common)" \
  --extern "jolt_witness=$(latest_lib jolt_witness)" \
  --extern "jolt_claims=$(latest_lib jolt_claims)" \
  --extern "jolt_field=$(latest_lib jolt_field)" \
  -o "$build_dir/repro"

JOLT_TRACER_CAPACITY_ROWS=64 "$build_dir/repro" "$build_dir/guest.elf"
