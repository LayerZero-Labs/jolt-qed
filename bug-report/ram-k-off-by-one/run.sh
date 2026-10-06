#!/bin/sh
# Usage: sh run.sh /absolute/path/to/jolt
# Build the Rust crates first, in the jolt checkout:
#   cargo build -p jolt-prover -p tracer -p jolt-witness -p jolt-program \
#     -p jolt-riscv -p common -p jolt-claims -p jolt-field
# Set RUSTC_TOOLCHAIN (default: the repo's pinned toolchain) to the one used for that build.
set -eu
repro_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if [ "$#" -ne 1 ] || [ ! -d "$1" ]; then
  printf 'Usage: sh %s /absolute/path/to/jolt\n' "$0" >&2
  exit 2
fi
rust_repo=$(CDPATH= cd -- "$1" && pwd)
deps_dir="$rust_repo/target/debug/deps"
build_dir=$(mktemp -d "${TMPDIR:-/tmp}/ramk.XXXXXX")
toolchain=${RUSTC_TOOLCHAIN:-1.95}
latest_lib() { ls -t "$deps_dir/lib$1"-*.rlib | head -n 1; }

python3 "$repro_dir/make_elf.py" "$build_dir/slot1023.elf" -40 > /dev/null
python3 "$repro_dir/make_elf.py" "$build_dir/slot1024.elf" -32 > /dev/null
rustup run "$toolchain" rustc --edition=2021 "$repro_dir/ramk_repro.rs" \
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
for elf in slot1023 slot1024; do
  echo "== $elf"
  JOLT_TRACER_CAPACITY_ROWS=64 "$build_dir/repro" "$build_dir/$elf.elf"
done
