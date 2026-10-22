#!/bin/sh
# Usage: sh run.sh /absolute/path/to/jolt
# Copies the Jolt checkout (without target/ and .git), patches the copy's tracer
# so that JOLT_CHEAT_SC_FAIL=1 makes SC.W report failure, builds the harness in
# release mode, and proves and verifies the test ELF with an honest and a
# cheating prover. The checkout itself is not modified. Needs Python 3, rsync,
# and Rust toolchain 1.95.
set -eu
repro_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
if [ "$#" -ne 1 ] || [ ! -d "$1" ]; then
  printf 'Usage: sh %s /absolute/path/to/jolt\n' "$0" >&2
  exit 2
fi
jolt=$(CDPATH= cd -- "$1" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/sc-forced-failure.XXXXXX")

rsync -a --exclude target --exclude .git "$jolt/" "$work/jolt/"
patch -s -d "$work/jolt" -p1 < "$repro_dir/tracer.patch"
mkdir -p "$work/jolt/jolt-sdk/examples"
cp "$repro_dir/sc_flag.rs" "$work/jolt/jolt-sdk/examples/sc_flag.rs"
python3 "$repro_dir/make_elf.py" "$work/sc.elf"
(cd "$work/jolt" && cargo +1.95 build -q --release -p jolt-sdk --features host --example sc_flag)

echo "== honest prover"
"$work/jolt/target/release/examples/sc_flag" "$work/sc.elf"
echo "== cheating prover"
JOLT_CHEAT_SC_FAIL=1 "$work/jolt/target/release/examples/sc_flag" "$work/sc.elf"
