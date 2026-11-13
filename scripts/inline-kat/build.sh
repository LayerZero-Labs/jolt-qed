#!/usr/bin/env bash
# Build inline-kat, the known-answer driver for Jolt's five hash inlines.
#
# inline-kat runs SHA256, SHA256_INIT, KECCAK256, KECCAK256_ABSORB_PERMUTE and
# BLAKE2 in Jolt's tracer, through the registered inline expansion, on
# known-answer and seeded random inputs, and writes the memory before and after
# each run to a JSON file. The Lean executable `lake exe inline-kat` then
# compares the outputs with the specifications in JoltBytecode/Inlines.
#
# Usage:
#   JOLT_DIR=/path/to/a16z/jolt scripts/inline-kat/build.sh WORK_DIR
#   scripts/inline-kat/run.sh WORK_DIR OUT.json
#   lake exe inline-kat OUT.json
#
# JOLT_DIR is an a16z/jolt checkout (the report in reports/ names the commit
# checked). The script never writes into it: the crate, its Cargo.lock (Jolt's,
# copied) and its target directory live in WORK_DIR/inline-kat.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:?usage: build.sh WORK_DIR}"
: "${JOLT_DIR:?set JOLT_DIR to an a16z/jolt checkout}"
mkdir -p "$work"
work="$(cd "$work" && pwd)"
JOLT_DIR="$(cd "$JOLT_DIR" && pwd)"
[[ -d "$JOLT_DIR/tracer" && -d "$JOLT_DIR/jolt-inlines/sha2" ]] ||
  { echo "inline-kat/build: $JOLT_DIR is not an a16z/jolt checkout" >&2; exit 2; }

crate="$work/inline-kat"
mkdir -p "$crate"
# The Jolt paths go into TOML strings; JSON string escapes are valid there.
python3 - "$HERE/Cargo.toml.in" "$JOLT_DIR" > "$crate/Cargo.toml" <<'PY'
import json, sys
template, jolt = sys.argv[1], sys.argv[2]
text = open(template).read()
for sub in ("tracer", "jolt-inlines/sha2", "jolt-inlines/keccak256", "jolt-inlines/blake2"):
    text = text.replace(f'"@JOLT_DIR@/{sub}"', json.dumps(f"{jolt}/{sub}", ensure_ascii=False))
if "@JOLT_DIR@" in text:
    sys.exit(f"{template}: unexpected @JOLT_DIR@ placeholder")
sys.stdout.write(text)
PY
ln -sfn "$HERE/src" "$crate/src"
# Pin dependency versions and the toolchain to the ones Jolt uses.
cp "$JOLT_DIR/Cargo.lock" "$crate/Cargo.lock"
cp "$JOLT_DIR/rust-toolchain.toml" "$crate/rust-toolchain.toml"
commit="$(git -C "$JOLT_DIR" rev-parse HEAD 2>/dev/null || echo unknown)"
echo "inline-kat/build: building against $JOLT_DIR ($commit)"
(cd "$crate" && cargo build --release --quiet) ||
  { echo "inline-kat/build: cargo build failed" >&2; exit 1; }

{
  printf 'INLINE_KAT=%q\n' "$crate/target/release/inline-kat"
  printf 'JOLT_DIR=%q\n' "$JOLT_DIR"
  printf 'JOLT_COMMIT=%q\n' "$commit"
} > "$work/env.sh"
echo "inline-kat/build: done; settings in $work/env.sh"
