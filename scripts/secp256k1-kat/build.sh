#!/usr/bin/env bash
# Build the secp256k1 known-answer driver against a Jolt checkout.
#
# Usage:
#   scripts/secp256k1-kat/build.sh WORK_DIR
#
# Environment:
#   JOLT_DIR  a16z/jolt checkout to build against (required). The driver only
#             reads it: Cargo builds in WORK_DIR/secp256k1-kat/target.
#
# The binary is WORK_DIR/secp256k1-kat/target/release/secp256k1-kat. Run it as
#   secp256k1-kat OUT.json
# and check the result with
#   lake exe secp256k1-kat OUT.json
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:?usage: build.sh WORK_DIR}"
: "${JOLT_DIR:?set JOLT_DIR to an a16z/jolt checkout}"
mkdir -p "$work"
work="$(cd "$work" && pwd)"
JOLT_DIR="$(cd "$JOLT_DIR" && pwd)"
[[ -d "$JOLT_DIR/jolt-inlines/secp256k1" ]] || { echo "secp256k1-kat: $JOLT_DIR has no jolt-inlines/secp256k1" >&2; exit 1; }

crate="$work/secp256k1-kat"
mkdir -p "$crate"
python3 - "$HERE/Cargo.toml.in" "$JOLT_DIR" > "$crate/Cargo.toml" <<'PY'
import json, sys
template, jolt = sys.argv[1], sys.argv[2]
text = open(template).read()
for sub in ("tracer", "jolt-inlines/sdk", "jolt-inlines/secp256k1"):
    text = text.replace(f'"@JOLT_DIR@/{sub}"', json.dumps(f"{jolt}/{sub}", ensure_ascii=False))
if "@JOLT_DIR@" in text:
    sys.exit(f"{template}: unexpected @JOLT_DIR@ placeholder")
sys.stdout.write(text)
PY
ln -sfn "$HERE/src" "$crate/src"
# Pin dependency versions and the toolchain to the ones Jolt uses.
cp "$JOLT_DIR/Cargo.lock" "$crate/Cargo.lock"
cp "$JOLT_DIR/rust-toolchain.toml" "$crate/rust-toolchain.toml"
echo "secp256k1-kat: building against $JOLT_DIR ($(git -C "$JOLT_DIR" rev-parse --short HEAD 2>/dev/null || echo unknown))"
# The driver records this commit in its output.
export JOLT_COMMIT="$(git -C "$JOLT_DIR" rev-parse HEAD 2>/dev/null || echo unknown)"
(cd "$crate" && cargo build --release --quiet)
echo "secp256k1-kat: built $crate/target/release/secp256k1-kat"
