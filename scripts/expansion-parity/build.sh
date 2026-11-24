#!/usr/bin/env bash
# Build only T3's constraint-gen against the read-only checkout JOLT_DIR.
# Usage: JOLT_DIR=/path/to/jolt CARGO_TARGET_DIR=/path/to/cache build.sh WORK_DIR
# Assemble the crate in WORK_DIR, copy Jolt's toolchain/lockfile/patches, and
# record CONSTRAINT_GEN, JOLT_DIR and JOLT_COMMIT in WORK_DIR/env.sh.
# CARGO_TARGET_DIR defaults to WORK_DIR/cargo-target; local repin runs use
# ~/claude-work/jq-repin/cargo-target to reuse the existing artifacts.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:?usage: build.sh WORK_DIR}"
mkdir -p "$work"
work="$(cd "$work" && pwd)"

fail() { echo "expansion-parity/build: $*" >&2; exit 1; }
say() { echo "expansion-parity/build: $*"; }

[[ -n "${JOLT_DIR:-}" ]] || fail "set JOLT_DIR to an a16z/jolt checkout"
[[ -d "$JOLT_DIR/tracer" ]] || fail "JOLT_DIR=$JOLT_DIR has no tracer/ directory"
JOLT_DIR="$(cd "$JOLT_DIR" && pwd)"

crate="$work/expansion-parity"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$work/cargo-target}"
mkdir -p "$CARGO_TARGET_DIR"
CARGO_TARGET_DIR="$(cd "$CARGO_TARGET_DIR" && pwd)"
mkdir -p "$crate"
python3 - "$HERE/Cargo.toml.in" "$JOLT_DIR" > "$crate/Cargo.toml.new" <<'PY'
import json, os, sys, tomllib
template, jolt = sys.argv[1], sys.argv[2]
text = open(template).read()
import re
# The Jolt paths go into TOML strings; JSON string escapes are valid there.
text = re.sub(r'"@JOLT_DIR@(/[^"]*)"',
              lambda m: json.dumps(jolt + m.group(1), ensure_ascii=False), text)
if "@JOLT_DIR@" in text:
    sys.exit(f"{template}: unexpected @JOLT_DIR@ placeholder")
root = tomllib.load(open(os.path.join(jolt, "Cargo.toml"), "rb"))
out = [text.rstrip("\n"), ""]
for source, table in root.get("patch", {}).items():
    out.append(f"[patch.{json.dumps(source)}]")
    for name, spec in table.items():
        spec = dict(spec)
        if "path" in spec:
            spec["path"] = os.path.normpath(os.path.join(jolt, spec["path"]))
        fields = ", ".join(f"{k} = {json.dumps(v)}" for k, v in spec.items())
        out.append(f"{name} = {{ {fields} }}")
    out.append("")
sys.stdout.write("\n".join(out))
PY
mv "$crate/Cargo.toml.new" "$crate/Cargo.toml"
ln -sfn "$HERE/src" "$crate/src"
# Pin dependency versions and the toolchain to the ones Jolt uses.
cp "$JOLT_DIR/Cargo.lock" "$crate/Cargo.lock"
cp "$JOLT_DIR/rust-toolchain.toml" "$crate/rust-toolchain.toml"
commit="$(git -C "$JOLT_DIR" rev-parse HEAD 2>/dev/null || echo unknown)"
say "building constraint-gen against $JOLT_DIR ($commit)"
(cd "$crate" && cargo build --release --quiet --bin constraint-gen) ||
  fail "constraint-gen build failed"

{
  printf 'CONSTRAINT_GEN=%q\n' "$CARGO_TARGET_DIR/release/constraint-gen"
  printf 'JOLT_DIR=%q\n' "$JOLT_DIR"
  printf 'JOLT_COMMIT=%q\n' "$commit"
} > "$work/env.sh"
say "done; settings in $work/env.sh"
