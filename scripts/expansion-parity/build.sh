#!/usr/bin/env bash
# Build the expansion-parity driver against an a16z/jolt checkout.
#
# Usage:
#   scripts/expansion-parity/build.sh WORK_DIR
#
# Environment:
#   JOLT_DIR  a16z/jolt checkout to build against (required; for example
#             ~/claude-work/jolt-inline-pin-a6b6 at a6b6dc717)
#   EXPANSION_PARITY_FEATURES  cargo features of the driver (optional; for
#             example zicsr-remaining against a16z/jolt#2384)
#
# The crate is assembled in WORK_DIR/expansion-parity the way
# scripts/difftest/build.sh assembles jolt-trace: Cargo.toml comes from
# Cargo.toml.in with @JOLT_DIR@ replaced, src/ is a symlink to this directory's
# src/, and Jolt's Cargo.lock and rust-toolchain.toml pin dependency versions
# and the compiler. Jolt's [patch] tables are copied in as well, with relative
# paths made absolute, because the crate is its own workspace and would
# otherwise resolve arkworks from crates.io instead of Jolt's fork.
# WORK_DIR/env.sh records the binary and the Jolt checkout for run.sh.
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
say "building expansion-parity against $JOLT_DIR ($commit)"
features=()
[[ -n "${EXPANSION_PARITY_FEATURES:-}" ]] && features=(--features "$EXPANSION_PARITY_FEATURES")
(cd "$crate" && cargo build --release --quiet ${features[@]+"${features[@]}"}) ||
  fail "expansion-parity build failed"

{
  printf 'EXPANSION_PARITY=%q\n' "$crate/target/release/expansion-parity"
  printf 'JOLT_DIR=%q\n' "$JOLT_DIR"
  printf 'JOLT_COMMIT=%q\n' "$commit"
} > "$work/env.sh"
say "done; settings in $work/env.sh"
