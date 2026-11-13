#!/usr/bin/env bash
# Build the inline probe three times against an a16z/jolt checkout.
#
# Usage:
#   JOLT_DIR=~/claude-work/jolt-inline-pin-a6b6 scripts/inline-open-questions/build.sh WORK_DIR
#
# The crate is assembled in WORK_DIR/inline-probe the way
# scripts/expansion-parity/build.sh assembles its driver: Cargo.toml comes
# from Cargo.toml.in with @JOLT_DIR@ replaced and Jolt's [patch] tables
# appended with absolute paths, src/ is a symlink to this directory's src/,
# and Jolt's Cargo.lock and rust-toolchain.toml pin versions and the compiler.
# The three builds run one after another and differ only in cargo features:
#   WORK_DIR/bin/inline-probe-nofeat   no inline crate linked
#   WORK_DIR/bin/inline-probe-depsha2  jolt-inlines-sha2 a dependency, never named
#   WORK_DIR/bin/inline-probe-inlines  all four in-scope inline crates named with `use ... as _`
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:?usage: build.sh WORK_DIR}"
mkdir -p "$work/bin"
work="$(cd "$work" && pwd)"

fail() { echo "inline-open-questions/build: $*" >&2; exit 1; }
[[ -n "${JOLT_DIR:-}" ]] || fail "set JOLT_DIR to an a16z/jolt checkout"
[[ -d "$JOLT_DIR/tracer" ]] || fail "JOLT_DIR=$JOLT_DIR has no tracer/ directory"
JOLT_DIR="$(cd "$JOLT_DIR" && pwd)"

crate="$work/inline-probe"
mkdir -p "$crate"
python3 - "$HERE/Cargo.toml.in" "$JOLT_DIR" > "$crate/Cargo.toml.new" <<'PY'
import json, os, re, sys, tomllib
template, jolt = sys.argv[1], sys.argv[2]
text = re.sub(r'"@JOLT_DIR@(/[^"]*)"',
              lambda m: json.dumps(jolt + m.group(1), ensure_ascii=False),
              open(template).read())
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
cp "$JOLT_DIR/Cargo.lock" "$crate/Cargo.lock"
cp "$JOLT_DIR/rust-toolchain.toml" "$crate/rust-toolchain.toml"
echo "inline-open-questions/build: building against $JOLT_DIR ($(git -C "$JOLT_DIR" rev-parse HEAD 2>/dev/null || echo unknown))"

for variant in nofeat depsha2 inlines; do
  case "$variant" in
    nofeat) features=() ;;
    depsha2) features=(--features dep-sha2) ;;
    inlines) features=(--features inlines) ;;
  esac
  (cd "$crate" && cargo build --release --quiet ${features[@]+"${features[@]}"}) ||
    fail "build of $variant failed"
  target="${CARGO_TARGET_DIR:-$crate/target}"
  cp "$target/release/inline-probe" "$work/bin/inline-probe-$variant"
done
echo "inline-open-questions/build: binaries in $work/bin"
