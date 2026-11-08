#!/usr/bin/env bash
# Build the two simulators the difftest harness compares.
#
#   sail_riscv_sim  the Sail RISC-V C++ emulator, built from the model commit,
#                   model patches and Sail compiler pinned in
#                   sail-import/PROVENANCE.toml
#   jolt-trace      a driver for Jolt's tracer (scripts/difftest/jolt-trace),
#                   built against the a16z/jolt checkout in JOLT_DIR
#
# Usage:
#   scripts/difftest/build.sh WORK_DIR
#
# Environment:
#   JOLT_DIR  a16z/jolt checkout to test (default: WORK_DIR/jolt, cloned from
#             a16z/jolt main on first use and never updated afterwards)
#   SAIL_BIN  Sail compiler to use; it must report the pinned version. Without
#             it the pinned compiler is fetched, patched and built with opam.
#   PROVENANCE_ROOT  jolt-qed checkout whose sail-import/PROVENANCE.toml, and
#             the patches and configuration it names, define the emulator
#             (default: the checkout this script is in). Use it to test
#             another branch's model patches and configuration.
#
# Each step is skipped when its inputs are unchanged: the emulator is rebuilt
# whenever the model commit, the compiler (its commit and patches, or an
# external SAIL_BIN executable) or any recorded model patch changes, so a new
# patch added to PROVENANCE.toml takes effect on the next run. The
# configuration (config.used) is read by the emulator at run time and needs no
# rebuild; this script only checks that the emulator accepts it.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${PROVENANCE_ROOT:-$HERE/../..}" && pwd)"
PROVENANCE="$ROOT/sail-import/PROVENANCE.toml"
work="${1:?usage: build.sh WORK_DIR}"
mkdir -p "$work"
work="$(cd "$work" && pwd)"

fail() { echo "difftest/build: $*" >&2; exit 1; }
say() { echo "difftest/build: $*"; }

# field KEY prints a string field of PROVENANCE.toml; field --list KEY prints
# a list of strings, one per line. Either fails unless the field exists and
# has that type, and no entry is empty or contains a newline.
field() {
  python3 - "$PROVENANCE" "$@" <<'PY'
import sys, tomllib
args = sys.argv[2:]
want_list, key = args[0] == "--list", args[-1]
value = tomllib.load(open(sys.argv[1], "rb"))
for part in key.split("."):
    if not isinstance(value, dict) or part not in value:
        sys.exit(f"PROVENANCE.toml has no {key}")
    value = value[part]
items = value if want_list else [value]
if (want_list and not isinstance(value, list)) or not all(
        isinstance(v, str) and v and "\n" not in v for v in items):
    sys.exit(f"PROVENANCE.toml: {key} is not a {'list of strings' if want_list else 'string'}")
for v in items:
    print(v)
PY
}

# get KEY prints a string field, and stops the build if it cannot.
get() {
  local value
  value="$(field "$1")" || fail "cannot read $1 from $PROVENANCE"
  printf '%s' "$value"
}

sha256() {
  if command -v sha256sum >/dev/null; then sha256sum "$1"; else shasum -a 256 "$1"; fi | cut -d' ' -f1
}

check_sha() {
  local got
  got="$(sha256 "$1")" || fail "cannot hash $1"
  [[ "$got" == "$2" ]] || fail "$1 has sha256 $got; PROVENANCE.toml records $2"
}

# hashes FILE... prints the sha256 of each file, each followed by a space.
hashes() {
  local p h
  for p in "$@"; do
    h="$(sha256 "$p")" || fail "cannot hash $p"
    printf '%s ' "$h"
  done
}

# checked_files FILES_KEY SHAS_KEY sets the array `checked` to the files that
# FILES_KEY lists (paths under ROOT), after checking each against SHAS_KEY.
checked_files() {
  local files shas line i=0
  local -a names=() sums=()
  files="$(field --list "$1")" || fail "cannot read $1 from $PROVENANCE"
  shas="$(field --list "$2")" || fail "cannot read $2 from $PROVENANCE"
  while IFS= read -r line; do [[ -z "$line" ]] || names+=("$line"); done <<< "$files"
  while IFS= read -r line; do [[ -z "$line" ]] || sums+=("$line"); done <<< "$shas"
  [[ ${#names[@]} -eq ${#sums[@]} ]] || fail "$1 and $2 have different lengths"
  checked=()
  while [[ $i -lt ${#names[@]} ]]; do
    check_sha "$ROOT/${names[$i]}" "${sums[$i]}"
    checked+=("$ROOT/${names[$i]}")
    i=$((i + 1))
  done
}

fetch_commit() {
  local dir="$1" url="$2" commit="$3"
  rm -rf "$dir"
  git init -q "$dir"
  git -C "$dir" fetch -q --depth 1 "$url" "$commit"
  git -C "$dir" checkout -q FETCH_HEAD
  [[ "$(git -C "$dir" rev-parse HEAD)" == "$commit" ]] || fail "$url did not check out $commit"
}

checked_files compiler.patches compiler.patch_sha256
compiler_patches=(${checked[@]+"${checked[@]}"})
checked_files model.patches model.patch_sha256
model_patches=(${checked[@]+"${checked[@]}"})
# Each value is read by its own assignment, so a failed read stops the build.
config_used="$(get config.used)"
config_sha="$(get config.used_sha256)"
compiler_commit="$(get compiler.commit)"
compiler_repository="$(get compiler.repository)"
pinned_version="$(get compiler.version)"
model_commit="$(get model.commit)"
model_repository="$(get model.repository)"
project_sha="$(get model.project_file_sha256)"
config="$ROOT/$config_used"
check_sha "$config" "$config_sha"

# 1. The Sail compiler. compiler_key identifies it: the pinned commit and the
# patches applied to it, or, for an external SAIL_BIN, the executable itself.
if [[ -z "${SAIL_BIN:-}" ]]; then
  patch_hashes="$(hashes ${compiler_patches[@]+"${compiler_patches[@]}"})"
  compiler_key="$compiler_commit $patch_hashes"
  SAIL_BIN="$work/sail-install/bin/sail"
  if [[ ! -x "$SAIL_BIN" || "$(cat "$work/sail-install/.key" 2>/dev/null)" != "$compiler_key" ]]; then
    say "building the Sail compiler"
    sail_src="$work/sail"
    fetch_commit "$sail_src" "$compiler_repository" "$compiler_commit"
    for patch in ${compiler_patches[@]+"${compiler_patches[@]}"}; do
      git -C "$sail_src" apply "$patch"
    done
    (
      cd "$sail_src"
      opam install -y --deps-only .
      opam exec -- dune build --release
      opam exec -- dune install --release --prefix "$work/sail-install"
    )
    echo "$compiler_key" > "$work/sail-install/.key"
  fi
else
  sail_exe="$(command -v "$SAIL_BIN")" || fail "SAIL_BIN=$SAIL_BIN is not an executable"
  sail_hash="$(hashes "$sail_exe")"
  compiler_key="external $sail_exe $sail_hash"
fi
version="$("$SAIL_BIN" --version)" || fail "$SAIL_BIN --version failed"
[[ "$version" == *"$pinned_version"* ]] ||
  fail "Sail reports '$version'; PROVENANCE.toml records version $pinned_version"

# 2. The sail-riscv C++ emulator.
patch_hashes="$(hashes ${model_patches[@]+"${model_patches[@]}"})"
model_key="$model_commit $compiler_key $version $patch_hashes"
riscv="$work/sail-riscv"
sim="$riscv/build/c_emulator/sail_riscv_sim"
if [[ ! -x "$sim" || "$(cat "$riscv/.difftest-key" 2>/dev/null)" != "$model_key" ]]; then
  say "building sail_riscv_sim"
  fetch_commit "$riscv" "$model_repository" "$model_commit"
  check_sha "$riscv/model/riscv.sail_project" "$project_sha"
  for patch in ${model_patches[@]+"${model_patches[@]}"}; do
    git -C "$riscv" apply "$patch"
  done
  # Upstream validates its bundled default configurations after linking the
  # emulator. A model patch that adds required configuration keys, as the Jolt
  # hart patch does, makes those defaults invalid; the configuration actually
  # used is validated below instead.
  python3 - "$riscv/c_emulator/CMakeLists.txt" <<'PY'
import re, sys
path = sys.argv[1]
text = open(path).read()
text, n = re.subn(r"\n# After the emulator is built, use it to validate the generated config files\.\n"
                  r"foreach \(config_filename IN LISTS generated_config_filenames\).*?endforeach\(\)\n",
                  "\n", text, flags=re.S)
if n != 1:
    sys.exit(f"{path}: default-configuration validation block not found")
open(path, "w").write(text)
PY
  cmake -S "$riscv" -B "$riscv/build" -DCMAKE_BUILD_TYPE=RelWithDebInfo \
    -DSAIL_BIN="$SAIL_BIN" > "$work/cmake.log" 2>&1 ||
    { tail -30 "$work/cmake.log" >&2; fail "cmake configure failed"; }
  cmake --build "$riscv/build" --target sail_riscv_sim -j "$(getconf _NPROCESSORS_ONLN)" \
    > "$work/sail-build.log" 2>&1 ||
    { tail -30 "$work/sail-build.log" >&2; fail "sail_riscv_sim build failed"; }
  echo "$model_key" > "$riscv/.difftest-key"
fi
"$sim" --config "$config" --validate-config > /dev/null ||
  fail "sail_riscv_sim rejects $config"

# 3. jolt-trace.
JOLT_DIR="${JOLT_DIR:-$work/jolt}"
if [[ ! -d "$JOLT_DIR/tracer" ]]; then
  [[ "$JOLT_DIR" == "$work/jolt" ]] || fail "JOLT_DIR=$JOLT_DIR has no tracer/ directory"
  say "cloning a16z/jolt"
  git clone -q --filter=blob:none https://github.com/a16z/jolt "$JOLT_DIR"
fi
JOLT_DIR="$(cd "$JOLT_DIR" && pwd)"
crate="$work/jolt-trace"
mkdir -p "$crate"
# The Jolt paths go into TOML strings; JSON string escapes are valid there.
python3 - "$HERE/jolt-trace/Cargo.toml.in" "$JOLT_DIR" > "$crate/Cargo.toml" <<'PY'
import json, sys
template, jolt = sys.argv[1], sys.argv[2]
text = open(template).read()
for sub in ("tracer", "common", "crates/jolt-riscv"):
    text = text.replace(f'"@JOLT_DIR@/{sub}"', json.dumps(f"{jolt}/{sub}", ensure_ascii=False))
if "@JOLT_DIR@" in text:
    sys.exit(f"{template}: unexpected @JOLT_DIR@ placeholder")
sys.stdout.write(text)
PY
ln -sfn "$HERE/jolt-trace/src" "$crate/src"
# Pin dependency versions and the toolchain to the ones Jolt uses.
cp "$JOLT_DIR/Cargo.lock" "$crate/Cargo.lock"
cp "$JOLT_DIR/rust-toolchain.toml" "$crate/rust-toolchain.toml"
say "building jolt-trace against $JOLT_DIR ($(git -C "$JOLT_DIR" rev-parse --short HEAD 2>/dev/null || echo unknown))"
(cd "$crate" && cargo build --release --quiet) || fail "jolt-trace build failed"

{
  printf 'SAIL_SIM=%q\n' "$sim"
  printf 'SAIL_CONFIG=%q\n' "$config"
  printf 'JOLT_TRACE=%q\n' "$crate/target/release/jolt-trace"
  printf 'JOLT_DIR=%q\n' "$JOLT_DIR"
} > "$work/env.sh"
say "done; settings in $work/env.sh"
