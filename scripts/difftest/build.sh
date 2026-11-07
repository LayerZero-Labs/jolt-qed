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
#
# Each step is skipped when its inputs are unchanged: the emulator is rebuilt
# whenever the model commit, the compiler commit or any recorded patch changes,
# so a new patch added to PROVENANCE.toml takes effect on the next run. The
# configuration (config.used) is read by the emulator at run time and needs no
# rebuild; this script only checks that the emulator accepts it.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
PROVENANCE="$ROOT/sail-import/PROVENANCE.toml"
work="${1:?usage: build.sh WORK_DIR}"
mkdir -p "$work"
work="$(cd "$work" && pwd)"

fail() { echo "difftest/build: $*" >&2; exit 1; }
say() { echo "difftest/build: $*"; }

field() {
  python3 - "$PROVENANCE" "$1" <<'EOF'
import sys, tomllib
value = tomllib.load(open(sys.argv[1], "rb"))
for key in sys.argv[2].split("."):
    value = value[key]
print("\n".join(value) if isinstance(value, list) else value)
EOF
}

sha256() {
  if command -v sha256sum >/dev/null; then sha256sum "$1"; else shasum -a 256 "$1"; fi | cut -d' ' -f1
}

check_sha() {
  local got
  got="$(sha256 "$1")"
  [[ "$got" == "$2" ]] || fail "$1 has sha256 $got; PROVENANCE.toml records $2"
}

checked_files() {
  local files shas i
  files=($(field "$1"))
  shas=($(field "$2"))
  [[ ${#files[@]} -eq ${#shas[@]} ]] || fail "$1 and $2 have different lengths"
  for i in "${!files[@]}"; do
    check_sha "$ROOT/${files[$i]}" "${shas[$i]}"
    echo "$ROOT/${files[$i]}"
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

compiler_patches=($(checked_files compiler.patches compiler.patch_sha256))
model_patches=($(checked_files model.patches model.patch_sha256))
config="$ROOT/$(field config.used)"
check_sha "$config" "$(field config.used_sha256)"

# 1. The Sail compiler.
if [[ -z "${SAIL_BIN:-}" ]]; then
  compiler_key="$(field compiler.commit) $(printf '%s\n' "${compiler_patches[@]}" | while read -r p; do sha256 "$p"; done | tr '\n' ' ')"
  SAIL_BIN="$work/sail-install/bin/sail"
  if [[ ! -x "$SAIL_BIN" || "$(cat "$work/sail-install/.key" 2>/dev/null)" != "$compiler_key" ]]; then
    say "building the Sail compiler"
    sail_src="$work/sail"
    fetch_commit "$sail_src" "$(field compiler.repository)" "$(field compiler.commit)"
    for patch in "${compiler_patches[@]}"; do git -C "$sail_src" apply "$patch"; done
    (
      cd "$sail_src"
      opam install -y --deps-only .
      opam exec -- dune build --release
      opam exec -- dune install --release --prefix "$work/sail-install"
    )
    echo "$compiler_key" > "$work/sail-install/.key"
  fi
fi
version="$("$SAIL_BIN" --version)"
[[ "$version" == *"$(field compiler.version)"* ]] ||
  fail "Sail reports '$version'; PROVENANCE.toml records version $(field compiler.version)"

# 2. The sail-riscv C++ emulator.
model_key="$(field model.commit) $("$SAIL_BIN" --version) $(for p in "${model_patches[@]}"; do sha256 "$p"; done | tr '\n' ' ')"
riscv="$work/sail-riscv"
sim="$riscv/build/c_emulator/sail_riscv_sim"
if [[ ! -x "$sim" || "$(cat "$riscv/.difftest-key" 2>/dev/null)" != "$model_key" ]]; then
  say "building sail_riscv_sim"
  fetch_commit "$riscv" "$(field model.repository)" "$(field model.commit)"
  check_sha "$riscv/model/riscv.sail_project" "$(field model.project_file_sha256)"
  for patch in "${model_patches[@]}"; do git -C "$riscv" apply "$patch"; done
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
sed "s|@JOLT_DIR@|$JOLT_DIR|g" "$HERE/jolt-trace/Cargo.toml.in" > "$crate/Cargo.toml"
ln -sfn "$HERE/jolt-trace/src" "$crate/src"
# Pin dependency versions and the toolchain to the ones Jolt uses.
cp "$JOLT_DIR/Cargo.lock" "$crate/Cargo.lock"
cp "$JOLT_DIR/rust-toolchain.toml" "$crate/rust-toolchain.toml"
say "building jolt-trace against $JOLT_DIR ($(git -C "$JOLT_DIR" rev-parse --short HEAD 2>/dev/null || echo unknown))"
(cd "$crate" && cargo build --release --quiet) || fail "jolt-trace build failed"

cat > "$work/env.sh" <<EOF
SAIL_SIM="$sim"
SAIL_CONFIG="$config"
JOLT_TRACE="$crate/target/release/jolt-trace"
JOLT_DIR="$JOLT_DIR"
EOF
say "done; settings in $work/env.sh"
