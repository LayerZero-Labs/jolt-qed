#!/usr/bin/env bash
# Check that the trusted generated model (LeanRV64D/ and LeanRV64D.lean) is
# exactly what the pinned generator produces from the pinned inputs.
#
# Every pin, patch, configuration and module selection is read from
# sail-import/PROVENANCE.toml. The script fetches the Sail compiler and the
# sail-riscv model at their pinned commits, checks every recorded digest,
# applies the recorded patches, builds Sail with opam, runs
# scripts/regen-sail-model.sh, and fails unless the result is byte-for-byte
# identical to the checked-in tree.
#
# Usage:
#   scripts/check-sail-model.sh WORK_DIR
#
# Needs git, python3 (3.11 or later), z3 and an initialised opam switch that can
# build Sail. Set SAIL_BIN to an absolute path to skip building Sail; that binary
# must already be the pinned commit with the pinned patches applied.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PROVENANCE="$ROOT/sail-import/PROVENANCE.toml"
work="${1:?usage: check-sail-model.sh WORK_DIR}"
mkdir -p "$work"
work="$(cd "$work" && pwd)"

fail() { echo "check-sail-model: $*" >&2; exit 1; }

# Print a PROVENANCE.toml field (dotted key); list values print one per line.
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

# Check each file listed under KEY against the digest at the same position in
# SHA_KEY, then print the absolute paths.
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

# The digest recorded in [output]: sha256 over the `sha256sum`-style lines of
# LeanRV64D/**/*.lean (C-locale order) followed by LeanRV64D.lean.
tree_sha256() {
  (
    cd "$1"
    find LeanRV64D -name '*.lean' -print0 | LC_ALL=C sort -z | while IFS= read -r -d '' file; do
      echo "$(sha256 "$file")  $file"
    done
    echo "$(sha256 LeanRV64D.lean)  LeanRV64D.lean"
  ) | if command -v sha256sum >/dev/null; then sha256sum; else shasum -a 256; fi | cut -d' ' -f1
}

# 1. The checked-in tree must match the recorded digest.
recorded="$(field output.tree_sha256)"
actual="$(tree_sha256 "$ROOT")"
[[ "$actual" == "$recorded" ]] ||
  fail "checked-in model has tree digest $actual; PROVENANCE.toml records $recorded"

# 2. Inputs kept in this repository.
compiler_patches=($(checked_files compiler.patches compiler.patch_sha256))
model_patches=($(checked_files model.patches model.patch_sha256))
check_sha "$ROOT/$(field config.upstream)" "$(field config.upstream_sha256)"
config="$ROOT/$(field config.used)"
check_sha "$config" "$(field config.used_sha256)"

# 3. The Sail compiler.
if [[ -z "${SAIL_BIN:-}" ]]; then
  sail_src="$work/sail"
  fetch_commit "$sail_src" "$(field compiler.repository)" "$(field compiler.commit)"
  for patch in "${compiler_patches[@]}"; do git -C "$sail_src" apply "$patch"; done
  (
    cd "$sail_src"
    opam install -y --deps-only .
    opam exec -- dune build --release
    opam exec -- dune install --release --prefix "$work/sail-install"
  )
  SAIL_BIN="$work/sail-install/bin/sail"
fi
version="$("$SAIL_BIN" --version)"
[[ "$version" == *"$(field compiler.version)"* ]] ||
  fail "Sail reports '$version'; PROVENANCE.toml records version $(field compiler.version)"

# 4. The sail-riscv model.
riscv="$work/sail-riscv"
fetch_commit "$riscv" "$(field model.repository)" "$(field model.commit)"
check_sha "$riscv/model/riscv.sail_project" "$(field model.project_file_sha256)"
for patch in "${model_patches[@]}"; do git -C "$riscv" apply "$patch"; done

# 5. Regenerate and compare.
out="$work/out"
rm -rf "$out"
SAIL_CONFIG="$config" "$ROOT/scripts/regen-sail-model.sh" \
  "$SAIL_BIN" "$riscv" "$out" $(field modules.selected) > "$work/regen.log" 2>&1 ||
  { tail -50 "$work/regen.log" >&2; fail "regeneration failed"; }

# LeanRV64D/LICENSE is the only checked-in file the generator does not write.
generated="$out/Lean_RV64D"
if ! diff -rq -x LICENSE "$generated/LeanRV64D" "$ROOT/LeanRV64D" ||
   ! diff -q "$generated/LeanRV64D.lean" "$ROOT/LeanRV64D.lean"; then
  fail "the checked-in model differs from the regenerated one (listed above)"
fi
[[ "$(tree_sha256 "$generated")" == "$recorded" ]] || fail "regenerated tree digest differs"
echo "check-sail-model: LeanRV64D matches the pinned generator output ($recorded)"
