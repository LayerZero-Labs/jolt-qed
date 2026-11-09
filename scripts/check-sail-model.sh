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

# 2b. The memory regions of the configuration are the ones the Lean side uses.
# The Lean side takes its regions from `platformPma` in
# JoltConstraints/WholeRun/Relation.lean, not from the configuration, so the two
# must agree on every field. The configuration's header comments are stripped
# before parsing.
if ! python3 - "$config" "$ROOT/JoltConstraints/WholeRun/Relation.lean" <<'EOF'
import json, re, sys

config_path, lean_path = sys.argv[1], sys.argv[2]
ATTRIBUTES = [
    "cacheable", "coherent", "executable", "readable", "writable",
    "read_idempotent", "write_idempotent", "misaligned_fault", "atomic_support",
    "reservability", "supports_cbo_zero", "supports_pte_read", "supports_pte_write",
]

def problem(message):
    print(f"check-sail-model: memory regions: {message}", file=sys.stderr)
    sys.exit(1)

text = open(config_path).read()
stripped = "\n".join(l for l in text.splitlines() if not l.lstrip().startswith("//"))
json_regions = json.loads(stripped)["memory"]["regions"]

def from_json(region):
    attrs = region["attributes"]
    if sorted(attrs) != sorted(ATTRIBUTES):
        problem(f"configuration attributes are {sorted(attrs)}, expected {sorted(ATTRIBUTES)}")
    fields = {"base": int(region["base"]["value"], 16), "size": int(region["size"]["value"], 16)}
    for key in ATTRIBUTES:
        value = attrs[key]
        fields[key] = ("true" if value else "false") if isinstance(value, bool) else "." + value
    fields["include_in_device_tree"] = "true" if region["include_in_device_tree"] else "false"
    return fields

lean = open(lean_path).read()

def lean_region(name):
    match = re.search(r"def " + re.escape(name) + r" : PMA_Region :=(.*?)(?=\n/--|\ndef |\Z)", lean, re.S)
    if match is None:
        problem(f"Relation.lean has no definition of {name}")
    body = match.group(1)
    fields = {}
    for key in ["base", "size"]:
        m = re.search(r"\b" + key + r" := (0x[0-9A-Fa-f]+)#64", body)
        if m is None:
            problem(f"{name} has no {key}")
        fields[key] = int(m.group(1), 16)
    for key in ATTRIBUTES + ["include_in_device_tree"]:
        found = re.findall(r"\b" + key + r" := (\.?\w+)", body)
        if len(found) != 1:
            problem(f"{name} sets {key} {len(found)} times, expected once")
        fields[key] = found[0]
    return fields

m = re.search(r"def platformPma : List PMA_Region := \[([^\]]*)\]", lean)
if m is None:
    problem("Relation.lean has no platformPma list")
names = [n.strip() for n in m.group(1).split(",") if n.strip()]
if len(names) != len(json_regions):
    problem(f"configuration has {len(json_regions)} regions, platformPma has {len(names)} ({', '.join(names)})")
for index, (name, region) in enumerate(zip(names, json_regions)):
    want, got = from_json(region), lean_region(name)
    for key in ["base", "size"] + ATTRIBUTES + ["include_in_device_tree"]:
        if want[key] != got[key]:
            shown = lambda v: hex(v) if isinstance(v, int) else v
            problem(f"region {index} ({name}): {key} is {shown(want[key])} in the configuration "
                    f"but {shown(got[key])} in Relation.lean")
print(f"check-sail-model: memory regions of the configuration match platformPma ({', '.join(names)})")
EOF
then
  echo FAIL
  fail "the configuration's memory regions differ from Relation.lean"
fi

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
