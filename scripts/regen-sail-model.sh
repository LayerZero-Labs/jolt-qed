#!/usr/bin/env bash
# Regenerate the trusted Sail RISC-V Lean model (LeanRV64D) from pinned inputs.
#
# The command line mirrors sail-riscv's own `generated_lean_rv64d` CMake target
# (model/CMakeLists.txt at the pinned revision): `sail_common`, then
# `lean_sail_common`, then `lean_sail_default`, then the module selection and the
# project file. The module selection is the only intended difference from that
# target; it is recorded in sail-import/PROVENANCE.toml.
#
# Usage:
#   scripts/regen-sail-model.sh SAIL_BIN SAIL_RISCV_DIR OUT_DIR [MODULE ...]
#
# With no MODULE arguments, every module is selected (`--all-modules`), which is
# how the original LeanRV64D was produced. OUT_DIR receives Lean_RV64D/.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
sail_bin="${1:?usage: regen-sail-model.sh SAIL_BIN SAIL_RISCV_DIR OUT_DIR [MODULE ...]}"
riscv_dir="${2:?missing SAIL_RISCV_DIR}"
out_dir="${3:?missing OUT_DIR}"
shift 3

[[ "$sail_bin" == /* && "$riscv_dir" == /* && "$out_dir" == /* ]] || {
  echo 'regen-sail-model: paths must be absolute' >&2; exit 2; }
config="${SAIL_CONFIG:-$ROOT/sail-import/rv64d_jolt.json}"
[[ -f "$config" ]] || { echo "regen-sail-model: missing $config" >&2; exit 2; }
command -v z3 >/dev/null || { echo 'regen-sail-model: z3 not found' >&2; exit 2; }

if [[ $# -eq 0 ]]; then
  modules=(--all-modules)
else
  modules=("$@")
fi

required_ver="$(sed -nE 's/^set\(SAIL_REQUIRED_VER ([0-9.]+)\)$/\1/p' "$riscv_dir/CMakeLists.txt")"
[[ -n "$required_ver" ]] || { echo 'regen-sail-model: cannot read SAIL_REQUIRED_VER' >&2; exit 2; }

mkdir -p "$out_dir"
smt_cache="$out_dir/sail_smt_cache"
sail_dir="$(cd "$(dirname "$sail_bin")/../share/sail" && pwd)"

cd "$riscv_dir/model"
SAIL_DIR="$sail_dir" "$sail_bin" \
  --strict-var --strict-bitvector --strict-exponentials \
  --require-version "$required_ver" \
  --memo-z3-path "$smt_cache" \
  --config "$config" \
  --lean \
  --memo-z3 \
  --lean-output-dir "$out_dir" \
  --lean-force-output \
  --lean-non-beq-type instruction \
  --lean-non-beq-type ExecutionResult \
  --lean-non-beq-type Step \
  --lean-noncomputable \
  --lean-noncomputable-function encdec_forwards \
  --lean-noncomputable-function encdec_backwards \
  --lean-noncomputable-function encdec_forwards_matches \
  --lean-noncomputable-function encdec_backwards_matches \
  --lean-noncomputable-function encdec_compressed_forwards \
  --lean-noncomputable-function encdec_compressed_backwards \
  --lean-noncomputable-function encdec_compressed_forwards_matches \
  --lean-noncomputable-function encdec_compressed_backwards_matches \
  --lean-import-file ../handwritten_support/RiscvExtras.lean \
  -o Lean_RV64D \
  riscv.sail_project \
  "${modules[@]}"

# Post-processing of the generated tree.
#
# a. Sail's Lean backend starts every generated file with
#      set_option maxHeartbeats 1_000_000_000
#      set_option maxRecDepth 1_000_000
#    so that no declaration can ever hit a limit. Both lines are dropped: the
#    checked-in model is then elaborated at Lean's default limits (200000
#    heartbeats, maxRecDepth 512), the same as the proofs built on it, and no
#    file-wide limit remains in the closure of the headline theorem. The script
#    fails if a generated file does not carry exactly one copy of each line, so a
#    change in Sail's output cannot pass silently. FakeReal, RiscvExtras and
#    SpecializationV1 are copied verbatim from lean-sail and sail-riscv's
#    handwritten support and carry no header.
#
# b. The three 256-entry S-box tables are single `#v[...]` literals, which need
#    maxRecDepth 526. Each is rewritten as two 128-entry literals joined with `++`;
#    the name and the type stay the same.
#
# c. A few declarations still exceed a default limit. Each gets a
#    `set_option ... in` directly before it (the declarations have no doc comment
#    or attribute), with the smallest value that passes rounded up to the next 50
#    (next 50000 for heartbeats). The values are measured with the options Lake
#    passes when it builds the module (`--tstack`, `--setup`), not with a plain
#    `lean` run, which gave smaller numbers:
#    - is_CSR_accessible, read_CSR and write_CSR are one generated if-chain over
#      every CSR address;
#    - encdec_backwards and encdec_compressed_backwards are the decoder mapping
#      over every instruction, and the two `_matches` functions are the same
#      mapping returning a Bool; both functions that cover the 32-bit encodings also
#      need more heartbeats;
#    - print_rvfi_exec is a debug printer for the RVFI trace format; nothing
#      proved here refers to it.
#    Proofs unfold the CSR chains and the mapping, so they are not split here. The
#    follow-up is for the Sail Lean backend to split long chains into helper
#    definitions, after which these options and the S-box rewrite can go.
#    The script fails unless each listed declaration is found exactly once, if
#    any other limit option is left after step a, or if the tree does not end up
#    with exactly the listed options.
python3 - "$out_dir/Lean_RV64D" <<'EOF'
import pathlib, re, sys

root = pathlib.Path(sys.argv[1])

# ---- a. the file-wide limit overrides -------------------------------------
overrides = ("set_option maxHeartbeats 1_000_000_000", "set_option maxRecDepth 1_000_000")
headerless = {"FakeReal.lean", "RiscvExtras.lean", "SpecializationV1.lean"}
files = sorted(root.glob("LeanRV64D/**/*.lean")) + [root / "LeanRV64D.lean"]
stripped = 0
for path in files:
    lines = path.read_text().split("\n")
    if path.name in headerless:
        if any(line in overrides for line in lines):
            sys.exit(f"regen-sail-model: {path} unexpectedly carries a limit override")
        continue
    for override in overrides:
        if lines.count(override) != 1:
            sys.exit(f"regen-sail-model: {path} has {lines.count(override)} copies of "
                     f"'{override}', expected exactly one")
    path.write_text("\n".join(line for line in lines if line not in overrides))
    stripped += 1
if stripped == 0:
    sys.exit("regen-sail-model: no generated file found")
# No other limit option may remain anywhere in the tree, file-wide or local:
# step c below adds the only ones.
limit_option = re.compile(r"^\s*set_option\s+(maxHeartbeats|maxRecDepth|synthInstance\.maxHeartbeats|maxSize)\b")
for path in files:
    for n, line in enumerate(path.read_text().split("\n"), 1):
        if limit_option.match(line):
            sys.exit(f"regen-sail-model: {path}:{n} sets a limit Sail is not expected to emit: '{line}'")

# ---- b. the three 256-entry S-box tables ----------------------------------
kext = root / "LeanRV64D" / "TypesKext.lean"
text = kext.read_text()
for table in ("sm4_sbox_table", "aes_sbox_fwd_table", "aes_sbox_inv_table"):
    pattern = re.compile(
        r"^(def " + table + r" : \(Vector \(BitVec 8\) 256\) :=\n)  #v\[([^\]\n]*)\]\n", re.M)
    matches = pattern.findall(text)
    if len(matches) != 1:
        sys.exit(f"regen-sail-model: found {len(matches)} definitions of {table}, expected one")
    entries = matches[0][1].split(", ")
    if len(entries) != 256 or not all(re.fullmatch(r"0x[0-9A-F]{2}#8", e) for e in entries):
        sys.exit(f"regen-sail-model: {table} does not have exactly 256 byte entries")
    halves = (", ".join(entries[:128]), ", ".join(entries[128:]))
    text = pattern.sub(
        lambda m: f"{m.group(1)}  (#v[{halves[0]}] ++\n    #v[{halves[1]}])\n", text)
kext.write_text(text)

# ---- c. per-declaration limits ---------------------------------------------
LIMITS = [
    ("SysControl", "is_CSR_accessible", [("maxRecDepth", 900)]),
    ("ZicsrInsts", "read_CSR", [("maxRecDepth", 900)]),
    ("ZicsrInsts", "write_CSR", [("maxRecDepth", 900)]),
    ("InstsEnd", "encdec_backwards", [("maxRecDepth", 1450), ("maxHeartbeats", 250000)]),
    ("InstsEnd", "encdec_backwards_matches", [("maxRecDepth", 1400), ("maxHeartbeats", 250000)]),
    ("InstsEnd", "encdec_compressed_backwards", [("maxRecDepth", 550)]),
    ("InstsEnd", "encdec_compressed_backwards_matches", [("maxRecDepth", 550)]),
    ("RvfiDii", "print_rvfi_exec", [("maxHeartbeats", 1_000_000_000)]),
]
for module, name, options in LIMITS:
    path = root / "LeanRV64D" / f"{module}.lean"
    lines = path.read_text().split("\n")
    pattern = re.compile(r"^(noncomputable )?def " + re.escape(name) + r"( |$)")
    hits = [i for i, line in enumerate(lines) if pattern.match(line)]
    if len(hits) != 1:
        sys.exit(f"regen-sail-model: found {len(hits)} definitions of {name} in {path}, expected one")
    i = hits[0]
    if lines[i - 1] != "":
        sys.exit(f"regen-sail-model: {name} is preceded by '{lines[i - 1]}', expected a blank line")
    lines[i:i] = [f"set_option {option} {value} in" for option, value in options]
    path.write_text("\n".join(lines))
# The tree now carries exactly the limit options listed above, and no other.
expected = sum(len(options) for _, _, options in LIMITS)
found = [(path, line) for path in files for line in path.read_text().split("\n")
         if limit_option.match(line)]
if len(found) != expected or not all(line.endswith(" in") for _, line in found):
    sys.exit(f"regen-sail-model: expected {expected} declaration-local limit options, found {len(found)}")
print("regen-sail-model: post-processed the generated model", file=sys.stderr)
EOF

echo "regen-sail-model: wrote $out_dir/Lean_RV64D" >&2
