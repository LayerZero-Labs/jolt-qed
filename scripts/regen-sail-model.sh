#!/usr/bin/env bash
# Regenerate the trusted Sail RISC-V Lean model (LeanRV64D) from pinned inputs.
#
# The command line mirrors sail-riscv's own `generated_lean_rv64d` CMake target
# (model/CMakeLists.txt at the pinned revision): `sail_common`, then
# `lean_sail_common`, then `lean_sail_default`, then the module selection and the
# project file. The module selection is the only intended difference from that
# target; it is recorded in sail-import/PROVENANCE.toml. After generation, one
# text rewrite is applied to RvfiDii.lean (see the end of this script and
# [postprocess] in PROVENANCE.toml).
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

# Work around leanprover/lean4#13858 (fixed by leanprover/lean4#15682, not in
# Lean 4.35): a run of non-final `pure (...)` statements in a `do` block takes
# time exponential in the run's length to elaborate. `print_rvfi_exec` in
# RvfiDii.lean has a run of 18, which alone takes 20 to 30 minutes on CI.
# `discard <| pure (...)` is also a no-op statement and elaborates in linear
# time. Nothing in the model or the proofs calls `print_rvfi_exec`.
# mit-pdos/xv6iris applies the same rewrite.
rvfi="$out_dir/Lean_RV64D/LeanRV64D/RvfiDii.lean"
sed 's/(pure (print_/(discard <| pure (print_/g' "$rvfi" > "$rvfi.tmp"
mv "$rvfi.tmp" "$rvfi"
if grep -q '(pure (print_' "$rvfi"; then
  echo 'regen-sail-model: RvfiDii.lean rewrite left a `(pure (print_` behind' >&2
  exit 1
fi

echo "regen-sail-model: wrote $out_dir/Lean_RV64D" >&2
