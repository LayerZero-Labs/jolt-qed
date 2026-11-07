#!/usr/bin/env bash
# Run the difftest harness on guest programs.
#
# Usage:
#   scripts/difftest/run.sh WORK_DIR [GUEST ...]
#
# Each GUEST is an assembly file (.S), which is assembled and linked with
# guest/link.ld, or a ready ELF. With no GUEST the reproducers in
# guest/repro/ are run. Run build.sh WORK_DIR first.
#
# Environment:
#   CLANG  clang with the RISC-V target (default: Homebrew LLVM, then clang)
#   LLD    ld.lld or rust-lld (default: ld.lld, then rustup's rust-lld)
#   LIMIT  instruction limit per run (default 100000)
#
# Raw traces and per-guest JSON results go to WORK_DIR/results/. The exit
# status is 0 when every guest agrees and 1 otherwise.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:?usage: run.sh WORK_DIR [GUEST ...]}"
shift
work="$(cd "$work" && pwd)"
[[ -f "$work/env.sh" ]] || { echo "difftest/run: run build.sh $work first" >&2; exit 2; }
source "$work/env.sh"

if [[ -z "${CLANG:-}" ]]; then
  for c in /opt/homebrew/opt/llvm/bin/clang /usr/local/opt/llvm/bin/clang clang; do
    if command -v "$c" >/dev/null && "$c" -print-targets 2>/dev/null | grep -q riscv64; then
      CLANG="$c"; break
    fi
  done
fi
[[ -n "${CLANG:-}" ]] || { echo "difftest/run: no clang with the riscv64 target; set CLANG" >&2; exit 2; }
if [[ -z "${LLD:-}" ]]; then
  if command -v ld.lld >/dev/null; then
    LLD="ld.lld"
  else
    LLD="$(find "$(rustc --print sysroot)" -name rust-lld -type f 2>/dev/null | head -1)"
    [[ -n "$LLD" ]] && LLD="$LLD -flavor gnu"
  fi
fi
[[ -n "${LLD:-}" ]] || { echo "difftest/run: no ld.lld or rust-lld; set LLD" >&2; exit 2; }

guests=("$@")
[[ ${#guests[@]} -gt 0 ]] || guests=("$HERE"/guest/repro/*.S)

out="$work/results"
mkdir -p "$out/elf"
status=0
for g in "${guests[@]}"; do
  name="$(basename "${g%.*}")"
  case "$g" in
    *.S)
      elf="$out/elf/$name.elf"
      "$CLANG" --target=riscv64 -march=rv64imac_zicsr -mabi=lp64 -mno-relax \
        -I "$HERE/guest" -c "$g" -o "$out/elf/$name.o"
      $LLD -T "$HERE/guest/link.ld" "$out/elf/$name.o" -o "$elf"
      ;;
    *) elf="$g" ;;
  esac
  python3 "$HERE/difftest.py" --sail "$SAIL_SIM" --config "$SAIL_CONFIG" \
    --jolt "$JOLT_TRACE" --limit "${LIMIT:-100000}" \
    --keep "$out/traces" --json "$out/$name.json" "$elf" || status=1
done
exit $status
