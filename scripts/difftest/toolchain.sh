# Guest toolchain for the difftest scripts; source it, don't run it.
#
# Sets CLANG (clang with the riscv64 target) and LLD (ld.lld or rust-lld),
# honouring values already in the environment, and defines
#   assemble SRC ELF [CLANG_FLAGS...]
# which assembles SRC for RV64IMAC with Zicsr and Zifencei and links it with
# guest/link.ld.

DIFFTEST_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

if [[ -z "${CLANG:-}" ]]; then
  for c in /opt/homebrew/opt/llvm/bin/clang /usr/local/opt/llvm/bin/clang clang; do
    if command -v "$c" >/dev/null && "$c" -print-targets 2>/dev/null | grep -q riscv64; then
      CLANG="$c"; break
    fi
  done
fi
[[ -n "${CLANG:-}" ]] || { echo "difftest: no clang with the riscv64 target; set CLANG" >&2; exit 2; }
if [[ -z "${LLD:-}" ]]; then
  if command -v ld.lld >/dev/null; then
    LLD="ld.lld"
  else
    LLD="$(find "$(rustc --print sysroot)" -name rust-lld -type f 2>/dev/null | head -1)"
    [[ -n "$LLD" ]] && LLD="$LLD -flavor gnu"
  fi
fi
[[ -n "${LLD:-}" ]] || { echo "difftest: no ld.lld or rust-lld; set LLD" >&2; exit 2; }

assemble() {
  local src="$1" elf="$2"
  shift 2
  "$CLANG" --target=riscv64 -march=rv64imac_zicsr_zifencei -mabi=lp64 -mno-relax \
    -I "$DIFFTEST_DIR/guest" "$@" -c "$src" -o "${elf%.elf}.o" &&
    $LLD -T "$DIFFTEST_DIR/guest/link.ld" "${elf%.elf}.o" -o "$elf"
}
