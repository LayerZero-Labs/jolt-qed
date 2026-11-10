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
#   CLANG, LLD  guest toolchain (see toolchain.sh); only .S guests need it
#   LIMIT       instruction limit per run (positive; default 100000)
#   TIMEOUT     seconds each simulator may run per guest (default 600)
#   EXPECT_CODE exit code every guest must end with when both simulators
#               agree (unset: any code); see difftest.py --expect-code
#   JOLT_MSTATUS_OR  bits Jolt ORs into its mstatus register on a read
#               (default 0; 0x1800 for Jolt versions that store only MIE and MPIE)
#   IGNORE_BITS space-separated CSR=MASK pairs left out of the comparison,
#               such as "mstatus=0xa00000000" for UXL/SXL on a configuration
#               with S- and U-mode
#   RESULTS     name of the results directory under WORK_DIR (default results)
#
# Raw traces and per-guest JSON results go to WORK_DIR/$RESULTS/. A guest
# whose first difference is a spec-legal reservation-policy SC is counted
# apart (see difftest.py). The exit status is 2 on a harness error (a guest
# that does not assemble, or difftest.py exiting with 2), which stops the run;
# otherwise 1 when any guest differs, and 0 when none does.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
work="${1:?usage: run.sh WORK_DIR [GUEST ...]}"
shift
work="$(cd "$work" && pwd)"
[[ -f "$work/env.sh" ]] || { echo "difftest/run: run build.sh $work first" >&2; exit 2; }
source "$work/env.sh"

guests=("$@")
[[ ${#guests[@]} -gt 0 ]] || guests=("$HERE"/guest/repro/*.S)

out="$work/${RESULTS:-results}"
mkdir -p "$out/elf"
options=()
read -r -a bits <<< "${IGNORE_BITS:-}"
for i in ${bits[@]+"${bits[@]}"}; do options+=(--ignore-bits "$i"); done
[[ -z "${EXPECT_CODE:-}" ]] || options+=(--expect-code "$EXPECT_CODE")
agree=0 policy=0 differ=0
for g in "${guests[@]}"; do
  name="$(basename "${g%.*}")"
  case "$g" in
    *.S)
      # The guest toolchain is needed only here, so ELF-only runs work without it.
      declare -F assemble >/dev/null || source "$HERE/toolchain.sh"
      elf="$out/elf/$name.elf"
      assemble "$g" "$elf" || { echo "difftest/run: cannot assemble $g" >&2; exit 2; }
      ;;
    *) elf="$g" ;;
  esac
  status=0
  python3 "$HERE/difftest.py" --sail "$SAIL_SIM" --config "$SAIL_CONFIG" \
    --jolt "$JOLT_TRACE" --limit "${LIMIT:-100000}" --timeout "${TIMEOUT:-600}" \
    --jolt-mstatus-or "${JOLT_MSTATUS_OR:-0}" ${options[@]+"${options[@]}"} \
    --keep "$out/traces" --json "$out/$name.json" "$elf" || status=$?
  case $status in
    0) agree=$((agree + 1)) ;;
    3) policy=$((policy + 1)) ;;
    1) differ=$((differ + 1)) ;;
    *) echo "difftest/run: harness error on $g" >&2; exit 2 ;;
  esac
done
echo "difftest/run: $agree agree, $policy reservation policy, $differ differ (results in $out)"
[[ $differ -eq 0 ]]
