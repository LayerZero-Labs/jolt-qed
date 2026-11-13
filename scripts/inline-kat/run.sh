#!/usr/bin/env bash
# Run inline-kat (built by build.sh in WORK_DIR) and write its cases to OUT.json.
#
# Usage:
#   scripts/inline-kat/run.sh WORK_DIR OUT.json
#
# Then compare with the Lean specifications:
#   lake exe inline-kat OUT.json
set -euo pipefail

work="${1:?usage: run.sh WORK_DIR OUT.json}"
out="${2:?usage: run.sh WORK_DIR OUT.json}"
# shellcheck disable=SC1091
source "$work/env.sh"
"$INLINE_KAT" --jolt-commit "$JOLT_COMMIT" "$out"
