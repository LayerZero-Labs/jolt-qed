#!/usr/bin/env bash
# Build the leanprover/comparator toolchain that scripts/run_comparator.sh and
# the `comparator` CI job use: the `comparator`, `lean4export` and `landrun`
# binaries. Adapted from openvm-fv.
#
# The binaries go to $COMPARATOR_TOOLCHAIN_DIR/bin (default
# $HOME/.comparator-toolchain/bin). The script prints the COMPARATOR_* variables that
# point at them and, inside GitHub Actions, appends them to $GITHUB_ENV.
#
# Requirements: git, elan (lake), and Go for landrun. Landrun uses Linux
# Landlock, so the full toolchain builds only on Linux. Each binary is built only
# when it is missing, so a cached toolchain directory is reused.
#
# Override the pins with COMPARATOR_REV, LEAN4EXPORT_REV and LANDRUN_REV.
#
# Lean v4.35.0 also ships this check as `lake comparator`, and the comparator
# README marks the external tool as deprecated. ci/comparator/README.md says how
# to use the built-in command instead, which needs none of these binaries.
set -euo pipefail

# "bump toolchain to v4.35.0 (#106)", the last code commit before the
# deprecation notice.
COMPARATOR_REV="${COMPARATOR_REV:-e3dcf3083fc53d44b27a4431fabf7d43181583f5}"
# "bump toolchain to v4.35.0 (#56)". Later commits target v4.36.0 release
# candidates.
LEAN4EXPORT_REV="${LEAN4EXPORT_REV:-5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe}"
# The `main` commit openvm-fv pins. openvm-fv found that the tagged releases
# fail with "permission denied" when comparator applies its Landlock ruleset.
LANDRUN_REV="${LANDRUN_REV:-5ed4a3db3a4ad930d577215c6b9abaa19df7f99f}"

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# lean4export must read .olean files from the same Lean version that wrote
# them, so it is built against this repository's toolchain.
TARGET_TOOLCHAIN="$(tr -d '[:space:]' < "$REPO_ROOT/lean-toolchain")"

DIR="${COMPARATOR_TOOLCHAIN_DIR:-$HOME/.comparator-toolchain}"
BIN="$DIR/bin"
SRC="$DIR/src"
mkdir -p "$BIN" "$SRC"

checkout() {
  local url="$1" rev="$2" dest="$3"
  rm -rf "$dest"
  git init -q "$dest"
  git -C "$dest" remote add origin "$url"
  git -C "$dest" fetch -q --depth=1 origin "$rev"
  git -C "$dest" checkout -q FETCH_HEAD
}

if [ ! -x "$BIN/comparator" ]; then
  echo ">> building comparator at $COMPARATOR_REV"
  checkout https://github.com/leanprover/comparator.git "$COMPARATOR_REV" "$SRC/comparator"
  ( cd "$SRC/comparator" && lake build )
  cp "$SRC/comparator/.lake/build/bin/comparator" "$BIN/comparator"
fi

if [ ! -x "$BIN/lean4export" ]; then
  echo ">> building lean4export at $LEAN4EXPORT_REV against $TARGET_TOOLCHAIN"
  checkout https://github.com/leanprover/lean4export.git "$LEAN4EXPORT_REV" "$SRC/lean4export"
  echo "$TARGET_TOOLCHAIN" > "$SRC/lean4export/lean-toolchain"
  ( cd "$SRC/lean4export" && lake build )
  cp "$SRC/lean4export/.lake/build/bin/lean4export" "$BIN/lean4export"
fi

if [ ! -x "$BIN/landrun" ]; then
  command -v go >/dev/null 2>&1 || {
    echo "error: Go is required to build landrun" >&2
    exit 1
  }
  echo ">> building landrun at $LANDRUN_REV"
  checkout https://github.com/Zouuup/landrun.git "$LANDRUN_REV" "$SRC/landrun"
  ( cd "$SRC/landrun" && go build -o "$BIN/landrun" ./cmd/landrun )
fi

echo ">> comparator toolchain:"
ls -l "$BIN"

emit() {
  echo "$1=$2"
  if [ -n "${GITHUB_ENV:-}" ]; then echo "$1=$2" >> "$GITHUB_ENV"; fi
}
emit COMPARATOR_BIN "$BIN/comparator"
emit COMPARATOR_LEAN4EXPORT "$BIN/lean4export"
emit COMPARATOR_LANDRUN "$BIN/landrun"
