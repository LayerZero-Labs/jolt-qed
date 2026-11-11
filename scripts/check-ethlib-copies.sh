#!/usr/bin/env bash
# Check that the hash specifications copied from EthLib still match EthLib.
#
# jolt-qed copies the specifications of its hash inlines from ethereum/EthLib
# (CC0-1.0) instead of importing EthLib (docs/inline-precompiles.md, section
# 5.6). Each copy records the EthLib commit it was taken from. This script
# extracts every declaration (with its docstring) from each copy, finds the
# declaration of the same full name in the EthLib source files at that commit,
# and compares the two texts after renaming EthLib's namespaces to jolt-qed's:
#
#   EthLib.Cryptography.Hash.X    ->  JoltSpec.X
#   EthLib.Cryptography.Models.X  ->  JoltSpec.X
#   EthLib.Base                   ->  JoltSpec.Base
#
# It fails if a copied declaration differs from EthLib's, if a copy holds a
# declaration EthLib does not have, or if a copy records another commit.
#
# Usage:
#   scripts/check-ethlib-copies.sh [ETHLIB_DIR]
#
# ETHLIB_DIR is an ethereum/EthLib checkout. The script reads the files at the
# recorded commit with `git show`, so the checkout may be at any revision, but
# it must contain that commit. Without ETHLIB_DIR the script fetches the
# commit into a temporary directory.
#
# A CI job runs it as
#   scripts/check-ethlib-copies.sh
# which needs only git, python3 and network access to github.com.
#
# To move to a newer EthLib commit: copy the changed declarations, update the
# commit in each copy's header and in ETHLIB_COMMIT below, and rerun.
set -euo pipefail

ETHLIB_COMMIT=5310b3ec007b05a2bfe33b01125392b07df5f636
ETHLIB_URL=https://github.com/ethereum/EthLib

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"

if [[ $# -ge 1 ]]; then
  ethlib="$(cd "$1" && pwd)"
else
  ethlib="$(mktemp -d)"
  trap 'rm -rf "$ethlib"' EXIT
  git init -q "$ethlib"
  git -C "$ethlib" fetch -q --depth 1 "$ETHLIB_URL" "$ETHLIB_COMMIT"
fi
git -C "$ethlib" cat-file -e "$ETHLIB_COMMIT^{commit}" 2>/dev/null ||
  { echo "check-ethlib-copies: $ethlib does not contain commit $ETHLIB_COMMIT" >&2; exit 2; }

python3 - "$ROOT" "$ethlib" "$ETHLIB_COMMIT" <<'PY'
import re
import subprocess
import sys

root, ethlib, commit = sys.argv[1:4]

# Each copy and the EthLib files its declarations come from.
COPIES = {
    "JoltBytecode/Inlines/Sha256/Spec.lean": [
        "EthLib/Cryptography/Hash/Sha256.lean",
        "EthLib/Cryptography/Proofs/Hash/Sha256.lean",
    ],
    "JoltBytecode/Inlines/Keccak256/Spec.lean": [
        "EthLib/Base/Bytes.lean",
        "EthLib/Cryptography/Hash/Keccak.lean",
        "EthLib/Cryptography/Proofs/Hash/Keccak.lean",
        "EthLib/Cryptography/Proofs/Models/KeccakBits.lean",
        "EthLib/Cryptography/Proofs/Hash/KeccakBitsPermutation.lean",
    ],
    "JoltBytecode/Inlines/Blake2b/Spec.lean": [
        "EthLib/Base/Proofs/BitVec.lean",
        "EthLib/Cryptography/Hash/Blake2b.lean",
        "EthLib/Cryptography/Proofs/Hash/Blake2b.lean",
    ],
}

RENAMES = [
    ("EthLib.Cryptography.Hash.", "JoltSpec."),
    ("EthLib.Cryptography.Models.", "JoltSpec."),
    ("EthLib.Cryptography.Hash", "JoltSpec"),
    ("EthLib.Base", "JoltSpec.Base"),
]


def normalize(text):
    for old, new in RENAMES:
        text = text.replace(old, new)
    return text


DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:def|theorem|lemma|abbrev|structure|inductive|class|instance)\s+([^\s(:{\[]+)"
)
# Lines at column 0 that end the declaration before them.
BOUNDARY = re.compile(r"^(?:/--|/-!|namespace\s|end\b|open\s|section\b|--|@\[|private\s|"
                      r"protected\s|noncomputable\s|def\s|theorem\s|lemma\s|abbrev\s|"
                      r"structure\s|inductive\s|class\s|instance\s|import\s|module\b|"
                      r"public\s|@\[expose\])")


def declarations(text):
    """Map each declaration's full name to its text, docstring included."""
    lines = text.split("\n")
    stack, decls, i = [], {}, 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^namespace\s+(\S+)", line)
        if m:
            stack.append(m.group(1))
            i += 1
            continue
        m = re.match(r"^end\s+(\S+)", line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
            i += 1
            continue
        start = i
        if line.startswith("/--"):
            # A docstring: it belongs to the declaration after it.
            while "-/" not in lines[i]:
                i += 1
            i += 1
            if i >= len(lines) or not DECL.match(lines[i]):
                continue
        m = DECL.match(lines[i]) if i < len(lines) else None
        if not m:
            i = start + 1
            continue
        j = i + 1
        while j < len(lines) and not BOUNDARY.match(lines[j]):
            j += 1
        body = "\n".join(lines[start:j]).rstrip()
        name = ".".join(stack + [m.group(1)])
        if name in decls:
            sys.exit(f"duplicate declaration {name}")
        decls[name] = body
        i = j
    return decls


def ethlib_file(path):
    return subprocess.run(["git", "-C", ethlib, "show", f"{commit}:{path}"],
                          check=True, capture_output=True, text=True).stdout


failures, checked = [], 0
for copy, sources in COPIES.items():
    text = open(f"{root}/{copy}").read()
    if commit not in text:
        failures.append(f"{copy}: the header does not record EthLib commit {commit}")
    ours = declarations(text)
    theirs = {}
    for source in sources:
        for name, body in declarations(normalize(ethlib_file(source))).items():
            theirs.setdefault(name, (source, body))
    for name, body in ours.items():
        if name not in theirs:
            failures.append(f"{copy}: {name} is not a declaration of {', '.join(sources)}")
            continue
        source, original = theirs[name]
        if body != original:
            failures.append(f"{copy}: {name} differs from {source}\n--- EthLib\n{original}\n"
                            f"--- jolt-qed\n{body}")
        else:
            checked += 1
    print(f"{copy}: {len(ours)} declarations")

for failure in failures:
    print(f"MISMATCH {failure}")
print(f"check-ethlib-copies: {checked} declarations match EthLib {commit[:12]}, "
      f"{len(failures)} mismatches")
sys.exit(1 if failures else 0)
PY
