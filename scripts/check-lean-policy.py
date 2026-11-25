#!/usr/bin/env python3
"""Fail on Lean source that weakens what the build checks.

Usage: scripts/check-lean-policy.py

Scans every .lean file of the Lake libraries (JoltBytecode/, JoltConstraints/, LeanRV64D/ and
the root files JoltBytecode.lean, JoltConstraints.lean, LeanRV64D.lean), with comments and
string contents removed, and fails on:

- `sorry` and `admit`;
- an `axiom` declaration that scripts/lean-policy-allowlist.toml does not list;
- `native_decide`, `bv_decide`, `decide +kernel` (or `kernel := true`), and the terms they
  produce (`Lean.ofReduceBool`, `Lean.trustCompiler`);
- `debug.skipKernelTC`;
- the options `maxHeartbeats`, `synthInstance.*`, `maxRecDepth` and `respectTransparency false`,
  except the `maxRecDepth` lines the allowlist names, each with the definition it precedes.

It also fails when an allowlist entry no longer matches the source, so the allowlist cannot
outlive what it allows.

`#audit_statements` in JoltConstraints/Audit/Statements.lean checks the axioms of the headline
theorems in Lean; this script catches the same mechanisms anywhere in the source, including
code no headline theorem uses yet.

Exit status: 0 when the source passes, 1 otherwise.
"""

import pathlib
import re
import sys
import tomllib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from lean_source import strip_comments  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
ALLOWLIST = ROOT / "scripts/lean-policy-allowlist.toml"
LIBRARIES = ("JoltBytecode", "JoltConstraints", "LeanRV64D")

# (pattern, what it is). Each pattern is searched in comment-free source.
BANNED = [
    (r"\bsorry\b", "`sorry`"),
    (r"\badmit\b", "`admit`"),
    (r"\bnative_decide\b", "`native_decide`"),
    (r"\bbv_decide\b", "`bv_decide`"),
    (r"\bdecide\s*\+\s*kernel\b", "`decide +kernel`"),
    (r"\bkernel\s*:=\s*true\b", "`decide` with `kernel := true`"),
    (r"\bofReduceBool\b|\btrustCompiler\b", "a native-evaluation axiom"),
    (r"\bdebug\.skipKernelTC\b", "`debug.skipKernelTC`"),
    (r"\bmaxHeartbeats\b", "a `maxHeartbeats` option"),
    (r"\bsynthInstance\.\w+", "a `synthInstance` option"),
    (r"\brespectTransparency\s+false\b", "`respectTransparency false`"),
]
AXIOM = re.compile(r"\baxiom\s+([^\s:({\[]+)")
MAX_REC_DEPTH = re.compile(r"\bset_option\s+maxRecDepth\s+(\d+)\s+in\b")
ANY_MAX_REC_DEPTH = re.compile(r"\bmaxRecDepth\b")


def lean_files():
    for library in LIBRARIES:
        root_file = ROOT / f"{library}.lean"
        if root_file.exists():
            yield root_file
        yield from sorted((ROOT / library).rglob("*.lean"))


def line_of(text, index):
    return text.count("\n", 0, index) + 1


def main():
    allow = tomllib.loads(ALLOWLIST.read_text())
    allowed_axioms = {(entry["file"], name) for entry in allow.get("axioms", [])
                      for name in entry["names"]}
    allowed_options = [(e["file"], e["option"], e["declaration"]) for e in allow.get("options", [])]
    used_axioms, used_options = set(), []
    errors = []
    files = 0

    for path in lean_files():
        files += 1
        where = str(path.relative_to(ROOT))
        raw = path.read_text()
        text = strip_comments(raw)
        lines = text.split("\n")
        for pattern, what in BANNED:
            for match in re.finditer(pattern, text):
                errors.append(f"{where}:{line_of(text, match.start())}: {what}")
        for match in AXIOM.finditer(text):
            name = match.group(1)
            if (where, name) in allowed_axioms:
                used_axioms.add((where, name))
            else:
                errors.append(f"{where}:{line_of(text, match.start())}: `axiom {name}` is not in "
                              f"{ALLOWLIST.relative_to(ROOT)}")
        allowed_lines = set()
        for match in MAX_REC_DEPTH.finditer(text):
            number = line_of(text, match.start())
            following = next((l for l in lines[number:] if l.strip()), "")
            declaration = re.match(r"(?:noncomputable\s+)?def\s+(\S+)", following)
            key = (where, f"maxRecDepth {match.group(1)}", declaration.group(1) if declaration else "")
            if key in allowed_options and key not in used_options:
                used_options.append(key)
                allowed_lines.add(number)
        for match in ANY_MAX_REC_DEPTH.finditer(text):
            number = line_of(text, match.start())
            if number not in allowed_lines:
                errors.append(f"{where}:{number}: a `maxRecDepth` option that "
                              f"{ALLOWLIST.relative_to(ROOT)} does not list")

    for where, name in sorted(allowed_axioms - used_axioms):
        errors.append(f"allowlist: {where} no longer declares `axiom {name}`; remove it")
    for key in allowed_options:
        if key not in used_options:
            errors.append(f"allowlist: {key[0]} has no `set_option {key[1]} in` before "
                          f"`def {key[2]}`; remove or update the entry")

    for message in errors:
        print(f"check-lean-policy: {message}", file=sys.stderr)
    if errors:
        print(f"check-lean-policy: {len(errors)} problem(s)", file=sys.stderr)
        return 1
    print(f"check-lean-policy: {files} files pass; allowed: {len(used_axioms)} axioms in "
          f"LeanRV64D/RiscvExtras.lean, {len(used_options)} generated maxRecDepth options")
    return 0


if __name__ == "__main__":
    sys.exit(main())
