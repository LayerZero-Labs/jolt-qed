#!/usr/bin/env python3
"""Hygiene scan of jolt-qed's Lean sources, adapted from openvm-fv.

The scan looks for proof holes, tactics that trust the compiler or the kernel's
evaluator, raised limits and new axioms in four roots, each with its own policy:

  JoltBytecode/     zero tolerance for every token below.
  JoltConstraints/  zero tolerance, except the debt recorded under [[known]] in
                    scripts/hygiene-baseline.toml.
  JoltTests/        zero tolerance; tests may use #eval and IO, which the scan
                    does not look for.
  LeanRV64D/        generated Sail model; every occurrence must match the
                    [[generated]] baseline in scripts/hygiene-baseline.toml.

Tokens: sorry, admit, native_decide, decide +kernel (also kernel := true),
bv_decide, set_option maxHeartbeats, maxRecDepth, synthInstance.* options and
axiom declarations.

Comments (nested /- -/ blocks, docstrings and -- lines) and string literals are
blanked before matching, so a token that appears only in prose does not count.
Each root's root module (for example JoltBytecode.lean) is scanned with it.

A baseline entry records a file, a token and the exact number of occurrences.
The scan fails when a file has an occurrence the baseline does not allow, and
when a baseline entry no longer matches (the debt shrank, so the entry must be
lowered or deleted). The frozen statements in ci/comparator/Challenge.lean are
outside every root, as in openvm-fv.

Usage: scripts/check_hygiene.py [--baseline FILE] [--print-baseline]
Exit status: 0 clean, 1 violations, 2 usage or input error.
"""

from __future__ import annotations

import argparse
import re
import sys
import tomllib
from collections import Counter
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

TOKENS: dict[str, re.Pattern[str]] = {
    "sorry": re.compile(r"(?<![\w.'])sorry(?![\w'])"),
    "admit": re.compile(r"(?<![\w.'])admit(?![\w'])"),
    "native_decide": re.compile(r"(?<![\w.'])native_decide(?![\w'])"),
    "decide +kernel": re.compile(r"(?<![\w.'])decide\s*\+\s*kernel(?![\w'])|(?<![\w.'])kernel\s*:=\s*true(?![\w'])"),
    "bv_decide": re.compile(r"(?<![\w.'])bv_decide(?![\w'])"),
    "maxHeartbeats": re.compile(r"(?<![\w.'])set_option\s+maxHeartbeats(?![\w'])"),
    "maxRecDepth": re.compile(r"(?<![\w.'])maxRecDepth(?![\w'])"),
    "synthInstance": re.compile(r"(?<![\w.'])synthInstance\.\w+"),
    "axiom": re.compile(
        r"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?"
        r"(?:(?:private|protected|noncomputable|unsafe|partial)[ \t]+)*axiom(?![\w'])"
    ),
}

# root directory -> (root module, baseline section or None for zero tolerance)
ROOTS: dict[str, tuple[str, str | None]] = {
    "JoltBytecode": ("JoltBytecode.lean", None),
    "JoltConstraints": ("JoltConstraints.lean", "known"),
    "JoltTests": ("JoltTests.lean", None),
    "LeanRV64D": ("LeanRV64D.lean", "generated"),
}

IDENT_CHAR = re.compile(r"[\w'!?.²-³¹⁰-ₜα-ωΑ-Ωᴀ-ᶿ℀-⅏]")


def strip_comments_and_strings(src: str) -> str:
    """Blank Lean comments, string literals and char literals, keeping layout.

    Newlines are kept, so line numbers of the remaining code do not change.
    """
    out: list[str] = []
    i, n = 0, len(src)
    depth = 0

    def blank(s: str) -> str:
        return "".join("\n" if c == "\n" else " " for c in s)

    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth > 0:
            if c == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
            elif c == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if c == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
            continue
        if c == "-" and nxt == "-":
            j = src.find("\n", i)
            j = n if j == -1 else j
            out.append(" " * (j - i))
            i = j
            continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(blank(src[i:j]))
            i = j
            continue
        if c == "'" and (i == 0 or not IDENT_CHAR.match(src[i - 1])):
            m = re.match(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'", src[i:])
            if m:
                out.append(blank(m.group(0)))
                i += len(m.group(0))
                continue
        out.append(c)
        i += 1
    return "".join(out)


def scan_file(path: Path) -> list[tuple[int, str, str]]:
    """Return (line, token, source line) for every occurrence in a file."""
    text = path.read_text(encoding="utf-8", errors="replace")
    code = strip_comments_and_strings(text)
    raw_lines = text.splitlines()
    starts = [0]
    for idx, ch in enumerate(code):
        if ch == "\n":
            starts.append(idx + 1)
    hits = []
    for token, pattern in TOKENS.items():
        for m in pattern.finditer(code):
            pos = m.start() + (len(m.group(0)) - len(m.group(0).lstrip()))
            lineno = _line_of(starts, pos)
            raw = raw_lines[lineno - 1].strip() if lineno - 1 < len(raw_lines) else ""
            hits.append((lineno, token, raw))
    hits.sort()
    return hits


def _line_of(starts: list[int], pos: int) -> int:
    lo, hi = 0, len(starts) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if starts[mid] <= pos:
            lo = mid
        else:
            hi = mid - 1
    return lo + 1


def files_of(root: str, module: str) -> list[Path]:
    base = REPO / root
    files = sorted(p for p in base.rglob("*.lean") if ".lake" not in p.parts)
    if (REPO / module).is_file():
        files.insert(0, REPO / module)
    return files


def load_baseline(path: Path) -> dict[str, Counter]:
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as e:
        raise SystemExit(f"error: cannot read baseline {path}: {e}")
    out: dict[str, Counter] = {"known": Counter(), "generated": Counter()}
    for section in out:
        for entry in data.get(section, []):
            key = (entry["file"], entry["token"])
            if entry["token"] not in TOKENS:
                raise SystemExit(f"error: unknown token {entry['token']!r} in baseline")
            if key in out[section]:
                raise SystemExit(f"error: duplicate baseline entry {key}")
            out[section][key] = int(entry["count"])
    return out


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--baseline", default=str(REPO / "scripts" / "hygiene-baseline.toml"))
    ap.add_argument("--print-baseline", action="store_true",
                    help="print the baseline that matches the tree today and exit")
    args = ap.parse_args(argv)

    found: dict[str, Counter] = {}
    lines: dict[tuple[str, str], list[tuple[int, str]]] = {}
    nfiles = 0
    for root, (module, _) in ROOTS.items():
        found[root] = Counter()
        for path in files_of(root, module):
            nfiles += 1
            rel = path.relative_to(REPO).as_posix()
            for lineno, token, raw in scan_file(path):
                found[root][(rel, token)] += 1
                lines.setdefault((rel, token), []).append((lineno, raw))

    if args.print_baseline:
        for root, (_, section) in ROOTS.items():
            if section is None:
                continue
            for (rel, token), count in sorted(found[root].items()):
                print(f'[[{section}]]\nfile = "{rel}"\ntoken = "{token}"\ncount = {count}\n')
        return 0

    baseline = load_baseline(Path(args.baseline))
    failures = 0
    print(f"hygiene scan: {nfiles} Lean files under {', '.join(r + '/' for r in ROOTS)}")
    for root, (_, section) in ROOTS.items():
        allowed = baseline[section] if section else Counter()
        if section:
            for (rel, token) in allowed:
                if not rel.startswith(root + "/") and rel != ROOTS[root][0]:
                    print(f"FAIL baseline [[{section}]] entry {rel} is outside {root}/")
                    failures += 1
        keys = sorted(set(found[root]) | set(allowed))
        recorded = 0
        for key in keys:
            have, want = found[root].get(key, 0), allowed.get(key, 0)
            rel, token = key
            if have == want:
                recorded += have
                continue
            failures += 1
            if have > want:
                print(f"FAIL {rel}: {token} occurs {have} time(s), baseline allows {want}")
                for lineno, raw in lines.get(key, []):
                    print(f"     {rel}:{lineno}: {raw}")
            else:
                print(f"FAIL {rel}: baseline records {want} {token}, the file has {have}; "
                      f"lower the entry in {Path(args.baseline).name}")
        policy = "zero tolerance" if section is None else f"baseline [[{section}]]"
        print(f"  {root}/: {sum(found[root].values())} occurrence(s), "
              f"{recorded} recorded in the baseline ({policy})")
    if failures:
        print(f"FAIL: {failures} hygiene check(s) failed")
        return 1
    print("OK: every occurrence matches the hygiene policy")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
