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
bv_decide, set_option maxHeartbeats, maxRecDepth, synthInstance.* options,
axiom declarations and new syntax that takes `interpolatedStr`.

Comments (nested /- -/ blocks, docstrings and -- lines) and the text of string,
raw-string and char literals are blanked before matching, so a token that
appears only in prose does not count. Quoted identifiers (`«...»`) are one
opaque name. A string literal is read as interpolated, with its `{...}` parts
kept as code, when the syntax just before it takes an interpolated string
(`s!"..."`, `throwError "..."`, `trace[c] "..."`; see _INTERP_DIRECT); every
other literal is plain text. New syntax declared with `interpolatedStr` counts
as an occurrence. An `axiom` keyword counts wherever it appears in code.
The regression tests are in scripts/tests/test_check_hygiene.py.
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
    # `axiom` is a keyword, so any occurrence in code starts a declaration,
    # wherever it sits on the line (for example after `set_option ... in`).
    "axiom": re.compile(r"(?<![\w.'])axiom(?![\w'])"),
    # New syntax that takes an interpolated string (see _INTERP_DIRECT).
    "interpolatedStr": re.compile(r"(?<![\w.'])interpolatedStr(?![\w'])"),
}

# root directory -> (root module, baseline section or None for zero tolerance)
ROOTS: dict[str, tuple[str, str | None]] = {
    "JoltBytecode": ("JoltBytecode.lean", None),
    "JoltConstraints": ("JoltConstraints.lean", "known"),
    "JoltTests": ("JoltTests.lean", None),
    "LeanRV64D": ("LeanRV64D.lean", "generated"),
}

IDENT_CHAR = re.compile(r"[\w'!?.²-³¹⁰-ₜα-ωΑ-Ωᴀ-ᶿ℀-⅏]")
CHAR_LIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'")
RAW_STR_START = re.compile(r'r(#*)"')


# Syntax that reads the next string literal as an interpolated string
# (`interpolatedStr(term)`), from Lean v4.35.0 core and the dependencies
# (Mathlib, Batteries and the others declare none of their own):
#   - s!, m!, f!, v!, println!, reportIssue!, reportDbgIssue!,
#     reportEMatchIssue!, throwError, dbg_trace and Aesop's throwPRError
#     directly before the literal;
#   - trace[c], trace_goal[c], Macro.trace[c], and Aesop's aesop_trace[c] and
#     aesop_trace![c] directly before it;
#   - throwErrorAt, throwNamedError(At), logNamedError(At), logNamedWarning(At)
#     earlier on the same line, which take one or two arguments first.
# Every other literal is a plain string. Reading a literal the wrong way can
# hide code in either direction (the `{...}` of an interpolated string blanked
# as text, or a `"` inside a plain string's `{` read as the start of another
# string), so the list is exact rather than generous. A scanned file that
# declares new syntax with `interpolatedStr` counts as an occurrence of that
# token, so a new interpolating macro in this project is noticed and added here.
_INTERP_DIRECT = re.compile(
    r"(?<![\w'.!])(?:(?:s|m|f|v|println|reportIssue|reportDbgIssue|reportEMatchIssue)!"
    r"|throwError|dbg_trace|throwPRError"
    r"|(?:trace|trace_goal|Macro\.trace|aesop_trace|aesop_trace!)\[[^\]\n]*\])\s*$"
)
_INTERP_ARGS = re.compile(
    r"(?<![\w'.])(?:throwErrorAt|throwNamedError|throwNamedErrorAt|logNamedError|logNamedErrorAt"
    r"|logNamedWarning|logNamedWarningAt)(?![\w'])[^\"\n]*$"
)


class _Lexer:
    """Blank comments and literal text of one Lean source, keeping layout.

    A string literal is interpolated when the syntax before it says so
    (_INTERP_DIRECT, _INTERP_ARGS); then the code between an unescaped `{` and
    its matching `}` is kept and lexed like any other code, nested string
    literals included. Quoted identifiers (`«...»`, which may span lines) are
    one opaque name.
    """

    def __init__(self, src: str) -> None:
        self.src, self.n = src, len(src)
        self.out: list[str] = []

    def blank(self, i: int, j: int) -> None:
        self.out.append("".join("\n" if c == "\n" else " " for c in self.src[i:j]))

    def keep(self, i: int, j: int) -> None:
        self.out.append(self.src[i:j])

    def run(self) -> str:
        self.code(0, in_braces=False)
        return "".join(self.out)

    def interpolated_here(self) -> bool:
        """Whether a string literal starting now is interpolated."""
        before = "".join(self.out[-400:])[-300:]
        return bool(_INTERP_DIRECT.search(before) or _INTERP_ARGS.search(before))

    def code(self, i: int, in_braces: bool) -> int:
        """Lex code from i; inside an interpolation, stop after its closing `}`."""
        src, n = self.src, self.n
        depth = 0
        while i < n:
            c = src[i]
            nxt = src[i + 1] if i + 1 < n else ""
            if c == "/" and nxt == "-":
                i = self.block_comment(i)
            elif c == "-" and nxt == "-":
                j = src.find("\n", i)
                j = n if j == -1 else j
                self.blank(i, j)
                i = j
            elif c == "«":
                j = src.find("»", i + 1)
                if j == -1:
                    self.keep(i, i + 1)
                    i += 1
                else:
                    # A quoted identifier: one opaque name, never a comment or token.
                    self.out.append("".join("\n" if ch == "\n" else "x" for ch in src[i:j + 1]))
                    i = j + 1
            elif c == '"':
                i = self.string(i, self.interpolated_here())
            elif c == "r" and (i == 0 or not IDENT_CHAR.match(src[i - 1])) and RAW_STR_START.match(src, i):
                hashes = RAW_STR_START.match(src, i).group(1)
                close = '"' + hashes
                j = src.find(close, i + 2 + len(hashes))
                j = n if j == -1 else j + len(close)
                self.blank(i, j)
                i = j
            elif c == "'" and (i == 0 or not IDENT_CHAR.match(src[i - 1])) and CHAR_LIT.match(src, i):
                m = CHAR_LIT.match(src, i)
                self.blank(i, m.end())
                i = m.end()
            elif in_braces and c == "{":
                depth += 1
                self.keep(i, i + 1)
                i += 1
            elif in_braces and c == "}":
                if depth == 0:
                    self.blank(i, i + 1)
                    return i + 1
                depth -= 1
                self.keep(i, i + 1)
                i += 1
            else:
                self.keep(i, i + 1)
                i += 1
        return i

    def block_comment(self, i: int) -> int:
        src, n = self.src, self.n
        depth, j = 1, i + 2
        while j < n and depth:
            if src.startswith("/-", j):
                depth, j = depth + 1, j + 2
            elif src.startswith("-/", j):
                depth, j = depth - 1, j + 2
            else:
                j += 1
        self.blank(i, j)
        return j

    def string(self, i: int, interpolate: bool) -> int:
        src, n = self.src, self.n
        start, j = i, i + 1
        while j < n:
            c = src[j]
            if c == "\\":
                j += 2
            elif c == '"':
                j += 1
                break
            elif c == "{" and interpolate:
                self.blank(start, j + 1)
                j = self.code(j + 1, in_braces=True)
                start = j
            else:
                j += 1
        j = min(j, n)
        self.blank(start, j)
        return j


def strip_comments_and_strings(src: str) -> str:
    """Blank Lean comments, string and char literal text; keep layout and code.

    Newlines are kept, so line numbers of the remaining code do not change.
    Quoted identifiers (`«...»`) become one opaque name, and the `{...}` parts
    of interpolated string literals stay code (see _Lexer).
    """
    return _Lexer(src).run()


def scan_file(path: Path) -> list[tuple[int, str, str]]:
    """Return (line, token, source line) for every occurrence in a file."""
    return scan_text(path.read_text(encoding="utf-8", errors="replace"))


def scan_text(text: str) -> list[tuple[int, str, str]]:
    """Return (line, token, source line) for every occurrence in a Lean source."""
    code = strip_comments_and_strings(text)
    assert len(code) == len(text)
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
