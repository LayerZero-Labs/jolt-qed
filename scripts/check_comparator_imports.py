#!/usr/bin/env python3
"""Check the import headers of the comparator gate's Challenge and Solution.

Usage: scripts/check_comparator_imports.py CHALLENGE SOLUTION MODULE...

The check passes when SOLUTION has exactly the header of CHALLENGE and that
header imports exactly the listed MODULEs, each once, with no modifiers. Lean
reads comments as whitespace, so the check reads the header after removing
comments (with the lexer of scripts/check_hygiene.py): a comment before an
import cannot hide it, and an `import` line inside a comment does not count.
A header token that the check does not understand fails it.

Exit status: 0 the headers agree, 1 they do not, 2 bad usage or unreadable file.
"""

from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path

_spec = importlib.util.spec_from_file_location(
    "check_hygiene", Path(__file__).resolve().parent / "check_hygiene.py")
hygiene = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(hygiene)

# Words that may start or modify a header command in Lean 4.35.
HEADER_WORDS = ("module", "prelude", "public", "private", "meta", "import", "all")
NAME_RE = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")


def header(src: str) -> list[str]:
    """The header of a Lean file: one string per command, such as "import A.B".

    Raises ValueError for a header the check does not understand.
    """
    code = hygiene.strip_comments_and_strings(src)
    if len(code) != len(src):
        raise ValueError("the comment lexer changed the file length")
    matches = list(re.finditer(r"\S+", code))
    tokens = [m.group(0) for m in matches]
    out: list[str] = []
    i = 0
    while i < len(tokens) and tokens[i] in HEADER_WORDS:
        cmd: list[str] = []
        while i < len(tokens) and tokens[i] in ("public", "private", "meta"):
            cmd.append(tokens[i])
            i += 1
        if i < len(tokens) and tokens[i] in ("module", "prelude") and not cmd:
            out.append(tokens[i])
            i += 1
            continue
        if i >= len(tokens) or tokens[i] != "import":
            raise ValueError(f"unexpected header token after {' '.join(cmd)!r}")
        cmd.append("import")
        i += 1
        if i < len(tokens) and tokens[i] == "all":
            cmd.append("all")
            i += 1
        # The name must read the same in the source; this rejects text that
        # the lexer replaced, such as a quoted identifier.
        if (i >= len(tokens) or not NAME_RE.fullmatch(tokens[i])
                or src[matches[i].start():matches[i].end()] != tokens[i]):
            raise ValueError(f"cannot read the module name after {' '.join(cmd)!r}")
        cmd.append(tokens[i])
        i += 1
        out.append(" ".join(cmd))
    # The body starts with a command keyword or an attribute, never with text
    # that begins like a header word. `import«Lean»` is one token here (the
    # lexer hides the quoted name) but an import for Lean, so it fails.
    if i < len(tokens) and re.match(r"(?:" + "|".join(HEADER_WORDS) + r")(?![\w'])|import",
                                    tokens[i]):
        raise ValueError(f"cannot read the header token {tokens[i]!r}")
    return out


def check(challenge: str, solution: str, modules: list[str]) -> list[str]:
    """Problems with the two headers; empty when they agree."""
    problems = []
    try:
        ch, so = header(challenge), header(solution)
    except ValueError as e:
        return [f"unreadable header: {e}"]
    want = [f"import {m}" for m in modules]
    if sorted(ch) != sorted(want) or len(set(ch)) != len(ch):
        problems.append(f"Challenge.lean's header is {ch}; the trusted imports are {want}")
    if so != ch:
        problems.append(f"Solution.lean's header is {so}; it must equal Challenge.lean's {ch}")
    return problems


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print(__doc__.split("\n\n")[1], file=sys.stderr)
        return 2
    try:
        challenge, solution = (Path(p).read_text(encoding="utf-8") for p in argv[:2])
    except OSError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    problems = check(challenge, solution, argv[2:])
    for p in problems:
        print(f"ERROR: {p}", file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
