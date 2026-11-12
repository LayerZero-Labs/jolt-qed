#!/usr/bin/env python3
"""Check provenance.toml, the manifest of which Jolt code each Lean file models.

The manifest (provenance.toml at the repository root) has one [jolt] table with
the Jolt pin, one [[file]] entry per Lean file under JoltBytecode/ and
JoltConstraints/, a list of [[other_revision]] commits of other repositories
that the docs may cite, and a [[known]] baseline of existing violations.

Checks without a Jolt clone:

  1. [jolt] has repository "a16z/jolt" and exactly one pin, a 40-hex commit.
  2. Every Lean file under JoltBytecode/ and JoltConstraints/ has exactly one
     [[file]] entry, and every entry names an existing file. An entry with a
     `checked` revision (40 hex) has at least one `models` path.
  3. The scanned files (*.lean and *.md under JoltBytecode/, JoltConstraints/
     and docs/, plus README.md and provenance.toml) contain no local paths
     (/Users/, /home/, ~/, /private/tmp), no citation of a Jolt fork
     (github.com/<owner>/jolt with an owner other than a16z), and no Jolt
     revision other than the pin or, in a Lean file, that file's `checked`
     revision. A revision is a token of 7 to 40 hex digits with at least one
     digit and one letter; [[other_revision]] lists the tokens that are commits
     of other repositories. provenance.toml is not checked for revisions,
     because it is where they are recorded.
     The violations found must equal the [[known]] baseline exactly: the check
     fails on a new violation and on a baseline count that is too high, so the
     baseline shrinks as files are fixed.

With --jolt-dir DIR (a clone of a16z/jolt that has the pin and every
`checked` revision; trees are enough, so a shallow blobless fetch of each
revision printed by --list-revisions works, as CI does):

  4. The pin and every `checked` revision are commits in DIR, and every
     `models` path of an entry exists at its `checked` revision.
  5. Report, without failing, every `models` path that is missing at the pin
     or at a --compare revision, including the paths of entries that name no
     `checked` revision, and, in a full clone, every baseline revision that is
     not a Jolt commit.

Usage:
  scripts/check-provenance.py [--manifest FILE] [--jolt-dir DIR] [--compare REV ...]
  scripts/check-provenance.py --print-baseline   # baseline that matches today
  scripts/check-provenance.py --list-revisions   # pin and checked revisions
Exit status: 0 pass, 1 a check failed, 2 usage or input error.
"""

from __future__ import annotations

import argparse
import itertools
import json
import re
import subprocess
import sys
import tomllib
from collections import Counter
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
MANIFEST_ROOTS = ("JoltBytecode", "JoltConstraints")
SCAN_ROOTS = ("JoltBytecode", "JoltConstraints", "docs")
SCAN_FILES = ("README.md", "provenance.toml")
FULL_REV = re.compile(r"[0-9a-f]{40}")
KNOWN_KINDS = ("local-path", "fork", "revision", "unchecked-model")

# Local paths and fork citations. The baseline records the whole citation (the
# path or URL up to the next space or delimiter), so replacing one baselined
# citation with another fails: the old entry goes stale and the new one is not
# recorded.
CITE_END = r"[^\s`'\"()<>\[\]{},;]*"
LOCAL_RE = re.compile(r"(?:/Users/|/home/|~/|/private/tmp)" + CITE_END)
FORK_RE = re.compile(r"github\.com/([A-Za-z0-9_.-]+)/jolt(?![A-Za-z0-9_-])" + CITE_END)
HEX_RE = re.compile(r"(?<![0-9A-Za-z_])[0-9a-f]{7,40}(?![0-9A-Za-z_])")
# A repository-qualified revision: a GitHub URL or owner/repo@rev.
QUALIFIED_RE = re.compile(
    r"(?:github\.com/([A-Za-z0-9_.-]+)/([A-Za-z0-9_.-]+)/(?:blob|tree|commit|commits|compare)/"
    r"|(?<![\w./-])([A-Za-z0-9_.-]+)/([A-Za-z0-9_.-]+)@)"
    r"([0-9a-fA-F]{7,40})(?![0-9A-Za-z_])"
)
# Words before a token that make an all-digit or all-letter hex token a
# revision citation ("commit 7538215", "at revision deadbeef", "jolt@1234567").
REV_CONTEXT_RE = re.compile(
    r"(?:(?i:\b(?:commit|commits|revision|rev|pin|pinned|sha|hash|checked)\b)[\s:=`'\"(]*|@)$"
)


def fail_input(msg: str) -> "NoReturn":  # noqa: F821
    print(f"error: {msg}", file=sys.stderr)
    raise SystemExit(2)


def is_revision_token(tok: str) -> bool:
    """A 7-40 hex token with a digit and a letter (not 0b binary) is a revision.

    All-digit and all-letter tokens are ordinary numbers and words far more
    often than revisions, so they count only in a citation context
    (REV_CONTEXT_RE or a repository-qualified citation).
    """
    return (re.search(r"[0-9]", tok) is not None
            and re.search(r"[a-f]", tok) is not None
            and re.fullmatch(r"0b[01]+", tok) is None)


def same_revision(token: str, rev: str) -> bool:
    return rev.startswith(token) or token.startswith(rev)


def is_jolt_repo(owner: str, repo: str) -> bool:
    return repo.lower() == "jolt"


def manifest_lean_files() -> list[str]:
    out = []
    for root in MANIFEST_ROOTS:
        out += [p.relative_to(REPO).as_posix() for p in (REPO / root).rglob("*.lean")
                if ".lake" not in p.parts]
    return sorted(out)


def scanned_files() -> list[str]:
    out = []
    for root in SCAN_ROOTS:
        for pattern in ("*.lean", "*.md"):
            out += [p.relative_to(REPO).as_posix() for p in (REPO / root).rglob(pattern)
                    if ".lake" not in p.parts]
    out += [f for f in SCAN_FILES if (REPO / f).is_file()]
    return sorted(set(out))


def manifest_scan_text(text: str, manifest: dict) -> str:
    """provenance.toml without the `text` lines of its [[known]] entries.

    Those lines quote the baselined citations; scanning them would make the
    baseline cite itself.
    """
    quoted = {"text = " + json.dumps(k.get("text", "")) for k in manifest.get("known", [])}
    return "\n".join("" if line.strip() in quoted else line for line in text.split("\n"))


def scan_text(rel: str, text: str, pin: str, checked: str | None,
              others: list[dict]) -> Counter:
    """Count violations per (file, kind, text) in one file's text."""
    found: Counter = Counter()
    for m in LOCAL_RE.finditer(text):
        found[(rel, "local-path", m.group(0))] += 1
    for m in FORK_RE.finditer(text):
        if m.group(1).lower() != "a16z":
            found[(rel, "fork", m.group(0))] += 1
    if rel == "provenance.toml":
        return found
    jolt_ok = [pin] + ([checked] if checked else [])
    qualified: set[int] = set()
    for m in QUALIFIED_RE.finditer(text):
        owner = m.group(1) or m.group(3)
        repo = m.group(2) or m.group(4)
        tok = m.group(5)
        qualified.add(m.start(5))
        if is_jolt_repo(owner, repo):
            ok = any(same_revision(tok.lower(), r) for r in jolt_ok)
        else:
            ok = any(same_revision(tok.lower(), o["revision"])
                     and o.get("repository", "").lower() == f"{owner}/{repo}".lower()
                     for o in others)
        if not ok:
            found[(rel, "revision", tok)] += 1
    allowed = jolt_ok + [o["revision"] for o in others]
    for m in HEX_RE.finditer(text):
        if m.start() in qualified:
            continue
        tok = m.group(0)
        if not is_revision_token(tok) and not REV_CONTEXT_RE.search(text[max(0, m.start() - 24):m.start()]):
            continue
        if not any(same_revision(tok, r) for r in allowed):
            found[(rel, "revision", tok)] += 1
    return found


def scan(manifest: dict, checked_of: dict[str, str]) -> Counter:
    """Count violations per (file, kind, text) over every scanned file."""
    pin = manifest["jolt"]["pin"]
    others = manifest.get("other_revision", [])
    found: Counter = Counter()
    for rel in scanned_files():
        text = (REPO / rel).read_text(encoding="utf-8", errors="replace")
        if rel == "provenance.toml":
            text = manifest_scan_text(text, manifest)
        found += scan_text(rel, text, pin, checked_of.get(rel), others)
    return found


# Jolt paths a Lean file cites. A path segment may hold brace lists
# (`virt/{load,store}_{b,h,w}.rs`), and a bare file name that follows a cited
# `.rs` path closely (`div.rs, divu.rs, rem.rs`) is read in that path's
# directory. A GitHub URL or local checkout prefix up to `/jolt/` is dropped.
_SEG = r"(?:[\w.-]|\{[\w.,\s-]+\})+"
_PATH_RE = re.compile(r"(?<![\w./{-])/?" + _SEG + r"(?:/" + _SEG + r")+")
_BARE_RE = re.compile(r"(?<![\w./{-])([\w-]+\.rs)(?![\w/])")
_URL_PREFIX = re.compile(r"(?:https?://)?github\.com/[\w.-]+/[\w.-]+/(?:blob|tree)/[\w.-]+/")
BARE_WINDOW = 300


def _expand(tok: str) -> list[str]:
    parts = re.split(r"(\{[^}]*\})", tok)
    opts = [[x.strip() for x in part[1:-1].split(",")] if part.startswith("{") else [part]
            for part in parts]
    return ["".join(c) for c in itertools.product(*opts)]


def _normalize(path: str) -> str:
    path = path.rstrip("/.")
    i = path.find("jolt/")
    if i != -1 and (i == 0 or path[i - 1] == "/"):
        path = path[i + len("jolt/"):]
    return path


def cited_paths(text: str) -> set[str]:
    """Candidate Jolt paths cited in a file; callers keep those that exist."""
    text = _URL_PREFIX.sub(" ", text)
    events = sorted([(m.start(), m.end(), True, m.group(0)) for m in _PATH_RE.finditer(text)]
                    + [(m.start(), m.end(), False, m.group(1)) for m in _BARE_RE.finditer(text)])
    out: set[str] = set()
    last_dir, last_end = None, -BARE_WINDOW - 1
    for start, end, is_path, tok in events:
        if is_path:
            for path in map(_normalize, _expand(tok)):
                out.add(path)
                if path.endswith(".rs") and "/" in path:
                    last_dir, last_end = path.rsplit("/", 1)[0], end
        elif last_dir is not None and start - last_end <= BARE_WINDOW:
            out.add(f"{last_dir}/{tok}")
            last_end = end
    return out


def git(jolt_dir: str, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", jolt_dir, *args], capture_output=True, text=True)


def resolve(jolt_dir: str, rev: str) -> str | None:
    r = git(jolt_dir, "rev-parse", "--verify", "--quiet", f"{rev}^{{commit}}")
    return r.stdout.strip() if r.returncode == 0 else None


_trees: dict[str, set[str]] = {}


def paths_at(jolt_dir: str, rev: str) -> set[str]:
    """Every file and directory path at a revision, read from trees only."""
    if rev not in _trees:
        r = git(jolt_dir, "ls-tree", "-r", "-t", "--full-tree", "--name-only", "-z", rev)
        if r.returncode != 0:
            fail_input(f"git ls-tree {rev} failed in {jolt_dir}: {r.stderr.strip()}")
        _trees[rev] = set(p for p in r.stdout.split("\0") if p)
    return _trees[rev]


_blobs: dict[str, set[str]] = {}


def files_at(jolt_dir: str, rev: str) -> set[str]:
    """Every file (blob) path at a revision, read from trees only."""
    if rev not in _blobs:
        r = git(jolt_dir, "ls-tree", "-r", "--full-tree", "--name-only", "-z", rev)
        if r.returncode != 0:
            fail_input(f"git ls-tree {rev} failed in {jolt_dir}: {r.stderr.strip()}")
        _blobs[rev] = set(p for p in r.stdout.split("\0") if p)
    return _blobs[rev]


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--manifest", default=str(REPO / "provenance.toml"))
    ap.add_argument("--jolt-dir", help="clone of a16z/jolt with the pin and checked revisions")
    ap.add_argument("--compare", action="append", default=[], metavar="REV",
                    help="also report models paths missing at REV (needs --jolt-dir)")
    ap.add_argument("--print-baseline", action="store_true",
                    help="print the [[known]] baseline that matches the tree today and exit")
    ap.add_argument("--list-revisions", action="store_true",
                    help="print the pin and every checked revision, one per line, and exit")
    args = ap.parse_args(argv)

    try:
        manifest = tomllib.loads(Path(args.manifest).read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as e:
        fail_input(f"cannot read {args.manifest}: {e}")

    failures: list[str] = []
    notes: list[str] = []

    # 1. The pin.
    jolt = manifest.get("jolt")
    if not isinstance(jolt, dict):
        fail_input("provenance.toml has no [jolt] table")
    pin = jolt.get("pin")
    if jolt.get("repository") != "a16z/jolt":
        failures.append('[jolt] repository must be "a16z/jolt"')
    if not isinstance(pin, str) or not FULL_REV.fullmatch(pin):
        fail_input("[jolt] must have exactly one pin, a 40-hex commit string")
    extra = sorted(k for k in jolt if k not in ("repository", "pin", "note"))
    if extra:
        failures.append(f"[jolt] has unexpected keys {extra}; it records one pin")

    # 2. One entry per Lean file.
    entries = manifest.get("file", [])
    by_file: dict[str, dict] = {}
    lean_files = set(manifest_lean_files())
    for e in entries:
        lean = e.get("lean")
        if not isinstance(lean, str):
            failures.append(f"[[file]] entry without a lean path: {e}")
            continue
        if lean in by_file:
            failures.append(f"{lean}: more than one [[file]] entry")
        by_file[lean] = e
        unknown = sorted(k for k in e if k not in ("lean", "models", "checked", "note"))
        if unknown:
            failures.append(f"{lean}: [[file]] entry has unexpected keys {unknown}")
        if not (REPO / lean).is_file():
            failures.append(f"{lean}: [[file]] entry names a file that does not exist")
        elif lean not in lean_files:
            failures.append(f"{lean}: [[file]] entries are for Lean files under "
                            f"{' and '.join(r + '/' for r in MANIFEST_ROOTS)} only")
        models = e.get("models")
        if not isinstance(models, list) or not all(isinstance(m, str) for m in models):
            failures.append(f"{lean}: models must be a list of Jolt paths")
            continue
        checked = e.get("checked")
        if checked is not None:
            if not isinstance(checked, str) or not FULL_REV.fullmatch(checked):
                failures.append(f"{lean}: checked must be a 40-hex commit")
            elif not models:
                failures.append(f"{lean}: has a checked revision but no models")
    for lean in manifest_lean_files():
        if lean not in by_file:
            failures.append(f"{lean}: no [[file]] entry in provenance.toml")
    checked_of = {k: e["checked"] for k, e in by_file.items() if isinstance(e.get("checked"), str)}
    unpinned = sorted(k for k, e in by_file.items() if e.get("models") and "checked" not in e)

    if args.list_revisions:
        for rev in sorted({pin, *checked_of.values()}):
            print(rev)
        return 0

    # 3. Local paths, fork citations, other revisions, and models paths that
    # no checked revision vouches for.
    found = scan(manifest, checked_of)
    for lean in unpinned:
        for path in by_file[lean]["models"]:
            found[(lean, "unchecked-model", path)] += 1
    if args.print_baseline:
        for (rel, kind, text), count in sorted(found.items()):
            print(f'[[known]]\nfile = {json.dumps(rel)}\nkind = {json.dumps(kind)}\n'
                  f'text = {json.dumps(text)}\ncount = {count}\n')
        return 0
    known: Counter = Counter()
    for k in manifest.get("known", []):
        if sorted(k) != ["count", "file", "kind", "text"]:
            failures.append(f"[[known]] {k}: needs exactly file, kind, text and count")
            continue
        key = (k["file"], k["kind"], k["text"])
        if k["kind"] not in KNOWN_KINDS:
            failures.append(f"[[known]] {key}: unknown kind")
        if key in known:
            failures.append(f"[[known]] {key}: duplicate entry")
        known[key] = int(k["count"])
    for key in sorted(set(found) | set(known)):
        have, want = found.get(key, 0), known.get(key, 0)
        rel, kind, text = key
        if have > want:
            failures.append(f"{rel}: {kind} {text!r} occurs {have} time(s), baseline allows {want}")
        elif have < want:
            failures.append(f"{rel}: baseline records {want} {kind} {text!r}, the file has {have}; "
                            f"lower or delete the [[known]] entry")

    # 4 and 5. Paths at the checked revisions and at the pin.
    if args.compare and not args.jolt_dir:
        fail_input("--compare needs --jolt-dir")
    if args.jolt_dir:
        jd = args.jolt_dir
        full_pin = resolve(jd, pin)
        if full_pin != pin:
            failures.append(f"pin {pin} is not a commit in {jd}")
        compare = []
        for rev in args.compare:
            full = resolve(jd, rev)
            if full is None:
                fail_input(f"--compare {rev} is not a commit in {jd}")
            compare.append(full)
        for rev in sorted(set(checked_of.values())):
            if resolve(jd, rev) != rev:
                failures.append(f"checked revision {rev} is not a commit in {jd}")
        missing_at: dict[str, list[str]] = {}
        for lean, e in sorted(by_file.items()):
            checked = e.get("checked")
            if checked and resolve(jd, checked) == checked:
                at = paths_at(jd, checked)
                for p in e["models"]:
                    if p not in at:
                        failures.append(f"{lean}: models path {p} does not exist at {checked}")
                text = (REPO / lean).read_text(encoding="utf-8", errors="replace")
                files = files_at(jd, checked)
                for p in sorted(cited_paths(text) & files - set(e["models"])):
                    failures.append(f"{lean}: cites {p}, a file at {checked}, but models omits it")
            elif lean in unpinned and full_pin == pin:
                at = paths_at(jd, pin)
                for p in e["models"]:
                    if p not in at:
                        failures.append(f"{lean}: models path {p} has no checked revision "
                                        f"and does not exist at the pin")
            for rev in ([pin] if full_pin == pin else []) + compare:
                at = paths_at(jd, rev)
                for p in e.get("models", []):
                    if p not in at:
                        missing_at.setdefault(rev, []).append(f"{lean}: {p}")
        for rev in ([pin] if full_pin == pin else []) + compare:
            label = "the pin" if rev == pin else "--compare"
            lines = missing_at.get(rev, [])
            notes.append(f"{len(lines)} models path(s) missing at {label} {rev}")
            notes += [f"  {line}" for line in lines]
        for o in manifest.get("other_revision", []):
            if resolve(jd, o["revision"]):
                notes.append(f"[[other_revision]] {o['revision']} ({o.get('repository')}) "
                             f"also names a commit in the Jolt clone; check it is not a Jolt revision")
        shallow = git(jd, "rev-parse", "--is-shallow-repository").stdout.strip() == "true"
        for (rel, kind, text) in sorted(found):
            if kind == "revision" and not shallow and resolve(jd, text) is None:
                notes.append(f"{rel}: revision {text} is not a commit in the Jolt clone")

    with_models = sum(1 for e in by_file.values() if e.get("models"))
    revs = Counter(checked_of.values())
    by_kind = Counter()
    for (rel, kind, text), c in found.items():
        by_kind[kind] += c
    print(f"provenance: pin {pin}")
    print(f"  {len(by_file)} [[file]] entries: {with_models} with models, "
          f"{len(by_file) - with_models} without, {len(unpinned)} with models but no checked revision")
    for rev, n in sorted(revs.items(), key=lambda kv: -kv[1]):
        print(f"  checked {rev}: {n} file(s)")
    print(f"  {sum(found.values())} baseline violation(s) found: "
          + ", ".join(f"{k} {v}" for k, v in sorted(by_kind.items())))
    for line in notes:
        print(f"note: {line}")
    if unpinned:
        print(f"note: {len(unpinned)} entries name models but no checked revision; see their notes")
    for line in failures:
        print(f"FAIL {line}")
    if failures:
        print(f"FAIL: {len(failures)} provenance check(s) failed")
        return 1
    print("OK: provenance checks passed" + ("" if args.jolt_dir else " (no --jolt-dir: paths not checked)"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
