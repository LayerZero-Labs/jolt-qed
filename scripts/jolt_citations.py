#!/usr/bin/env python3
"""List every Jolt source file the Lean model cites, resolved against a Jolt commit.

Usage: scripts/jolt_citations.py --jolt-dir PATH [--rev REV] [--lean-root DIR] [--unresolved]

The model cites the Jolt code it transcribes in comments and docstrings, as a path
(`tracer/src/emulator/mmu.rs`), a GitHub URL, a path under some local Jolt checkout, or a
shorter suffix (`expand/memory/scd.rs`). This script collects every `.rs` path mentioned in
JoltBytecode/ and JoltConstraints/, and resolves each one against the tree of REV (default:
`jolt_rev` in assumptions.toml) in the Jolt checkout PATH:

- a full path that exists at REV resolves to itself;
- a URL or a path under a checkout resolves after its prefix is removed;
- a suffix resolves to the one file at REV that ends with it, if exactly one does.

It prints one resolved path per line, followed by the Lean files that cite it. With
--unresolved it prints the citations that resolve to no file instead: stale paths or
suffixes that match several files. A brace list (`relations/{ram,registers}/x.rs`) counts as
one citation per alternative. Citations of vendored crates (`dory-pcs-0.4.2/src/...`) and of
this repository's `scripts/` are skipped.

scripts/jolt-drift-report.py uses the resolved set, together with the anchors in
assumptions.toml, as the files it compares with Jolt main, so a newly cited file is watched
without a registry edit.
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
CITATION = re.compile(r"[A-Za-z0-9_./:-]*[A-Za-z0-9_-]\.rs\b")
# A brace list names one file per alternative: `virt/{load,store}_{b,h,w}.rs` is six files.
BRACED = re.compile(r"[A-Za-z0-9_./:{},-]*\{[A-Za-z0-9_./:{},-]*\.rs\b")
BRACE = re.compile(r"\{([A-Za-z0-9_./:-]*(?:,[A-Za-z0-9_./:-]*)+)\}")
# Rust sources outside Jolt: a vendored crate (`dory-pcs-0.4.2/src/...`) or this
# repository's own generator (`scripts/...`). They are listed apart, not as stale.
EXTERNAL = re.compile(r"^(?:[A-Za-z0-9_-]+-\d+\.\d+\.\d+/|scripts/)")
URL_PREFIX = re.compile(r"^(?:https?:)?//github\.com/a16z/jolt/(?:blob|tree)/[^/]+/")
# A path under a local checkout, such as `~/src/jolt/tracer/...`. Tried shortest first, so
# that a path segment named `jolt` inside Jolt's own tree (`protocols/jolt/...`) is kept.
CHECKOUT_PREFIX = re.compile(r"(?:^|/)jolt/")


def cited_paths(root=ROOT):
    """Return {citation: {Lean file}} for every `.rs` path in the Lean sources."""
    cited = {}
    for folder in ("JoltBytecode", "JoltConstraints"):
        for path in sorted((root / folder).rglob("*.lean")):
            text = BRACED.sub(lambda m: " ".join(expand_braces(m.group(0))),
                              path.read_text())
            for match in CITATION.finditer(text):
                cited.setdefault(match.group(0), set()).add(str(path.relative_to(root)))
    return cited


def expand_braces(citation):
    """Expand every `{a,b}` group: `x_{b,h}.rs` becomes [`x_b.rs`, `x_h.rs`]."""
    match = BRACE.search(citation)
    if not match:
        return [citation]
    return [expanded
            for alt in match.group(1).split(",")
            for expanded in expand_braces(citation[:match.start()] + alt
                                          + citation[match.end():])]


def tree(jolt_dir, rev):
    listing = subprocess.run(["git", "-C", jolt_dir, "ls-tree", "-r", "--name-only", rev],
                             capture_output=True, text=True, check=True).stdout
    return set(listing.split())


def resolve(citation, files, by_name):
    """The file at the revision that `citation` names, or None.

    It tries the citation as written, then without a GitHub URL prefix, then without each
    possible local-checkout prefix, first as a full path and then as a unique suffix.
    """
    stripped = URL_PREFIX.sub("", citation).lstrip("./")
    forms = [citation.lstrip("./"), stripped]
    forms += [stripped[m.end():] for m in CHECKOUT_PREFIX.finditer(stripped)]
    for path in forms:
        if path in files:
            return path
    for path in forms:
        candidates = [f for f in by_name.get(path.rsplit("/", 1)[-1], [])
                      if f == path or f.endswith("/" + path)]
        if len(candidates) == 1:
            return candidates[0]
    return None


def resolved_citations(jolt_dir, rev, root=ROOT):
    """Return ({Jolt path: {Lean file}}, {unresolved citation: {Lean file}}).

    Citations of Rust outside Jolt (see EXTERNAL) appear in neither dictionary.
    """
    files = tree(jolt_dir, rev)
    by_name = {}
    for f in files:
        by_name.setdefault(f.rsplit("/", 1)[-1], []).append(f)
    resolved, unresolved = {}, {}
    for citation, lean_files in cited_paths(root).items():
        if EXTERNAL.match(citation):
            continue
        path = resolve(citation, files, by_name)
        target = resolved if path else unresolved
        target.setdefault(path or citation, set()).update(lean_files)
    return resolved, unresolved


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--jolt-dir", required=True)
    parser.add_argument("--rev")
    parser.add_argument("--lean-root", type=pathlib.Path, default=ROOT,
                        help="the jolt-qed checkout whose Lean files are scanned (default: this one)")
    parser.add_argument("--unresolved", action="store_true")
    args = parser.parse_args()
    rev = args.rev or tomllib.loads((ROOT / "assumptions.toml").read_text())["jolt_rev"]
    resolved, unresolved = resolved_citations(args.jolt_dir, rev, args.lean_root)
    shown = unresolved if args.unresolved else resolved
    for path in sorted(shown):
        print(f"{path}  ({', '.join(sorted(shown[path]))})")
    print(f"jolt_citations: {len(resolved)} cited files resolve at {rev[:9]}, "
          f"{len(unresolved)} citations do not", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
