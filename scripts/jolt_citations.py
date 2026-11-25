#!/usr/bin/env python3
"""List every Jolt source file the Lean model cites, resolved against a Jolt commit.

Usage: scripts/jolt_citations.py --jolt-dir PATH [--rev REV] [--unresolved]

The model cites the Jolt code it transcribes in comments and docstrings, as a path
(`tracer/src/emulator/mmu.rs`), a GitHub URL, a path under some local Jolt checkout, or a
shorter suffix (`expand/memory/scd.rs`). This script collects every `.rs` path mentioned in
JoltBytecode/ and JoltConstraints/, and resolves each one against the tree of REV (default:
`jolt_rev` in assumptions.toml) in the Jolt checkout PATH:

- a full path that exists at REV resolves to itself;
- a URL or a path under a checkout resolves after its prefix is removed;
- a suffix resolves to the one file at REV that ends with it, if exactly one does.

It prints one resolved path per line, followed by the Lean files that cite it. With
--unresolved it prints the citations that resolve to no file instead: stale paths, files of
other repositories, or suffixes that match several files.

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
PREFIXES = [
    re.compile(r"^(?:https?:)?//github\.com/a16z/jolt/(?:blob|tree)/[^/]+/"),
    re.compile(r"^.*/jolt/"),
    re.compile(r"^jolt/"),
]


def cited_paths():
    """Return {citation: {Lean file}} for every `.rs` path in the Lean sources."""
    cited = {}
    for folder in ("JoltBytecode", "JoltConstraints"):
        for path in sorted((ROOT / folder).rglob("*.lean")):
            for match in CITATION.finditer(path.read_text()):
                cited.setdefault(match.group(0), set()).add(str(path.relative_to(ROOT)))
    return cited


def tree(jolt_dir, rev):
    listing = subprocess.run(["git", "-C", jolt_dir, "ls-tree", "-r", "--name-only", rev],
                             capture_output=True, text=True, check=True).stdout
    return set(listing.split())


def resolve(citation, files, by_name):
    """The file at the revision that `citation` names, or None."""
    path = citation
    for prefix in PREFIXES:
        path = prefix.sub("", path)
    path = path.lstrip("./")
    if path in files:
        return path
    candidates = [f for f in by_name.get(path.rsplit("/", 1)[-1], []) if f.endswith("/" + path)]
    return candidates[0] if len(candidates) == 1 else None


def resolved_citations(jolt_dir, rev):
    """Return ({Jolt path: {Lean file}}, {unresolved citation: {Lean file}})."""
    files = tree(jolt_dir, rev)
    by_name = {}
    for f in files:
        by_name.setdefault(f.rsplit("/", 1)[-1], []).append(f)
    resolved, unresolved = {}, {}
    for citation, lean_files in cited_paths().items():
        path = resolve(citation, files, by_name)
        target = resolved if path else unresolved
        target.setdefault(path or citation, set()).update(lean_files)
    return resolved, unresolved


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--jolt-dir", required=True)
    parser.add_argument("--rev")
    parser.add_argument("--unresolved", action="store_true")
    args = parser.parse_args()
    rev = args.rev or tomllib.loads((ROOT / "assumptions.toml").read_text())["jolt_rev"]
    resolved, unresolved = resolved_citations(args.jolt_dir, rev)
    shown = unresolved if args.unresolved else resolved
    for path in sorted(shown):
        print(f"{path}  ({', '.join(sorted(shown[path]))})")
    print(f"jolt_citations: {len(resolved)} cited files resolve at {rev[:9]}, "
          f"{len(unresolved)} citations do not", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
