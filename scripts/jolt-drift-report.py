#!/usr/bin/env python3
"""Write the "Drift against Jolt main" report as Markdown on standard output.

Usage:
  scripts/jolt-drift-report.py --jolt-dir PATH [--main REV] [--generated-stat FILE]
      [--generated-diff FILE] [--generation-status N] [--equiv-status N]
      [--upstream] [--run-url URL]

PATH is a Jolt checkout that holds both the pinned commit (`jolt_rev` in assumptions.toml)
and REV (default: HEAD, which the nightly job checks out from Jolt main). The report lists:

- the registry entries whose anchor files changed between the pin and REV, and the anchors
  whose name no longer appears in the file at REV;
- `git diff --stat` of every anchor file;
- the result of regenerating the constraint data from REV, when the caller passes it;
- with --upstream, the state of each upstream issue, read with `gh api`.

Anchors are compared file by file. Function-level anchors (hashing each cited function's
body) build on the provenance scripts of jolt-qed#56 and come later.
"""

import argparse
import pathlib
import re
import subprocess
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
ANCHOR = re.compile(r"^(?P<path>[\w./-]+) \((?P<name>[\w:]+)\)$")
MAX_DIFF = 30000  # GitHub limits an issue body to 65536 characters.


def git(jolt_dir, *args):
    return subprocess.run(["git", "-C", jolt_dir, *args], capture_output=True, text=True,
                          check=True).stdout


def file_at(jolt_dir, rev, path):
    shown = subprocess.run(["git", "-C", jolt_dir, "show", f"{rev}:{path}"], capture_output=True,
                           text=True)
    return shown.stdout if shown.returncode == 0 else None


def upstream_state(reference):
    match = re.fullmatch(r"([\w.-]+/[\w.-]+)#(\d+)", reference)
    if not match:
        return "not a GitHub reference"
    result = subprocess.run(["gh", "api", f"repos/{match.group(1)}/issues/{match.group(2)}",
                             "--jq", ".state"], capture_output=True, text=True)
    return result.stdout.strip() if result.returncode == 0 else "could not read"


def read(path):
    return pathlib.Path(path).read_text() if path and pathlib.Path(path).exists() else ""


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--jolt-dir", required=True)
    parser.add_argument("--main", default="HEAD")
    parser.add_argument("--generated-stat")
    parser.add_argument("--generated-diff")
    parser.add_argument("--generation-status")
    parser.add_argument("--equiv-status")
    parser.add_argument("--upstream", action="store_true")
    parser.add_argument("--run-url", default="")
    args = parser.parse_args()

    registry = tomllib.loads((ROOT / "assumptions.toml").read_text())
    pin = registry["jolt_rev"]
    head = git(args.jolt_dir, "rev-parse", args.main).strip()
    entries = registry["entry"]
    paths = sorted({ANCHOR.match(a).group("path") for e in entries for a in e["anchors"]})
    changed = set(git(args.jolt_dir, "diff", "--name-only", pin, head, "--", *paths).split())

    out = [f"Jolt main `{head}` compared with the pin `{pin[:9]}` (`jolt_rev` in "
           "`assumptions.toml`)."]
    if args.run_url:
        out.append(f"Written by [this run]({args.run_url}); each night's run replaces this text.")
    out.append("")

    out.append("## Registry entries whose anchor files changed")
    out.append("")
    flagged = 0
    for entry in entries:
        hits = []
        for anchor in entry["anchors"]:
            match = ANCHOR.match(anchor)
            path, name = match.group("path"), match.group("name").split("::")[-1]
            if path not in changed:
                continue
            text = file_at(args.jolt_dir, head, path)
            if text is None:
                hits.append(f"`{anchor}`: the file is gone")
            elif not re.search(rf"\b{re.escape(name)}\b", text):
                hits.append(f"`{anchor}`: the file changed and no longer mentions `{name}`")
            else:
                hits.append(f"`{anchor}`: the file changed")
        if hits:
            flagged += 1
            out.append(f"- **{entry['name']}** ({entry['kind']}, `{entry['lean']}`)")
            out.extend(f"  - {hit}" for hit in hits)
    if not flagged:
        out.append("None.")
    out.append("")
    out.append("For each flagged entry, read the Jolt change and ask whether it makes the entry "
               "provable. A premise that a new Jolt check guarantees should be removed; its "
               "necessity witness stops building once the check is transcribed.")
    out.append("")

    out.append("## Anchor files")
    out.append("")
    stat = git(args.jolt_dir, "diff", "--stat", pin, head, "--", *paths).strip()
    out.append("```text\n" + (stat or "no anchor file changed") + "\n```")
    out.append("")

    if args.generation_status is not None:
        out.append("## Constraint data regenerated from Jolt main")
        out.append("")
        status = args.generation_status
        meaning = {"0": "its checks passed", "1": "a generator check failed",
                   "2": "the generator could not run"}.get(status, "unexpected status")
        out.append(f"`scripts/expansion-parity/run-constraint-gen.sh` exited with {status} "
                   f"({meaning}).")
        if args.equiv_status is not None:
            verdict = "builds" if args.equiv_status == "0" else "does not build"
            out.append(f"`JoltConstraints.ConstraintGen.Equiv` {verdict} on the regenerated data.")
        generated = read(args.generated_stat).strip()
        out.append("")
        out.append("```text\n" + (generated or "the generated files did not change") + "\n```")
        diff = read(args.generated_diff)
        if diff:
            if len(diff) > MAX_DIFF:
                diff = diff[:MAX_DIFF] + "\n… (cut; the run's log has the rest)\n"
            out.append("")
            out.append("<details><summary>Diff of the generated files</summary>\n")
            out.append("```diff\n" + diff + "```\n</details>")
        out.append("")

    if args.upstream:
        out.append("## Upstream issues")
        out.append("")
        seen = {}
        for entry in entries:
            if entry.get("upstream"):
                seen.setdefault(entry["upstream"], []).append(entry["name"])
        for reference, names in sorted(seen.items()):
            out.append(f"- {reference}: {upstream_state(reference)} "
                       f"(entries: {', '.join(names)})")
        if not seen:
            out.append("None.")
        out.append("")

    print("\n".join(out))


if __name__ == "__main__":
    main()
