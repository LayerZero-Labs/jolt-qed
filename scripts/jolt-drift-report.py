#!/usr/bin/env python3
"""Write the "Drift against Jolt main" report as Markdown on standard output.

Usage:
  scripts/jolt-drift-report.py [--jolt-dir PATH] [--main REV] [--monitor NAME=OUTCOME]...
      [--generation-status N] [--generated yes|partial|copy-failed|no] [--generated-stat FILE]
      [--generated-diff FILE] [--equiv-status N] [--upstream] [--run-url URL]

PATH is a Jolt checkout that holds both the pinned commit (`jolt_rev` in assumptions.toml)
and REV (default: HEAD, which the nightly job checks out from Jolt main). The report starts
with whether the run could monitor Jolt main, then lists:

- the registry entries whose anchor files changed between the pin and REV, and the anchors
  whose name no longer appears in the file at REV;
- every other Jolt file the Lean sources cite (scripts/jolt_citations.py) that changed, with
  the Lean files that cite it, and the citations that resolve to no file at the pin;
- `git diff --stat` of all those files;
- the result of regenerating the constraint data from REV, labelled by whether the generator
  produced new files, when the caller passes it;
- with --upstream, the state of each upstream issue, read with `gh api`.

Each --monitor NAME=OUTCOME records the outcome (`success`, `failure`, `skipped`, …) of a step
the report depends on, such as checking out Jolt main. Any outcome other than `success` or
`skipped` marks the run as a monitoring failure, which the report states first. Without
--jolt-dir, or when the checkout lacks the pin or REV, the anchor sections say that they could
not be computed. The report never repeats data from an earlier run.

Exit status: 0 when the report was written and monitoring succeeded, 3 when the report was
written and says that monitoring failed (a failed step, no usable Jolt checkout, or a failed
anchor comparison), and anything else when no report was written.
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tomllib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from jolt_citations import resolved_citations  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
ANCHOR = re.compile(r"^(?P<path>[\w./-]+) \((?P<name>[\w:]+)\)$")
MAX_DIFF = 30000
MAX_BODY = 64000  # GitHub limits an issue body to 65536 characters.
MAX_LIST = 60


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


def anchor_sections(out, jolt_dir, main, pin, entries):
    head = git(jolt_dir, "rev-parse", main).strip()
    git(jolt_dir, "cat-file", "-e", f"{pin}^{{commit}}")
    out[0] = (f"Jolt main `{head}` compared with the pin `{pin[:9]}` (`jolt_rev` in "
              "`assumptions.toml`).")
    anchor_paths = {ANCHOR.match(a).group("path") for e in entries for a in e["anchors"]}
    cited, unresolved = resolved_citations(jolt_dir, pin)
    paths = sorted(anchor_paths | cited.keys())
    changed = set(git(jolt_dir, "diff", "--name-only", pin, head, "--", *paths).split())

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
            text = file_at(jolt_dir, head, path)
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

    out.append("## Other cited Jolt files that changed")
    out.append("")
    other = sorted(p for p in changed if p in cited and p not in anchor_paths)
    out.append(f"The Lean sources cite {len(cited)} Jolt files that exist at the pin; "
               f"{len(other)} of them changed and back no registry anchor.")
    out.append("")
    for path in other[:MAX_LIST]:
        gone = " (gone at main)" if file_at(jolt_dir, head, path) is None else ""
        out.append(f"- `{path}`{gone}: cited by {', '.join(f'`{f}`' for f in sorted(cited[path]))}")
    if len(other) > MAX_LIST:
        out.append(f"- … and {len(other) - MAX_LIST} more (the run's log has the full list)")
    out.append("")
    if unresolved:
        out.append(f"<details><summary>{len(unresolved)} citations resolve to no file at the pin "
                   "(stale paths, other repositories, or ambiguous suffixes)</summary>\n")
        for citation in sorted(unresolved):
            out.append(f"- `{citation}`: {', '.join(sorted(unresolved[citation]))}")
        out.append("\n</details>")
        out.append("")

    out.append("## Changed files")
    out.append("")
    stat = git(jolt_dir, "diff", "--stat", pin, head, "--", *paths).strip()
    out.append("```text\n" + (stat or "no anchor or cited file changed") + "\n```")
    out.append("")


def generation_section(out, args):
    out.append("## Constraint data regenerated from Jolt main")
    out.append("")
    status = args.generation_status
    if status in (None, ""):
        out.append("The generator did not run, so this section has no data.")
        out.append("")
        return
    meaning = {"0": "its checks passed", "1": "a generator check failed",
               "2": "the generator could not run, often because Jolt main changed an API it "
                    "uses"}.get(status, "unexpected status")
    out.append(f"`scripts/expansion-parity/run-constraint-gen.sh` exited with {status} "
               f"({meaning}). It wrote into an empty directory.")
    produced = args.generated or "no"
    if produced != "yes":
        what = {"partial": "only some of the three files",
                "copy-failed": "all three files, but copying them over the committed ones failed"
                }.get(produced, "no file")
        out.append(f"It produced {what}, so there is no regenerated data to compare and the "
                   "equivalence proofs were not built on it.")
        out.append("")
        return
    out.append("It produced all three files; the comparison below is with the committed ones.")
    if args.equiv_status not in (None, ""):
        verdict = ("builds on the regenerated data" if args.equiv_status == "0" else
                   "does not build on the regenerated data" if args.equiv_status.isdigit() else
                   f"was not built on the regenerated data ({args.equiv_status})")
        out.append(f"`JoltConstraints.ConstraintGen.Equiv` {verdict}.")
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


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--jolt-dir")
    parser.add_argument("--main", default="HEAD")
    parser.add_argument("--monitor", action="append", default=[])
    parser.add_argument("--generated-stat")
    parser.add_argument("--generated-diff")
    parser.add_argument("--generated")
    parser.add_argument("--generation-status")
    parser.add_argument("--equiv-status")
    parser.add_argument("--upstream", action="store_true")
    parser.add_argument("--run-url", default="")
    args = parser.parse_args()

    registry = tomllib.loads((ROOT / "assumptions.toml").read_text())
    pin = registry["jolt_rev"]
    entries = registry["entry"]

    failures = []
    for item in args.monitor:
        name, _, outcome = item.partition("=")
        if outcome not in ("success", "skipped"):
            failures.append(f"`{name}`: {outcome or 'no outcome'}")

    out = [f"Jolt main compared with the pin `{pin[:9]}` (`jolt_rev` in `assumptions.toml`)."]
    if args.run_url:
        out.append(f"Written by [this run]({args.run_url}); each night's run replaces this text, "
                   "including when it fails.")
    out.append("")
    anchors = []
    if not args.jolt_dir:
        failures.append("no Jolt checkout")
    else:
        anchors.append("")
        try:
            anchor_sections(anchors, args.jolt_dir, args.main, pin, entries)
        except (subprocess.CalledProcessError, OSError) as exc:
            failures.append(f"comparing the anchors failed: {exc}")
            anchors = []
    if failures:
        out.append("**Monitoring failed in this run.** Sections that depend on the failed steps "
                   "are missing; nothing below is carried over from an earlier run. Failed:")
        out.extend(f"- {failure}" for failure in failures)
    else:
        out.append("**Monitoring succeeded.** Anything listed below is drift, not a failure of "
                   "this job.")
    out.append("")
    if anchors:
        out[0] = anchors[0]
        out.extend(anchors[1:])
    else:
        out.append("## Registry entries and cited files")
        out.append("")
        out.append("Not computed: this run has no usable Jolt checkout.")
        out.append("")

    generation_section(out, args)

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

    report = "\n".join(out)
    if len(report) > MAX_BODY:
        report = report[:MAX_BODY] + "\n\n… (cut to fit an issue; the run's log has the rest)\n"
    print(report)
    return 3 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
