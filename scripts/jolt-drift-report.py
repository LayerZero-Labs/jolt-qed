#!/usr/bin/env python3
"""Write the "Drift against Jolt main" report as Markdown on standard output.

Usage:
  scripts/jolt-drift-report.py [--jolt-dir PATH] [--main REV] [--monitor NAME=OUTCOME]...
      [--generation-status N] [--generated yes|partial|copy-failed|no] [--generated-stat FILE]
      [--generated-diff FILE] [--equiv-status N] [--upstream] [--run-url URL]
      [--evidence-dir DIR]

PATH is a Jolt checkout that holds both the pinned commit (`jolt_rev` in assumptions.toml)
and REV (default: HEAD, which the nightly job checks out from Jolt main). The report starts
with whether the run could monitor Jolt main, then lists:

- the registry entries whose anchor files changed between the pin and REV, and the anchors
  whose name no longer appears in the file at REV;
- every other Jolt file the Lean sources cite (scripts/jolt_citations.py) that changed, with
  the Lean files that cite it, and the citations that resolve to no file at the pin;
- every other changed production Rust file or build input (`*.rs` outside tests, benches and
  examples, `Cargo.toml`, `Cargo.lock`, `rust-toolchain*`, `build.rs`) in a watched directory,
  as "unclassified": a change the citations miss, such as a new instruction's `exec` in a file
  no comment cites, still shows (see `classify_changes`). The watched directories are every
  crate of Jolt's workspace at the pin or at REV except the few in `EXCLUDED_CRATES`, plus
  `tracer/`, `common/` and the directory of each cited file. The section also names the crates
  that REV adds to the workspace;
- `git diff --stat` of all those files;
- the result of regenerating the constraint data from REV, labelled by whether the generator
  produced new files, when the caller passes it;
- with --upstream, the state of each upstream issue, read with `gh api`.

The issue body has a size limit, so the report shortens long lists and diffs. With
--evidence-dir it also writes the full data to DIR, which the nightly job uploads as the run's
`drift-evidence` artifact, and each shortened part points there:

- `report.md`: the report with every list and diff in full;
- `changed-files.tsv`: every Jolt file changed between the pin and REV, with its group
  (anchored, cited, unclassified, other), the Lean files that cite it and the registry entries
  anchored in it;
- `unresolved-citations.txt`: the citations that resolve to no file at the pin;
- `jolt-diff.stat` and `jolt-diff.patch`: `git diff --stat` of every changed file, and the full
  diff of the anchored, cited and unclassified ones;
- `generated.stat` and `generated.diff`: the comparison of the regenerated constraint data
  with the committed files, when the caller passes them.

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
import fnmatch
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
ARTIFACT = "drift-evidence"

# Directories that are always watched, whatever the workspace lists. Every crate of the
# workspace except those in EXCLUDED_CRATES, and every directory that holds a cited file (see
# `watched_directories`), is watched too.
WATCHED = ("tracer/", "common/")
# Workspace crates whose code cannot change what the model represents, by directory prefix,
# each with the reason. Keep this list short: a crate missing from it is watched, which costs a
# reader a look, while a crate wrongly on it hides drift.
EXCLUDED_CRATES = (
    ("examples/", "example host and guest programs built on the SDK"),
    ("jolt-eval", "a harness of invariants and red-team runs for agents"),
    ("jolt-inlines/fixtures", "fixture tests of the inline expansions"),
    ("z3-verifier", "SMT experiments on the constraints, written as tests"),
    ("crates/jolt-profiling", "profiling and tracing infrastructure"),
)
BUILD_INPUTS = re.compile(r"(?:^|/)(?:Cargo\.toml|Cargo\.lock|rust-toolchain(?:\.toml)?|build\.rs)$")
NOT_PRODUCTION = re.compile(r"(?:^|/)(?:tests|benches|examples)/")


def watched_directories(cited):
    """`WATCHED` plus the directory of each cited file: `crates/<name>/` for a crate, otherwise
    the top-level directory (`jolt-platform/`)."""
    found = set(WATCHED)
    for path in cited:
        parts = path.split("/")
        if parts[0] == "crates" and len(parts) > 2:
            found.add(f"crates/{parts[1]}/")
        elif len(parts) > 1:
            found.add(f"{parts[0]}/")
    return sorted(found)


def workspace_members(jolt_dir, rev):
    """The `members` of `[workspace]` in Jolt's top-level Cargo.toml at `rev`, and "." when that
    file also declares a package (the `jolt` command-line tool in `src/`). Raise `ValueError`
    when the file is missing or is not TOML, since the watched directories then are unknown."""
    text = file_at(jolt_dir, rev, "Cargo.toml")
    if text is None:
        raise ValueError(f"Jolt has no top-level Cargo.toml at {rev}")
    manifest = tomllib.loads(text)
    members = [member.strip("/") for member in manifest.get("workspace", {}).get("members", [])]
    return members + (["."] if "package" in manifest else [])


def crate_of(path, members):
    """The directory of the workspace crate that holds `path`: the longest member that contains
    it (a member may be a pattern such as `crates/*`), "." for `src/` and `build.rs` of the
    top-level package, or None."""
    parts = path.split("/")
    best = None
    for member in members:
        pattern = member.split("/")
        if (member != "." and len(parts) > len(pattern)
                and all(fnmatch.fnmatchcase(p, q) for p, q in zip(parts, pattern))
                and (best is None or len(pattern) > len(best.split("/")))):
            best = "/".join(parts[:len(pattern)])
    if best is None and "." in members and (parts[0] == "src" or path == "build.rs"):
        best = "."
    return best


def excluded_reason(crate):
    """The reason `EXCLUDED_CRATES` gives for the crate directory `crate`, or None."""
    for prefix, reason in EXCLUDED_CRATES:
        prefix = prefix.rstrip("/")
        if crate == prefix or crate.startswith(prefix + "/"):
            return reason
    return None


def classify_changes(changed, anchor_paths, cited, watched, members=()):
    """Sort every changed path into "anchored", "cited", "unclassified" and "other".

    A path is "unclassified" when no anchor or citation names it and it is a build input at the
    top level of Jolt or in a watched directory, or production Rust (`*.rs` outside `tests/`,
    `benches/` and `examples/`) in a watched directory. A watched directory is one in `watched`
    or a crate of the workspace `members` that `EXCLUDED_CRATES` does not list. Everything else
    is "other": tests, documentation, excluded crates, and directories outside the workspace.
    """
    groups = {"anchored": [], "cited": [], "unclassified": [], "other": []}
    for path in sorted(changed):
        if path in anchor_paths:
            group = "anchored"
        elif path in cited:
            group = "cited"
        else:
            crate = crate_of(path, members)
            in_watched = (any(path.startswith(d) for d in watched)
                          or (crate is not None and excluded_reason(crate) is None))
            build_input = BUILD_INPUTS.search(path) and ("/" not in path or in_watched)
            production = (in_watched and path.endswith(".rs")
                          and not NOT_PRODUCTION.search(path))
            group = "unclassified" if build_input or production else "other"
        groups[group].append(path)
    return groups


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


def compare(jolt_dir, main, pin, entries, with_diffs=False):
    """Compare Jolt at `main` with the pin, and return what the anchor sections and the evidence
    files show. With `with_diffs`, also read the diff statistic of every changed file and the
    full diff of the anchored, cited and unclassified ones. Raise `CalledProcessError` when Git
    fails and `ValueError` when a workspace manifest cannot be read."""
    head = git(jolt_dir, "rev-parse", main).strip()
    git(jolt_dir, "cat-file", "-e", f"{pin}^{{commit}}")
    anchor_paths = {ANCHOR.match(a).group("path") for e in entries for a in e["anchors"]}
    cited, unresolved = resolved_citations(jolt_dir, pin)
    # --no-renames lists a renamed file under its old and its new path. With -z, each change is
    # a status letter and a path.
    fields = git(jolt_dir, "diff", "--name-status", "--no-renames", "-z", pin, head).split("\0")
    status = {path: {"A": "added", "D": "deleted"}.get(letter, "modified")
              for letter, path in zip(fields[0::2], fields[1::2]) if path}
    # Both lists count: a crate that only the pin lists still holds changed (deleted) files.
    members_pin = workspace_members(jolt_dir, pin)
    members_main = workspace_members(jolt_dir, head)
    groups = classify_changes(set(status), anchor_paths, cited, watched_directories(cited),
                              sorted(set(members_pin) | set(members_main)))
    changed = set(groups["anchored"]) | set(groups["cited"])

    flagged = []
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
            flagged.append((entry, hits))

    # The Lean files and registry entries that each changed file backs.
    entries_of = {}
    for entry in entries:
        for anchor in entry["anchors"]:
            entries_of.setdefault(ANCHOR.match(anchor).group("path"), set()).add(entry["name"])
    paths = sorted(changed | set(groups["unclassified"]))
    result = {
        "head": head, "cited": cited, "unresolved": unresolved, "status": status,
        "groups": groups, "flagged": flagged,
        "new_crates": sorted(set(members_main) - set(members_pin)),
        "other_cited": sorted(p for p in changed if p in cited and p not in anchor_paths),
        "lean_files": {p: sorted(cited.get(p, ())) for p in status},
        "entries_of": {p: sorted(entries_of.get(p, ())) for p in status},
        "stat": (git(jolt_dir, "diff", "--stat", "--no-renames", pin, head, "--", *paths).strip()
                 if paths else ""),
    }
    if with_diffs:
        result["full_stat"] = git(jolt_dir, "diff", "--stat=200", "--no-renames", pin, head)
        result["patch"] = (git(jolt_dir, "diff", "--no-renames", pin, head, "--", *paths)
                           if paths else "")
    return result


def evidence_files(comparison):
    """The evidence files that hold the comparison's full lists and diffs, {file name: text}."""
    c = comparison
    files = {
        "changed-files.tsv": "group\tpath\tLean files citing it\tregistry entries anchored in it\n"
        + "".join(f"{group}\t{path}\t{', '.join(c['lean_files'][path])}\t"
                  f"{', '.join(c['entries_of'][path])}\n"
                  for group in c["groups"] for path in c["groups"][group]),
        "unresolved-citations.txt": "".join(
            f"{citation}\t{', '.join(sorted(files))}\n"
            for citation, files in sorted(c["unresolved"].items())),
    }
    if "patch" in c:
        files["jolt-diff.stat"] = c["full_stat"]
        files["jolt-diff.patch"] = c["patch"]
    return files


def shown(items, max_list):
    """The first `max_list` of `items` (all of them when `max_list` is None), and the number
    left out."""
    if max_list is None or len(items) <= max_list:
        return items, 0
    return items[:max_list], len(items) - max_list


def anchor_sections(out, comparison, max_list=None, full="a run with --evidence-dir"):
    """Append the anchor and citation sections of `comparison` (see `compare`) to `out`. Show
    at most `max_list` items of each list, or every item when it is None; `full` says where a
    reader finds the rest."""
    c = comparison
    groups, cited, unresolved = c["groups"], c["cited"], c["unresolved"]

    out.append("## Registry entries whose anchor files changed")
    out.append("")
    for entry, hits in c["flagged"]:
        out.append(f"- **{entry['name']}** ({entry['kind']}, `{entry['lean']}`)")
        out.extend(f"  - {hit}" for hit in hits)
    if not c["flagged"]:
        out.append("None.")
    out.append("")
    out.append("For each flagged entry, read the Jolt change and ask whether it makes the entry "
               "provable. A premise that a new Jolt check guarantees should be removed; its "
               "necessity witness stops building once the check is transcribed.")
    out.append("")

    out.append("## Other cited Jolt files that changed")
    out.append("")
    other = c["other_cited"]
    out.append(f"The Lean sources cite {len(cited)} Jolt files that exist at the pin; "
               f"{len(other)} of them changed and back no registry anchor.")
    out.append("")
    listed, rest = shown(other, max_list)
    for path in listed:
        gone = " (gone at main)" if c["status"][path] == "deleted" else ""
        out.append(f"- `{path}`{gone}: cited by {', '.join(f'`{f}`' for f in sorted(cited[path]))}")
    if rest:
        out.append(f"- … and {rest} more ({full} has the full list, with the Lean files citing "
                   "each one, in `changed-files.tsv`)")
    out.append("")
    if unresolved:
        out.append(f"<details><summary>{len(unresolved)} citations resolve to no file at the pin "
                   "(stale paths, other repositories, or ambiguous suffixes)</summary>\n")
        for citation in sorted(unresolved):
            out.append(f"- `{citation}`: {', '.join(sorted(unresolved[citation]))}")
        out.append("\n</details>")
        out.append("")

    unclassified = groups["unclassified"]
    out.append("## Unclassified changed files")
    out.append("")
    out.append(f"{len(c['status'])} Jolt files changed between the pin and main: "
               f"{len(groups['anchored'])} anchored, {len(groups['cited'])} cited by the Lean "
               f"sources, {len(unclassified)} unclassified and {len(groups['other'])} other. "
               "An unclassified file is production Rust or a build input (`Cargo.toml`, "
               "`Cargo.lock`, `rust-toolchain*`, `build.rs`) that no anchor or citation names, "
               "in a crate of Jolt's workspace, `tracer/`, `common/` or the directory of a cited "
               "file; read each one and decide whether the model transcribes it. The other "
               "files are tests, documentation, directories outside the workspace, and these "
               "crates, which are not watched: "
               + "; ".join(f"`{prefix}` ({reason})" for prefix, reason in EXCLUDED_CRATES)
               + ".")
    out.append("")
    for crate in c["new_crates"]:
        reason = excluded_reason(crate)
        watched = f"not watched: {reason}" if reason else "its files are watched"
        out.append(f"- crate `{crate}/` (added to the workspace since the pin; {watched})")
    listed, rest = shown(unclassified, max_list)
    for path in listed:
        out.append(f"- `{path}` ({c['status'][path]})")
    if rest:
        out.append(f"- … and {rest} more ({full} has the full list in `changed-files.tsv`)")
    if not unclassified and not c["new_crates"]:
        out.append("None.")
    out.append("")

    out.append("## Changed files")
    out.append("")
    out.append("```text\n" + (c["stat"] or "no anchored, cited or unclassified file changed")
               + "\n```")
    out.append(f"{full[0].upper() + full[1:]} has the full diff of these files "
               "(`jolt-diff.patch`) and the statistic of every changed file (`jolt-diff.stat`).")
    out.append("")


def generation_section(out, args, max_diff=None, full="a run with --evidence-dir"):
    """Append the section on the regenerated constraint data to `out`. Cut its diff after
    `max_diff` characters, or never when it is None; `full` says where a reader finds the rest."""
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
        if max_diff is not None and len(diff) > max_diff:
            diff = diff[:max_diff] + f"\n… (cut; {full} has the full diff in `generated.diff`)\n"
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
    parser.add_argument("--evidence-dir", type=pathlib.Path,
                        help="write the full report, lists and diffs here (see above)")
    args = parser.parse_args()

    registry = tomllib.loads((ROOT / "assumptions.toml").read_text())
    pin = registry["jolt_rev"]
    entries = registry["entry"]

    if args.run_url:
        full = f"the [`{ARTIFACT}` artifact]({args.run_url}#artifacts) of this run"
    elif args.evidence_dir:
        full = f"`{args.evidence_dir}`"
    else:
        full = "a run with --evidence-dir"
    failures = []
    for item in args.monitor:
        name, _, outcome = item.partition("=")
        if outcome not in ("success", "skipped"):
            failures.append(f"`{name}`: {outcome or 'no outcome'}")

    comparison = None
    if not args.jolt_dir:
        failures.append("no Jolt checkout")
    else:
        try:
            comparison = compare(args.jolt_dir, args.main, pin, entries,
                                 with_diffs=bool(args.evidence_dir))
        except (subprocess.CalledProcessError, OSError, ValueError) as exc:
            failures.append(f"comparing the anchors failed: {exc}")

    upstream = None
    if args.upstream:
        seen = {}
        for entry in entries:
            if entry.get("upstream"):
                seen.setdefault(entry["upstream"], []).append(entry["name"])
        upstream = [(reference, upstream_state(reference), names)
                    for reference, names in sorted(seen.items())]

    def render(max_list, max_diff):
        return render_report(args, pin, failures, comparison, upstream, full, max_list,
                             max_diff)

    # The issue body shows at most MAX_LIST items of a list and MAX_DIFF characters of a diff;
    # the evidence report shows everything.
    report = render(MAX_LIST, MAX_DIFF)
    if args.evidence_dir:
        evidence = evidence_files(comparison) if comparison else {}
        evidence["report.md"] = render(None, None) + "\n"
        for name, source in (("generated.stat", args.generated_stat),
                             ("generated.diff", args.generated_diff)):
            if read(source):
                evidence[name] = read(source)
        args.evidence_dir.mkdir(parents=True, exist_ok=True)
        for name, text in evidence.items():
            (args.evidence_dir / name).write_text(text)
    if len(report) > MAX_BODY:
        report = (report[:MAX_BODY] + f"\n\n… (cut to fit an issue; {full} has the full report "
                  "in `report.md`)\n")
    print(report)
    return 3 if failures else 0


def render_report(args, pin, failures, comparison, upstream, full, max_list, max_diff):
    """The report as Markdown. Lists show at most `max_list` items and the diff of the
    generated data at most `max_diff` characters; None means no limit."""
    if comparison:
        out = [f"Jolt main `{comparison['head']}` compared with the pin `{pin[:9]}` (`jolt_rev` "
               "in `assumptions.toml`)."]
    else:
        out = [f"Jolt main compared with the pin `{pin[:9]}` (`jolt_rev` in `assumptions.toml`)."]
    if args.run_url:
        out.append(f"Written by [this run]({args.run_url}); each night's run replaces this text, "
                   "including when it fails.")
    out.append("")
    if failures:
        out.append("**Monitoring failed in this run.** Sections that depend on the failed steps "
                   "are missing; nothing below is carried over from an earlier run. Failed:")
        out.extend(f"- {failure}" for failure in failures)
    else:
        out.append("**Monitoring succeeded.** Anything listed below is drift, not a failure of "
                   "this job.")
    out.append("")
    if comparison:
        anchor_sections(out, comparison, max_list, full)
    else:
        out.append("## Registry entries and cited files")
        out.append("")
        out.append("Not computed: this run has no usable Jolt checkout.")
        out.append("")

    generation_section(out, args, max_diff, full)

    if upstream is not None:
        out.append("## Upstream issues")
        out.append("")
        for reference, state, names in upstream:
            out.append(f"- {reference}: {state} (entries: {', '.join(names)})")
        if not upstream:
            out.append("None.")
        out.append("")
    return "\n".join(out)


if __name__ == "__main__":
    sys.exit(main())
