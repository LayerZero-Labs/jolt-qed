#!/usr/bin/env python3
"""Check that assumptions.toml covers every premise, sorry and image field.

Usage: scripts/check-assumptions.py [--jolt-dir PATH]

Run from anywhere; paths are relative to the repository root. The script checks:

1. Every entry has the required fields, a known kind, well-formed anchors, and (unless it is
   `data`) a necessity witness or a `no_witness_reason`.
2. Every `sorry` in JoltConstraints/ and JoltBytecode/ (comments ignored) has a `sorry`
   entry naming its file and declaration, and every `sorry` entry still has its `sorry`.
3. Every field of `Rv64ProgramImage` (JoltConstraints/translation/program.lean) appears in
   some entry's `appears_in`.
4. The binder and field lists of JoltConstraints/Audit/Premises.lean, which the build
   checks against Lean, match the `appears_in` lists exactly.
5. The `witness` and `derived_by` names are exactly the `witness` and `derived` lines of
   `#audit_statements` in JoltConstraints/Audit/Statements.lean, and its `headline` lines are
   exactly the theorems Premises.lean lists. The build resolves each of those names exactly in
   Lean's environment, checks its axioms and fingerprints its statement, so a registered name
   that does not exist fails the build.
6. Every bug-report/*/README.md starts with a TOML header (between `+++` lines) with
   `status`, `reproduced_at`, `fixed_by` and `registry`, and its `registry` names entries.
7. `jolt_rev` equals JOLT_REV in .github/workflows/constraint-generation.yml.

With --jolt-dir, it also checks that each anchor's file exists at `jolt_rev` in that Jolt
checkout and mentions the anchor's name.

Exit status: 0 when every check passes, 1 otherwise.
"""

import argparse
import pathlib
import re
import subprocess
import sys
import tomllib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from lean_source import strip_comments  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
KINDS = {"premise", "scope", "correspondence", "field", "image-field", "derived", "sorry",
         "statement", "data"}
STATUSES = {"open", "fixed-upstream", "fixed-in-model", "not-a-bug", "unknown"}
ANCHOR = re.compile(r"^(?P<path>[\w./-]+) \((?P<name>[\w:]+)\)$")
REQUIRED = ("name", "lean", "kind", "anchors", "upstream", "bug_report")

errors = []


def error(message):
    errors.append(message)


DECL = re.compile(r"^(?:[\w@\[\]() ]*?)(?:theorem|lemma|def|abbrev|instance|example)\s+([^\s:({\[]*)",
                  re.M)


def lean_sorries():
    """Return {(file, declaration)} for every `sorry` outside comments."""
    found = set()
    for folder in ("JoltConstraints", "JoltBytecode"):
        for path in sorted((ROOT / folder).rglob("*.lean")):
            text = strip_comments(path.read_text())
            for match in re.finditer(r"\bsorry\b", text):
                decls = [d.group(1) for d in DECL.finditer(text, 0, match.start())]
                decl = decls[-1] if decls else "?"
                found.add((str(path.relative_to(ROOT)), decl))
    return found


def image_fields():
    """Return the field names of `Rv64ProgramImage`, read from its structure declaration."""
    text = (ROOT / "JoltConstraints/translation/program.lean").read_text()
    start = text.index("structure Rv64ProgramImage")
    body = text[start:].split("\n")[1:]
    fields = []
    for line in body:
        if line and not line.startswith(" "):
            break
        match = re.match(r"^  (\w+) :", line)
        if match:
            fields.append(match.group(1))
    return fields


def expected_lists():
    """Return {"<declaration> (<name>)"} from the lists in Audit/Premises.lean."""
    text = strip_comments_keep_strings((ROOT / "JoltConstraints/Audit/Premises.lean").read_text())
    items = set()
    for match in re.finditer(r"^#expect_(?:binders|fields) (\S+)((?:\s*\"[^\"]*\")*)", text, re.M):
        for line in re.findall(r"\"([^\"]*)\"", match.group(2)):
            items.add(f"{match.group(1)} ({line.split(' : ', 1)[0]})")
    return items


def strip_comments_keep_strings(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def audited_roots():
    """Return {label: [names]} from `#audit_statements` in Audit/Statements.lean."""
    text = strip_comments_keep_strings((ROOT / "JoltConstraints/Audit/Statements.lean").read_text())
    block = re.search(r"^#audit_statements\n(.*?)^expect ", text, re.M | re.S)
    if not block:
        error("JoltConstraints/Audit/Statements.lean has no `#audit_statements` block")
        return {}
    roots = {}
    for line in block.group(1).splitlines():
        if line.strip():
            label, name = line.split()
            roots.setdefault(label, []).append(name)
    return roots


def bug_report_headers(names):
    for readme in sorted((ROOT / "bug-report").glob("*/README.md")):
        where = readme.relative_to(ROOT)
        text = readme.read_text()
        if not text.startswith("+++\n"):
            error(f"{where}: no TOML header (+++ … +++) at the top")
            continue
        try:
            header = tomllib.loads(text[4:text.index("\n+++", 4)])
        except (ValueError, tomllib.TOMLDecodeError) as exc:
            error(f"{where}: cannot read the header: {exc}")
            continue
        for key in ("status", "reproduced_at", "fixed_by", "registry"):
            if key not in header:
                error(f"{where}: header has no `{key}`")
        if header.get("status") not in STATUSES:
            error(f"{where}: status {header.get('status')!r} is not one of {sorted(STATUSES)}")
        for name in header.get("registry", []):
            if name not in names:
                error(f"{where}: registry names {name!r}, which assumptions.toml does not have")
    for folder in sorted(p for p in (ROOT / "bug-report").iterdir() if p.is_dir()):
        if not (folder / "README.md").exists():
            error(f"{folder.relative_to(ROOT)}: no README.md with a header")


def check_anchors_in_jolt(entries, jolt_dir, rev):
    for entry in entries:
        for anchor in entry["anchors"]:
            match = ANCHOR.match(anchor)
            if not match:
                continue
            path, name = match.group("path"), match.group("name").split("::")[-1]
            shown = subprocess.run(["git", "-C", jolt_dir, "show", f"{rev}:{path}"],
                                   capture_output=True, text=True)
            if shown.returncode != 0:
                error(f"{entry['name']}: anchor file {path} does not exist at {rev[:9]}")
            elif not re.search(rf"\b{re.escape(name)}\b", shown.stdout):
                error(f"{entry['name']}: {path} at {rev[:9]} does not mention {name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--jolt-dir", help="a Jolt checkout to check the anchors against")
    args = parser.parse_args()

    registry = tomllib.loads((ROOT / "assumptions.toml").read_text())
    entries = registry["entry"]
    names = [entry.get("name") for entry in entries]
    for name in {n for n in names if names.count(n) > 1}:
        error(f"two entries are named {name!r}")

    # 1. The shape of each entry.
    for entry in entries:
        label = entry.get("name", "?")
        for key in REQUIRED:
            if key not in entry:
                error(f"{label}: missing `{key}`")
        if entry.get("kind") not in KINDS:
            error(f"{label}: kind {entry.get('kind')!r} is not one of {sorted(KINDS)}")
        for anchor in entry.get("anchors", []):
            if not ANCHOR.match(anchor):
                error(f"{label}: anchor {anchor!r} is not of the form 'path (name)'")
        has_reason = any(entry.get(key) for key in ("witness", "derived_by", "no_witness_reason"))
        if entry.get("kind") != "data" and not has_reason:
            error(f"{label}: needs a `witness`, a `derived_by` or a `no_witness_reason`")
        if entry.get("kind") not in ("data", "statement") and not entry.get("anchors"):
            error(f"{label}: needs at least one anchor")
        if entry.get("kind") == "sorry" and not entry.get("file"):
            error(f"{label}: a sorry entry needs `file`")
        if entry.get("bug_report") and not (ROOT / entry["bug_report"]).exists():
            error(f"{label}: bug_report {entry['bug_report']} does not exist")

    # 2. Sorries.
    registered = {(e["file"], e["lean"]) for e in entries if e.get("kind") == "sorry"}
    found = lean_sorries()
    for file, decl in sorted(found):
        if not any(file == f and (lean == decl or lean.endswith("." + decl))
                   for f, lean in registered):
            error(f"{file}: `sorry` in {decl} has no sorry entry")
    for file, lean in sorted(registered):
        if not any(file == f and (lean == decl or lean.endswith("." + decl)) for f, decl in found):
            error(f"{lean}: registered as a sorry, but {file} has no `sorry` in it; "
                  "update or remove the entry")

    # 3 and 4. Rv64ProgramImage fields, and the lists the build checks.
    appears = {}
    for entry in entries:
        for item in entry.get("appears_in", []):
            if item in appears:
                error(f"{item} appears in both {appears[item]} and {entry['name']}")
            appears[item] = entry["name"]
    for field in image_fields():
        if f"Rv64ProgramImage ({field})" not in appears:
            error(f"Rv64ProgramImage field {field} has no entry")
    expected = expected_lists()
    for item in sorted(expected - appears.keys()):
        error(f"{item} (JoltConstraints/Audit/Premises.lean) has no entry")
    for item in sorted(appears.keys() - expected):
        error(f"{item} ({appears[item]}) is not in JoltConstraints/Audit/Premises.lean")

    # 5. Witnesses, derivations and headline theorems are the ones the build audits.
    roots = audited_roots()
    for key, label in (("witness", "witness"), ("derived_by", "derived")):
        registered = {e[key] for e in entries if e.get(key)}
        audited = set(roots.get(label, []))
        for name in sorted(registered - audited):
            error(f"{key} {name} is not a `{label}` line of #audit_statements "
                  "(JoltConstraints/Audit/Statements.lean)")
        for name in sorted(audited - registered):
            error(f"`{label} {name}` in #audit_statements is not a `{key}` in assumptions.toml")
    headlines = {item.split(" (")[0] for item in expected
                 if not item.startswith(("Rv64ProgramImage ", "WholeRun.BlockConforms "))}
    if set(roots.get("headline", [])) != headlines:
        error(f"the `headline` lines of #audit_statements {sorted(roots.get('headline', []))} "
              f"differ from the theorems Premises.lean lists {sorted(headlines)}")
    for label in roots:
        if label not in ("headline", "witness", "derived"):
            error(f"#audit_statements has an unknown label {label!r}")

    # 6. Bug-report headers.
    bug_report_headers(set(names))

    # 7. One pin.
    workflow = (ROOT / ".github/workflows/constraint-generation.yml").read_text()
    pin = re.search(r"JOLT_REV:\s*([0-9a-f]{40})", workflow)
    if not pin or pin.group(1) != registry.get("jolt_rev"):
        error("jolt_rev in assumptions.toml differs from JOLT_REV in constraint-generation.yml")

    if args.jolt_dir:
        check_anchors_in_jolt(entries, args.jolt_dir, registry["jolt_rev"])

    for message in errors:
        print(f"check-assumptions: {message}", file=sys.stderr)
    if errors:
        print(f"check-assumptions: {len(errors)} problem(s); see assumptions.toml", file=sys.stderr)
        return 1
    print(f"check-assumptions: {len(entries)} entries, {len(found)} sorry, "
          f"{len(expected)} binders and fields, "
          f"{sum(len(v) for v in roots.values())} audited theorems: all registered")
    return 0


if __name__ == "__main__":
    sys.exit(main())
