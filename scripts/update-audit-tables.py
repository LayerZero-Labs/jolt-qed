#!/usr/bin/env python3
"""Rewrite the expected data of the audit modules from the build.

Usage: scripts/update-audit-tables.py

Run it after a change to a headline theorem, to a definition its statement depends on, or to
a necessity witness or derived fact, once you have read the build's error and decided the
change is intended. It builds JoltConstraints.Audit.Premises and
JoltConstraints.Audit.Statements with JOLT_QED_AUDIT_OUT set, so that the audit commands write
their actual data (see JoltConstraints/Audit/Commands.lean), and then:

- replaces each `#expect_binders` and `#expect_fields` list in
  JoltConstraints/Audit/Premises.lean that changed;
- replaces the table after `expect` in JoltConstraints/Audit/Statements.lean;
- builds again and prints `git diff --stat` of the two files.

The table is data to review: `git diff` shows each changed statement in full and one line per
changed definition. The registry is not updated: when a binder changed, edit `appears_in` in
assumptions.toml and run scripts/check-assumptions.py.

Set LAKE to the command that runs Lake (default `lake`); for example
LAKE="$HOME/claude-work/track-t-build.sh lake".

Exit status: 0 when the final build of both modules passes, 1 otherwise.
"""

import os
import pathlib
import re
import shlex
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
PREMISES = ROOT / "JoltConstraints/Audit/Premises.lean"
STATEMENTS = ROOT / "JoltConstraints/Audit/Statements.lean"
TARGETS = ["JoltConstraints.Audit.Premises", "JoltConstraints.Audit.Statements"]
TABLE = re.compile(r'(\nexpect r#")(.*?)("#)', re.S)


def build(out_dir):
    env = dict(os.environ)
    if out_dir:
        env["JOLT_QED_AUDIT_OUT"] = str(out_dir)
    lake = shlex.split(os.environ.get("LAKE", "lake"))
    result = subprocess.run([*lake, "build", *TARGETS], cwd=ROOT, env=env, text=True,
                            capture_output=True)
    return result.returncode, result.stdout + result.stderr


def replace_list(text, command, name, lines):
    """Replace the string lines after `#<command> <name>` with `lines`."""
    pattern = re.compile(rf"(^#{command} {re.escape(name)}\n)((?:  \"[^\n]*\n)*)", re.M)
    if not pattern.search(text):
        sys.exit(f"update-audit-tables: no `#{command} {name}` in {PREMISES.relative_to(ROOT)}")
    return pattern.sub(lambda m: m.group(1) + lines.rstrip("\n") + "\n", text, count=1)


def apply(out_dir):
    """Paste every file the build wrote into the sources. Return the files changed."""
    changed = []
    premises = PREMISES.read_text()
    for path in sorted(out_dir.glob("expect_*-*.txt")):
        command, name = path.stem.split("-", 1)
        premises = replace_list(premises, command, name, path.read_text())
    if premises != PREMISES.read_text():
        PREMISES.write_text(premises)
        changed.append(PREMISES)
    table = out_dir / "audit_statements.txt"
    if table.exists():
        statements = STATEMENTS.read_text()
        if '"#' in table.read_text():
            sys.exit("update-audit-tables: the table contains `\"#`; use a longer raw string")
        if not TABLE.search(statements):
            sys.exit(f"update-audit-tables: no `expect r#\"…\"#` in {STATEMENTS.relative_to(ROOT)}")
        updated = TABLE.sub(lambda m: m.group(1) + "\n" + table.read_text() + m.group(3),
                            statements, count=1)
        if updated != statements:
            STATEMENTS.write_text(updated)
            changed.append(STATEMENTS)
    return changed


def main():
    # Premises.lean and Statements.lean can both be out of date; Statements.lean builds only
    # after Premises.lean passes, so this takes up to three rounds.
    for _ in range(3):
        with tempfile.TemporaryDirectory() as out:
            status, log = build(pathlib.Path(out))
            changed = apply(pathlib.Path(out))
        if status == 0:
            break
        if not changed:
            print(log[-6000:], file=sys.stderr)
            print("update-audit-tables: the build fails for a reason other than the expected "
                  "data (see above)", file=sys.stderr)
            return 1
        for path in changed:
            print(f"update-audit-tables: rewrote {path.relative_to(ROOT)}")
    status, log = build(None)
    if status != 0:
        print(log[-6000:], file=sys.stderr)
        print("update-audit-tables: the build still fails", file=sys.stderr)
        return 1
    stat = subprocess.run(["git", "diff", "--stat", "--", str(PREMISES), str(STATEMENTS)],
                          cwd=ROOT, text=True, capture_output=True).stdout
    print(stat or "update-audit-tables: nothing changed")
    print("update-audit-tables: review `git diff` of the two files; if a binder changed, update "
          "`appears_in` in assumptions.toml and run scripts/check-assumptions.py")
    return 0


if __name__ == "__main__":
    sys.exit(main())
