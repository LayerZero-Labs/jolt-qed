"""Tests of scripts/jolt-drift-report.py.

Run with `python3 -m unittest discover -s scripts/tests` from the repository root. The test
builds a small Git repository in a temporary directory with a "pin" commit and a "main" commit,
and checks that the report lists a changed file that no anchor or citation names, including
files in crates that only the workspace manifest names and in a crate that main adds.
"""

import contextlib
import importlib.util
import io
import pathlib
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = pathlib.Path(__file__).resolve().parent.parent

_spec = importlib.util.spec_from_file_location("jolt_drift_report",
                                               SCRIPTS / "jolt-drift-report.py")
drift = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(drift)

PIN_MEMBERS = ["tracer", "common", "crates/jolt-riscv", "crates/jolt-verifier", "crates/jolt-utils",
               "crates/jolt-lean-gen", "examples/demo", "jolt-eval"]
MAIN_MEMBERS = PIN_MEMBERS + ["crates/jolt-new"]


def manifest(members):
    return "[workspace]\nmembers = [" + ", ".join(f'"{m}"' for m in members) + "]\n"


PIN_FILES = {
    "tracer/src/instruction/addi.rs": "fn exec(x: u64, y: u64) -> u64 { x.wrapping_add(y) }\n",
    "tracer/src/instruction/jolt_success.rs": "pub fn exec() {}\n",
    "crates/jolt-verifier/src/stages/stage2/ram_output_check.rs": "fn ram_output_check_publics() {}\n",
    # Not cited, but `CommitmentMatrixShape::advice_from_max_bytes` uses it.
    "crates/jolt-utils/src/math.rs": "pub fn log2_power_of_two(n: usize) -> usize { 0 }\n",
    # The expansion generator.
    "crates/jolt-lean-gen/src/main.rs": "fn main() {}\n",
    "tracer/tests/addi.rs": "#[test] fn t() {}\n",
    "tracer/README.md": "Tracer.\n",
    "jolt-eval/src/lib.rs": "pub fn f() {}\n",
    "examples/demo/src/main.rs": "fn main() {}\n",
    "Cargo.lock": "version = 4\n",
    "Cargo.toml": manifest(PIN_MEMBERS),
}
MAIN_CHANGES = {
    "tracer/src/instruction/addi.rs": "fn exec(x: u64, y: u64) -> u64 { x.wrapping_sub(y) }\n",
    "tracer/src/instruction/jolt_success.rs": "pub fn exec() { halt() }\n",
    "crates/jolt-verifier/src/stages/stage2/ram_output_check.rs": "fn ram_output_check_publics() { check() }\n",
    "crates/jolt-utils/src/math.rs": "pub fn log2_power_of_two(n: usize) -> usize { 1 }\n",
    "crates/jolt-lean-gen/src/main.rs": "fn main() { emit() }\n",
    "crates/jolt-riscv/src/new_instruction.rs": "pub fn exec() {}\n",
    "crates/jolt-new/Cargo.toml": "[package]\nname = \"jolt-new\"\n",
    "crates/jolt-new/src/lib.rs": "pub fn g() {}\n",
    "tracer/tests/addi.rs": "#[test] fn t() { assert!(true) }\n",
    "tracer/README.md": "The tracer.\n",
    "jolt-eval/src/lib.rs": "pub fn f() { g() }\n",
    "examples/demo/src/main.rs": "fn main() { run() }\n",
    "Cargo.lock": "version = 4\n# changed\n",
    "Cargo.toml": manifest(MAIN_MEMBERS),
}
UNCLASSIFIED = [
    "Cargo.lock",
    "Cargo.toml",
    "crates/jolt-lean-gen/src/main.rs",
    "crates/jolt-new/Cargo.toml",
    "crates/jolt-new/src/lib.rs",
    "crates/jolt-riscv/src/new_instruction.rs",
    "crates/jolt-utils/src/math.rs",
    "crates/jolt-verifier/src/stages/stage2/ram_output_check.rs",
    "tracer/src/instruction/addi.rs",
    "tracer/src/instruction/jolt_success.rs",
]
OTHER = ["examples/demo/src/main.rs", "jolt-eval/src/lib.rs", "tracer/README.md",
         "tracer/tests/addi.rs"]


def make_repo(tmp, pin_files=PIN_FILES, main_changes=MAIN_CHANGES):
    """A Git repository in `tmp` with a pin commit and a main commit. Return the pin's SHA."""
    repo = pathlib.Path(tmp)
    subprocess.run(["git", "init", "-q", str(repo)], check=True)
    pin = commit(repo, pin_files, "pin")
    commit(repo, main_changes, "main")
    return pin


def commit(repo, files, message):
    for path, text in files.items():
        target = repo / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
    run = lambda *args: subprocess.run(["git", "-C", str(repo), *args], check=True,
                                       capture_output=True, text=True).stdout
    run("add", "-A")
    run("-c", "user.name=test", "-c", "user.email=test@example.com", "commit", "-q",
        "-m", message)
    return run("rev-parse", "HEAD").strip()


class UnclassifiedFiles(unittest.TestCase):
    def test_classify(self):
        groups = drift.classify_changes(set(UNCLASSIFIED) | set(OTHER), set(), {},
                                        drift.watched_directories({}), MAIN_MEMBERS)
        self.assertEqual(groups["unclassified"], UNCLASSIFIED)
        self.assertEqual(groups["other"], OTHER)

    def test_uncited_workspace_crates_are_watched(self):
        # Neither crate is cited or on a hand list; the workspace alone makes them watched.
        for path in ("crates/jolt-utils/src/math.rs", "crates/jolt-lean-gen/src/main.rs"):
            with self.subTest(path=path):
                groups = drift.classify_changes({path}, set(), {}, drift.watched_directories({}),
                                                PIN_MEMBERS)
                self.assertEqual(groups["unclassified"], [path])

    def test_crate_of(self):
        members = ["crates/*", "jolt-sdk", "jolt-sdk/macros", "."]
        self.assertEqual(drift.crate_of("crates/jolt-utils/src/math.rs", members),
                         "crates/jolt-utils")
        self.assertEqual(drift.crate_of("jolt-sdk/macros/src/lib.rs", members), "jolt-sdk/macros")
        self.assertEqual(drift.crate_of("jolt-sdk/src/lib.rs", members), "jolt-sdk")
        self.assertEqual(drift.crate_of("src/main.rs", members), ".")
        self.assertIsNone(drift.crate_of("third-party/x/src/lib.rs", members))

    def test_cited_and_anchored_files_keep_their_group(self):
        path = "tracer/src/instruction/addi.rs"
        self.assertEqual(drift.classify_changes({path}, {path}, {}, drift.WATCHED)["anchored"],
                         [path])
        self.assertEqual(drift.classify_changes({path}, set(), {path: {"x.lean"}},
                                                drift.WATCHED)["cited"], [path])

    def test_report_lists_an_uncited_semantic_change(self):
        with tempfile.TemporaryDirectory() as tmp:
            pin = make_repo(tmp)
            out = [""]
            drift.anchor_sections(out, drift.compare(tmp, "HEAD", pin, []))
        report = "\n".join(out)
        section = report.split("## Unclassified changed files", 1)[1].split("\n## ", 1)[0]
        for path in UNCLASSIFIED:
            self.assertIn(f"`{path}`", section)
        for path in OTHER:
            self.assertNotIn(f"`{path}`", section)
        self.assertIn("`crates/jolt-riscv/src/new_instruction.rs` (added)", section)
        self.assertIn("`crates/jolt-utils/src/math.rs` (modified)", section)
        self.assertIn("crate `crates/jolt-new/` (added to the workspace since the pin; its files "
                      "are watched)", section)
        self.assertIn("14 Jolt files changed", section)
        self.assertIn("10 unclassified and 4 other", section)


def run_main(argv, root, cited):
    """Run the script's `main` in this process with the registry in `root` and the citations
    `cited`, and return its exit status and standard output."""
    saved = drift.ROOT, drift.resolved_citations, sys.argv
    drift.ROOT = root
    drift.resolved_citations = lambda jolt_dir, rev: (cited, {})
    sys.argv = ["jolt-drift-report.py", *argv]
    try:
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            status = drift.main()
        return status, stdout.getvalue()
    finally:
        drift.ROOT, drift.resolved_citations, sys.argv = saved


class Evidence(unittest.TestCase):
    def test_long_lists_are_full_in_the_artifact_and_cut_in_the_issue(self):
        count = drift.MAX_LIST + 5
        cited_paths = [f"tracer/src/cited/f{i:03d}.rs" for i in range(count)]
        uncited_paths = [f"tracer/src/uncited/g{i:03d}.rs" for i in range(count)]
        cited = {path: {f"JoltBytecode/Cites{i:03d}.lean"} for i, path in enumerate(cited_paths)}
        pin_files = {path: "fn f() {}\n" for path in cited_paths + uncited_paths}
        pin_files["Cargo.toml"] = manifest(["tracer"])
        main_changes = {path: "fn f() { g() }\n" for path in cited_paths + uncited_paths}
        with tempfile.TemporaryDirectory() as tmp:
            tmp = pathlib.Path(tmp)
            pin = make_repo(tmp / "jolt", pin_files, main_changes)
            (tmp / "assumptions.toml").write_text(f'jolt_rev = "{pin}"\nentry = []\n')
            status, body = run_main(["--jolt-dir", str(tmp / "jolt"), "--evidence-dir",
                                     str(tmp / "evidence")], tmp, cited)
            self.assertEqual(status, 0, body)
            report = (tmp / "evidence" / "report.md").read_text()
            table = (tmp / "evidence" / "changed-files.tsv").read_text()
        last_cited, last_uncited = cited_paths[-1], uncited_paths[-1]
        # The issue body shows MAX_LIST items of each list and says where the rest is.
        self.assertNotIn(f"`{last_cited}`", body)
        self.assertNotIn(f"`{last_uncited}`", body)
        self.assertEqual(body.count("… and 5 more"), 2)
        # The evidence report shows every item.
        for path in cited_paths + uncited_paths:
            self.assertIn(f"`{path}`", report)
        self.assertIn(f"`{last_cited}`: cited by `JoltBytecode/Cites{count - 1:03d}.lean`", report)
        self.assertNotIn("more (", report)
        # The table maps each cited file to the Lean files that cite it.
        self.assertIn(f"cited\t{last_cited}\tJoltBytecode/Cites{count - 1:03d}.lean\t\n", table)
        self.assertIn(f"unclassified\t{last_uncited}\t\t\n", table)

    def test_long_diff_is_full_in_the_artifact_and_cut_in_the_issue(self):
        line = "+" + "x" * 99 + "\n"
        diff = "".join(f"{i:06d}{line}" for i in range(400))  # longer than MAX_DIFF
        self.assertGreater(len(diff), drift.MAX_DIFF)
        with tempfile.TemporaryDirectory() as tmp:
            tmp = pathlib.Path(tmp)
            (tmp / "generated.diff").write_text(diff)
            (tmp / "generated.stat").write_text(" R1CS.lean | 400 +\n")
            result = subprocess.run(
                ["python3", str(SCRIPTS / "jolt-drift-report.py"), "--generation-status", "0",
                 "--generated", "yes", "--generated-diff", str(tmp / "generated.diff"),
                 "--generated-stat", str(tmp / "generated.stat"), "--evidence-dir",
                 str(tmp / "evidence"), "--run-url", "https://example.invalid/run"],
                capture_output=True, text=True)
            # No --jolt-dir: the report is written and says that monitoring failed.
            self.assertEqual(result.returncode, 3, result.stderr)
            self.assertIn("`drift-evidence` artifact](https://example.invalid/run#artifacts)",
                          result.stdout)
            self.assertIn("full diff in `generated.diff`", result.stdout)
            self.assertNotIn("000399", result.stdout)
            evidence = tmp / "evidence"
            self.assertEqual((evidence / "generated.diff").read_text(), diff)
            report = (evidence / "report.md").read_text()
        self.assertIn("**Monitoring failed in this run.**", report)
        self.assertIn(diff, report)
        self.assertNotIn("(cut;", report)


if __name__ == "__main__":
    unittest.main()
