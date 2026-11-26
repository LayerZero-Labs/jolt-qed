"""Tests of scripts/jolt-drift-report.py.

Run with `python3 -m unittest discover -s scripts/tests` from the repository root. The test
builds a small Git repository in a temporary directory with a "pin" commit and a "main" commit,
and checks that the report lists a changed file that no anchor or citation names.
"""

import importlib.util
import pathlib
import subprocess
import tempfile
import unittest

SCRIPTS = pathlib.Path(__file__).resolve().parent.parent

_spec = importlib.util.spec_from_file_location("jolt_drift_report",
                                               SCRIPTS / "jolt-drift-report.py")
drift = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(drift)

PIN_FILES = {
    "tracer/src/instruction/addi.rs": "fn exec(x: u64, y: u64) -> u64 { x.wrapping_add(y) }\n",
    "tracer/src/instruction/jolt_success.rs": "pub fn exec() {}\n",
    "crates/jolt-verifier/src/stages/stage2/ram_output_check.rs": "fn ram_output_check_publics() {}\n",
    "tracer/tests/addi.rs": "#[test] fn t() {}\n",
    "tracer/README.md": "Tracer.\n",
    "jolt-eval/src/lib.rs": "pub fn f() {}\n",
    "Cargo.lock": "version = 4\n",
    "Cargo.toml": "[workspace]\n",
}
MAIN_CHANGES = {
    "tracer/src/instruction/addi.rs": "fn exec(x: u64, y: u64) -> u64 { x.wrapping_sub(y) }\n",
    "tracer/src/instruction/jolt_success.rs": "pub fn exec() { halt() }\n",
    "crates/jolt-verifier/src/stages/stage2/ram_output_check.rs": "fn ram_output_check_publics() { check() }\n",
    "crates/jolt-riscv/src/new_instruction.rs": "pub fn exec() {}\n",
    "tracer/tests/addi.rs": "#[test] fn t() { assert!(true) }\n",
    "tracer/README.md": "The tracer.\n",
    "jolt-eval/src/lib.rs": "pub fn f() { g() }\n",
    "Cargo.lock": "version = 4\n# changed\n",
}
UNCLASSIFIED = [
    "Cargo.lock",
    "crates/jolt-riscv/src/new_instruction.rs",
    "crates/jolt-verifier/src/stages/stage2/ram_output_check.rs",
    "tracer/src/instruction/addi.rs",
    "tracer/src/instruction/jolt_success.rs",
]
OTHER = ["jolt-eval/src/lib.rs", "tracer/README.md", "tracer/tests/addi.rs"]


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
                                        drift.watched_directories({}))
        self.assertEqual(groups["unclassified"], UNCLASSIFIED)
        self.assertEqual(groups["other"], OTHER)

    def test_cited_and_anchored_files_keep_their_group(self):
        path = "tracer/src/instruction/addi.rs"
        self.assertEqual(drift.classify_changes({path}, {path}, {}, drift.WATCHED)["anchored"],
                         [path])
        self.assertEqual(drift.classify_changes({path}, set(), {path: {"x.lean"}},
                                                drift.WATCHED)["cited"], [path])

    def test_report_lists_an_uncited_semantic_change(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = pathlib.Path(tmp)
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            pin = commit(repo, PIN_FILES, "pin")
            commit(repo, MAIN_CHANGES, "main")
            out = [""]
            drift.anchor_sections(out, str(repo), "HEAD", pin, [])
        report = "\n".join(out)
        section = report.split("## Unclassified changed files", 1)[1].split("\n## ", 1)[0]
        for path in UNCLASSIFIED:
            self.assertIn(f"`{path}`", section)
        for path in OTHER:
            self.assertNotIn(path, section)
        self.assertIn("`crates/jolt-riscv/src/new_instruction.rs` (added)", section)
        self.assertIn("8 Jolt files changed", section)
        self.assertIn("5 unclassified and 3 other", section)


class Evidence(unittest.TestCase):
    def test_cut_parts_are_kept_in_the_evidence_directory(self):
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
            self.assertEqual(result.stdout, report)


if __name__ == "__main__":
    unittest.main()
