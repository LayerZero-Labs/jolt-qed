"""Regression tests for scripts/check_comparator_imports.py.

Run from the repository root: python3 -m unittest discover -s scripts/tests
"""

from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent
_spec = importlib.util.spec_from_file_location(
    "check_comparator_imports", SCRIPTS / "check_comparator_imports.py")
imports = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(imports)

GATE = SCRIPTS.parent / "ci" / "comparator"
MODULES = ["JoltConstraints.WholeRun.Top", "JoltBytecode.Decode.Compressed",
           "JoltBytecode.Step.Instructions"]
CHALLENGE = (GATE / "Challenge.lean").read_text(encoding="utf-8")
SOLUTION = (GATE / "Solution.lean").read_text(encoding="utf-8")
FIRST = "import JoltConstraints.WholeRun.Top\n"


class ImportHeaderTest(unittest.TestCase):
    def test_gate_files_agree(self) -> None:
        self.assertEqual(imports.check(CHALLENGE, SOLUTION, MODULES), [])

    # Round-2 finding 9: a comment before an import hid it from the grep guard.
    def test_extra_import_after_a_comment_fails(self) -> None:
        bad = SOLUTION.replace(FIRST, "/- extra dependency -/ import Lean\n" + FIRST, 1)
        self.assertNotEqual(imports.check(CHALLENGE, bad, MODULES), [])

    def test_extra_import_on_the_same_line_fails(self) -> None:
        bad = SOLUTION.replace(FIRST, FIRST.rstrip("\n") + " import Lean\n", 1)
        self.assertNotEqual(imports.check(CHALLENGE, bad, MODULES), [])

    def test_modifier_fails(self) -> None:
        bad = SOLUTION.replace(FIRST, "public " + FIRST, 1)
        self.assertNotEqual(imports.check(CHALLENGE, bad, MODULES), [])

    # Round-2 finding 9: an `import` line inside a comment failed the grep guard.
    def test_import_inside_a_comment_is_ignored(self) -> None:
        ok = SOLUTION.replace("/-\n", "/-\nimport NotAnImport\n", 1)
        self.assertNotEqual(ok, SOLUTION)
        self.assertEqual(imports.check(CHALLENGE, ok, MODULES), [])
        ok = SOLUTION.replace(FIRST, FIRST + "-- import NotAnImport\n", 1)
        self.assertEqual(imports.check(CHALLENGE, ok, MODULES), [])

    def test_challenge_must_import_the_trusted_modules(self) -> None:
        self.assertNotEqual(imports.check(CHALLENGE, SOLUTION, MODULES[:2]), [])
        self.assertNotEqual(imports.check(CHALLENGE, SOLUTION, MODULES + ["Mathlib"]), [])

    def test_header_reading(self) -> None:
        self.assertEqual(imports.header("module\n-- c\npublic import A.B\nimport all C\ndef x := 1"),
                         ["module", "public import A.B", "import all C"])
        with self.assertRaises(ValueError):
            imports.header("import «A»\n")


if __name__ == "__main__":
    unittest.main()
