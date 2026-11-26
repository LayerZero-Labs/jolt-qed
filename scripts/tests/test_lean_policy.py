"""Tests of scripts/check-lean-policy.py and scripts/lean_source.py.

Run with `python3 -m unittest discover -s scripts/tests` from the repository root; CI runs it in
the step that runs the policy check. Each fixture in scripts/tests/lean-policy/ except
`clean.lean` is Lean source the policy must reject. The fixtures live outside the scanned
libraries, so the policy check of the repository never sees them.
"""

import importlib.util
import pathlib
import unittest

SCRIPTS = pathlib.Path(__file__).resolve().parent.parent
FIXTURES = pathlib.Path(__file__).resolve().parent / "lean-policy"

_spec = importlib.util.spec_from_file_location("check_lean_policy",
                                               SCRIPTS / "check-lean-policy.py")
policy = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(policy)

# The fixtures about `maxRecDepth` are scanned as the generated file that the allowlist names,
# so that the allowlist entry `maxRecDepth 750` before `def is_CSR_accessible` applies.
ALLOWLISTED_FILE = "LeanRV64D/SysControl.lean"

# fixture: (the file it is scanned as, a problem the scan must report)
MUST_FAIL = {
    "sorry-ax.lean": (None, "`sorryAx`"),
    "guillemet-hides-admit.lean": (None, "`admit`"),
    "guillemet-hides-axiom.lean": (None, "`axiom bad`"),
    "guillemet-hides-max-heartbeats.lean": (None, "`maxHeartbeats`"),
    "guillemet-hides-string-start.lean": (None, "`admit`"),
    "char-literal-quote.lean": (None, "`admit`"),
    "nested-comment.lean": (None, "`admit`"),
    "interpolated-sorry.lean": (None, "`sorry`"),
    "interpolated-nested-string.lean": (None, "`admit`"),
    "ambiguous-string.lean": (None, "the policy scanner cannot tell how Lean reads it"),
    "two-options-one-line.lean": (ALLOWLISTED_FILE, "`maxRecDepth` option that"),
    "allowed-option-wrong-declaration.lean": (ALLOWLISTED_FILE, "`maxRecDepth` option that"),
}


def scan(name, where=None):
    allowed_axioms, allowed_options = policy.load_allowlist()
    where = where or f"scripts/tests/lean-policy/{name}"
    return policy.scan(where, (FIXTURES / name).read_text(), allowed_axioms, allowed_options,
                       set(), [])


class LeanPolicyFixtures(unittest.TestCase):
    def test_every_fixture_is_listed(self):
        names = {path.name for path in FIXTURES.glob("*.lean")}
        self.assertEqual(names, set(MUST_FAIL) | {"clean.lean"})

    def test_rejected(self):
        for name, (where, problem) in MUST_FAIL.items():
            with self.subTest(fixture=name):
                errors = scan(name, where)
                self.assertTrue(any(problem in error for error in errors),
                                f"{name}: expected a problem containing {problem!r}, got {errors}")

    def test_clean_passes(self):
        self.assertEqual(scan("clean.lean", ALLOWLISTED_FILE), [])

    def test_admit_line_number(self):
        # The `«…»` identifier on line 1 must not shift or hide the `admit` on line 2.
        errors = scan("guillemet-hides-admit.lean")
        self.assertIn("scripts/tests/lean-policy/guillemet-hides-admit.lean:2: `admit`", errors)


if __name__ == "__main__":
    unittest.main()
